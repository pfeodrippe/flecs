# Flecs ECS Concurrency Bug Findings

Bugs found via TLA+ model checking against Flecs v4.1.4.

All specifications are in `specifications/bug-hunt/`. Each models a specific
concurrency scenario extracted from the Flecs C source, with non-atomic
read-modify-write operations split into separate steps to expose interleavings.

---

## Summary

| # | Bug | Severity | Spec | Source |
|---|-----|----------|------|--------|
| 1 | Duplicate entity allocation (entity index race) | **Critical** | `EntityIndexRace.tla` | `entity_index.c:242-265` |
| 2 | Silent data loss during cross-stage merge | **High** | `MultiStageMerge.tla` | `stage.c` / `commands.c` |
| 3 | Override removal data race (concurrent write) | **High** | `OverrideWriteRace.tla` | `commands.c:276-312` |

---

## Bug 1: Duplicate Entity Allocation (CRITICAL)

**Spec:** `EntityIndexRace.tla`
**Invariant violated:** `NoDuplicateEntityAllocation`
**TLC result:** 666 states explored, violation at depth 14, <1s

### Description

Two threads calling `flecs_entity_index_new_id()` concurrently can receive the
**same entity ID**. The entity index has zero synchronization — `alive_count`
and `max_id` are plain `int32_t`/`uint64_t` with no atomics or locks.

### Root cause

`flecs_entity_index_new_id` in `entity_index.c:239-270` has two non-atomic
read-modify-write sequences:

**Recycling path** (line 242-244):
```c
if (index->alive_count != ecs_vec_count(&index->dense)) {
    return ecs_vec_get_t(&index->dense, uint64_t, index->alive_count ++)[0];
}
```

**Creation path** (line 248, 265):
```c
uint32_t id = (uint32_t)++ index->max_id;
// ...
r->dense = index->alive_count ++;
```

Both `alive_count++` and `++max_id` are non-atomic. When two threads execute
concurrently:

1. Thread A reads `alive_count` (say, value 2)
2. Thread B reads `alive_count` (still 2 — A hasn't written yet)
3. Thread A returns `dense[2]` and writes `alive_count = 3`
4. Thread B returns `dense[2]` — **same entity** — and writes `alive_count = 3`

Both threads now own the same entity ID. The second `alive_count = 3` write
is a lost update (should have been 4).

### Stale comment

`entity.c:147-150` contains:
```c
/* ... thread safe (uses atomic inc when in threading mode) */
```

This comment is **false** in the current codebase. There are no atomics anywhere
in `entity_index.c`. The only guard is a debug-mode assert at `entity.c:153`:
```c
ecs_assert(!(unsafe_world->flags & EcsWorldMultiThreaded), ...);
```

This assert is compiled out in release builds, leaving zero protection.

### Race scenario (from TLC counterexample)

```
State 1:  Both threads idle, entity index empty
State 2:  Thread t1 starts new_id, reads alive_count = 0
State 3:  Thread t2 starts new_id, reads alive_count = 0
State 4:  t1 sees no recyclable slots, reads max_id = 0
State 5:  t2 sees no recyclable slots, reads max_id = 0
State 6:  t1 writes max_id = 1, gets entity ID 1
State 7:  t2 writes max_id = 1, gets entity ID 1 (LOST UPDATE)
...
State 14: Both threads finish — allocated = {(t1, 1), (t2, 1)} — VIOLATION
```

### Impact

- Two threads own the same entity — components written by one are silently
  overwritten by the other
- Dense array corruption: two records point to the same dense index
- `alive_count` lost update means the partition boundary is wrong, leading to
  incorrect recycling of live entities in subsequent operations

### Recommendation

Either:
- Make entity creation truly thread-safe with atomics (as the stale comment
  claims), or
- Document that `ecs_new()` must never be called from worker threads and
  enforce this in release builds (not just debug asserts), or
- Route all entity creation through the deferred command queue when in
  multi-threaded mode

---

## Bug 2: Silent Data Loss During Cross-Stage Merge (HIGH)

**Spec:** `MultiStageMerge.tla`
**Invariant violated:** `NoSilentDataLoss` (safety), liveness violation (temporal)
**TLC result:** Safety: 16,883 states, violation at depth 10, <1s. Liveness: 269,873 states, 7s.

### Description

When multiple worker stages queue commands during readonly mode and merge
sequentially, a **Delete** command from an earlier stage causes all subsequent
stages' commands for that entity to be **silently discarded** — no error, no
warning, no callback.

### Root cause

The merge loop in `stage.c` processes stages in order (stage 0, then stage 1,
etc.). Each command checks `alive[entity]` before applying. If stage 0 deletes
entity E, then when stage 1's commands for entity E are processed, the entity
is already dead and the commands are dropped:

```
// Pseudocode from merge logic:
if (!alive[cmd.entity]) {
    // silently skip — no error, no log
    continue;
}
```

This is by design — Flecs treats this as "the entity is gone, so the command
is moot." But from the perspective of the worker thread that enqueued the
command, its work is silently lost with no indication.

### Race scenario (from TLC counterexample)

```
State 1:  Idle, entities e1 and e2 alive
State 2:  Begin readonly
State 3:  Stage s0 enqueues Delete(e1)
State 4:  Stage s1 enqueues Add(e1, c1)    ← s1 sees e1 alive
State 5:  End readonly, begin merge
State 6:  Merge stage s0: apply Delete(e1) → e1 is now dead
State 7:  Merge stage s1: Add(e1, c1) → e1 is dead → DROPPED
          (dropped counter = 1 → NoSilentDataLoss VIOLATED)
```

### Liveness violation

The temporal property `InfiniteProgress` (the system always eventually reaches
idle with all queues cleared) can also be violated. TLC found a lasso-shaped
counterexample where the system loops through readonly/merge cycles but queues
are never fully drained due to re-enqueueing.

### Impact

- User work is silently lost — a system that computed and enqueued a result
  gets no feedback that the result was discarded
- Hard to debug — no log message, no error code, no callback
- Non-deterministic from the user's perspective — whether data is lost depends
  on which stage executes the delete and the merge order

### Recommendation

- Add an optional diagnostic callback or event when commands are dropped
  during merge due to dead entities
- Consider logging dropped commands at a debug/trace level
- Document this behavior explicitly in the multi-threading guide

---

## Bug 3: Override Removal Data Race (HIGH)

**Spec:** `OverrideWriteRace.tla`
**Invariants violated:** `NoSimultaneousWrite` (depth 3), `NoDataRace` (depth 5)
**TLC result:** 54 states, <1s

### Description

When removing an overridden component during readonly/deferred mode,
`flecs_defer_remove` **immediately writes** the base component value into the
entity's table column memory — bypassing the command queue entirely. This is a
direct write to shared world storage from a worker thread, with no lock.

### Root cause

`commands.c:276-312`:
```c
/* If an override is removed, restore to the component to the value of
 * the overridden component. */
void *dst = ECS_OFFSET(
    table->data.columns[tr->column].data,
    ti->size * ECS_RECORD_TO_ROW(r->row));
const void *src = ecs_ref_get_id(world, &o->refs[tr->column], id);
ecs_copy_t copy = ti->hooks.copy;
if (copy) {
    copy(dst, src, 1, ti);       // ← DIRECT WRITE, no lock
} else {
    ecs_os_memcpy(dst, src, ti->size);  // ← DIRECT WRITE
}
```

This code runs during deferred mode (inside a worker thread's system). If
another thread is iterating the same table column (reading the component), this
is a **data race** — undefined behavior in C.

### Additional issue: non-atomic table lock

The table "lock" mechanism (`table.c:2695-2717`) uses plain `++`/`--`:
```c
void ecs_table_lock(...) {
    table->_->lock ++;   // non-atomic increment
}
void ecs_table_unlock(...) {
    table->_->lock --;   // non-atomic decrement
}
```

Meanwhile, `entity.c` uses `ecs_os_ainc`/`ecs_os_adec` (atomics) on the same
field in some paths. This inconsistency means the lock counter itself can be
corrupted under concurrent access.

### Race scenario (from TLC counterexample)

**Simultaneous write (depth 3):**
```
State 1:  Both threads idle, slot = OverrideValue
State 2:  Thread t1 starts override removal, enters write_begin
State 3:  Thread t2 starts override removal, enters write_begin
          → Two threads both writing to same slot — VIOLATION
```

**Read-during-write (depth 5):**
```
State 1:  Both threads idle, slot = OverrideValue
State 2:  Thread t1 starts override removal, enters write_begin
State 3:  Thread t1 marks slot as being written (slotWriting = TRUE)
State 4:  Thread t2 starts read, enters reading state
State 5:  Thread t2 reads slot while t1 is mid-write
          → readsDuringWrite = TRUE — DATA RACE
```

### Pipeline scheduler mitigation

The Flecs pipeline scheduler prevents systems that touch the same archetype
from running in parallel under normal circumstances. However, this protection
can be bypassed if:

- Two systems in different pipeline stages both remove the same overridden
  component from the same entity
- User code manually schedules systems that violate the pipeline's assumptions
- Custom pipeline implementations don't enforce the archetype exclusion

### Impact

- Undefined behavior in C (concurrent read + write to same memory)
- Torn reads: a reader may see partially-written component data
- Data corruption: two simultaneous override removals can corrupt the
  component value

### Recommendation

- Defer the override value restoration to the merge phase instead of writing
  immediately during readonly mode
- Or, add a per-column lock for the override write path
- Document that custom pipeline implementations must enforce the archetype
  exclusion guarantee to avoid this race

---

## Methodology

All bugs were found using TLA+ model checking with the TLC model checker.

**Approach:** We extracted the concurrency-relevant portions of Flecs' C code
into TLA+ specifications, modeling non-atomic read-modify-write operations as
separate Read and Write steps with arbitrary interleaving between threads. This
is the standard technique for finding concurrency bugs via formal methods.

**Model size:** All specifications use small constants (2 threads, 2-3 entities,
1 component) with state constraints to keep TLC runs under 10 seconds. The bugs
are found at shallow depths (3-14 steps), confirming they are easily reachable
race conditions, not exotic corner cases.

**Tool:** TLC model checker via `clojure -Sdeps '{:deps {pfeodrippe/recife
{:mvn/version "0.22.0"}}}' -M -e '(tlc2.TLC/main ...)'`

**Files:**
- `EntityIndexRace.tla` / `.cfg` — Bug 1
- `MultiStageMerge.tla` / `.cfg` — Bug 2
- `OverrideWriteRace.tla` / `.cfg` — Bug 3

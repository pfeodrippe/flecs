# Flecs ECS Concurrency Bug Findings

Bugs found via TLA+ model checking against the Flecs source (v4).

All specifications are in `specifications/bug-hunt/`. Each models a specific
concurrency scenario extracted from the Flecs C source, with non-atomic
read-modify-write operations split into separate steps to expose interleavings.

---

## Summary

| # | Bug | Severity | Impact | Spec | Source |
|---|-----|----------|--------|------|--------|
| 1 | `ecs_ensure` direct-write race (missing `stage_count` guard) | **High** | Data corruption | `EnsureDirectWrite.tla` | `commands.c:399-459` |
| 2 | `system_data->time_spent +=` lost update | **Medium** | Incorrect profiling | `TimeSpentRace.tla` | `system.c:146` |
| 3 | `dirty_state[column+1] ++` lost update | **High** | Missed change detection | `DirtyStateRace.tla` | `change_detection.c:487,526` |
| 4 | `query->eval_count` inconsistent atomicity | **Low** | Incorrect statistics (UB) | `EvalCountRace.tla` | `eval_iter.c:551`, `api.c:492,522` |

### Previously reported (Phase 2 — invalidated)

The following specs from Phase 2 model scenarios that are either documented
behavior, user errors, or prevented by the pipeline scheduler under normal use.
They are kept for reference but are **not real bugs**:

| Spec | Why invalidated |
|------|-----------------|
| `EntityIndexRace.tla` | `ecs_new` from worker threads is forbidden by docs |
| `MultiStageMerge.tla` | Cross-stage delete/add discard is documented behavior |
| `OverrideWriteRace.tla` | Protected by pipeline scheduler sync points |

---

## Bug 1: `ecs_ensure` Direct-Write Race (HIGH)

**Spec:** `EnsureDirectWrite.tla`
**Invariants violated:** `NoDataRace` (depth 3), `NoConcurrentWrite` (depth 5)
**TLC result:** 47 states, <1s

### Description

When a multi-threaded system calls `ecs_ensure()` on an entity that already has
the requested component, `flecs_defer_ensure` returns a **raw pointer to the
live component storage** in the shared world. If two worker threads call
`ecs_ensure` on the same entity (e.g., a singleton), they both get the same raw
pointer and write to it concurrently — a data race.

### Root cause

`flecs_defer_ensure` (`commands.c:399-459`) calls `flecs_defer_get_existing`
which returns a pointer into the live component table via `flecs_get_mut`. When
the entity already has the component (`ptr.ptr != NULL`), the pointer is returned
directly (line 452-454):

```c
} else {
    cmd->kind = EcsCmdAdd;
}
return ptr.ptr;  // raw pointer to shared world data!
```

**Compare with `flecs_defer_set`** (`commands.c:461-546`) which has the guard
at lines 481-486:

```c
if (world->stage_count != 1) {
    /* If world has multiple stages we need to insert a set command
     * with temporary storage, as the value could be lost otherwise
     * by a command in another stage. */
    ptr.ptr = NULL;
}
```

This guard forces `flecs_defer_set` to allocate per-stage temporary storage
when multi-threaded, preventing the race. **This guard is missing from
`flecs_defer_ensure`, `flecs_defer_cpp_set`, and `flecs_defer_cpp_assign`.**

### Affected functions (all missing the guard)

| Function | File:Line | Description |
|----------|-----------|-------------|
| `flecs_defer_ensure` | `commands.c:399` | C API `ecs_ensure()` path |
| `flecs_defer_cpp_set` | `commands.c:549` | C++ `entity::set()` path |
| `flecs_defer_cpp_assign` | `commands.c:623` | C++ `entity::insert()` path |

### API documentation confirms the behavior

`flecs.h:3363-3366`:
> If ensure is called when the world is in deferred/readonly mode, the function
> will: return a pointer to the existing component if it exists

### TLC counterexample (NoDataRace violation)

```
State 1: Both workers idle, apiPath = "ensure"
State 2: Worker 1 calls ecs_ensure → workerPtr[1] = "raw"
State 3: Worker 2 calls ecs_ensure → workerPtr[2] = "raw"
         ⇒ Both hold raw pointers to same live component — VIOLATION
```

### Impact

- **Data race**: two workers write to the same memory location concurrently
- **Undefined behavior** under C11 memory model
- **Silent data corruption**: last writer wins, no error or warning
- Affects any multi-threaded system that calls `ecs_ensure` on a non-iterated
  entity (e.g., a singleton config entity)

### Fix

Add the same `stage_count != 1` guard to `flecs_defer_ensure`,
`flecs_defer_cpp_set`, and `flecs_defer_cpp_assign`:

```c
if (world->stage_count != 1) {
    ptr.ptr = NULL;
}
```

This forces per-stage temporary storage allocation, matching `flecs_defer_set`.

---

## Bug 2: `system_data->time_spent` Lost Update (MEDIUM)

**Spec:** `TimeSpentRace.tla`
**Invariant violated:** `NoLostUpdate`
**TLC result:** 63 states, <1s

### Description

When `EcsWorldMeasureSystemTime` is enabled and a system is marked
`multi_threaded`, all worker threads execute `system_data->time_spent +=`
on the **same shared float** without synchronization.

### Root cause

`system.c:146`:
```c
if (measure_time) {
    system_data->time_spent += (ecs_ftime_t)ecs_time_measure(&time_start);
}
```

`system_data` is the same `ecs_system_t` struct for all workers running a
multi-threaded system. The `+=` is a non-atomic read-modify-write on a float.

**Not covered by `FLECS_ACCURATE_COUNTERS`**: that flag only makes integer
counters (via `ecs_os_linc`) atomic. There is no atomic float add facility
in Flecs.

### TLC counterexample

```
State 1:  timeSpent = 0, Workers = {1, 2}
State 3:  Worker 1 reads timeSpent = 0
State 5:  Worker 2 reads timeSpent = 0  (stale!)
State 6:  Worker 1 writes 0 + 1 = 1
State 8:  Worker 2 writes 0 + 2 = 2     (overwrites Worker 1's contribution)
State 10: DONE: timeSpent = 2, expected 3 — Worker 1's time LOST
```

### Impact

- Inaccurate system timing statistics
- `ecs_system_t::time_spent` reports less time than actually spent
- Severity increases with more worker threads (more lost updates)

### Fix

Accumulate time per-stage during the parallel phase, then sum into
`system_data->time_spent` during the single-threaded merge/sync point.

---

## Bug 3: `dirty_state` Change Detection Lost Update (HIGH)

**Spec:** `DirtyStateRace.tla`
**Invariant violated:** `NoLostDirtyUpdate`, `ChangeDetectionIntegrity`
**TLC result:** 866 states (3 workers), <1s

### Description

The change detection system tracks which table columns have been modified via
`dirty_state[column + 1] ++`. When a multi-threaded system has a **fixed-source
field** (e.g., a singleton), ALL workers increment the same `dirty_state` entry
when they finish iteration. This is a non-atomic `++` on shared state.

### Root cause

`change_detection.c:526` (in `flecs_query_mark_fixed_fields_dirty`):
```c
dirty_state[column + 1] ++;
```

Called from `eval_iter.c:258` when `ecs_query_next` returns false (iteration
complete). For fixed-source fields, all workers touch the same table's
dirty_state because the fixed source is the same entity for all workers.

The same race also affects `flecs_query_mark_fields_dirty`
(`change_detection.c:487`) when workers process entities from the same table.

### TLC counterexample (3 workers, expected final dirty_state = 3)

```
State 1:  dirtyState = 0, all workers iterating
State 4:  Worker 1 finishes, reads dirtyState = 0, writes 1
State 7:  Worker 2 finishes, reads dirtyState = 1
State 9:  Worker 3 finishes, reads dirtyState = 1  (stale!)
State 10: Worker 3 writes 1 + 1 = 2
State 12: Worker 2 writes 1 + 1 = 2 (overwrites, same value but lost update)
State 14: DONE: dirtyState = 2, expected 3 — VIOLATION
```

### Impact

- **Functional bug**: change detection monitor can get out of sync with reality
- A subsequent `ecs_query_changed()` call may incorrectly return `false`,
  causing a system to skip processing of actually-modified data
- Unlike the statistics counter races, this affects correctness, not just
  profiling

### Fix

Use atomic increments for `dirty_state` updates, or accumulate dirty flags
per-stage and merge them during the sync point.

---

## Bug 4: `query->eval_count` Inconsistent Atomicity (LOW)

**Spec:** `EvalCountRace.tla`
**Invariant violated:** `NoLostEvalCount`
**TLC result:** 632 states, <1s

### Description

`query->eval_count` is incremented from multiple sites with inconsistent
atomicity guarantees:

| Site | Operation | Atomic with `FLECS_ACCURATE_COUNTERS`? |
|------|-----------|---------------------------------------|
| `eval_iter.c:551` | `ecs_os_linc(&q->eval_count)` | Yes (becomes `ecs_os_lainc`) |
| `api.c:492` | `q->eval_count ++` | **Never** |
| `api.c:522` | `q->eval_count ++` | **Never** |
| `observer.c:643` | `o->query->eval_count --` | **Never** |

Even with `FLECS_ACCURATE_COUNTERS` enabled, the `api.c` and `observer.c`
sites use plain `++`/`--`, defeating the atomicity of the `eval_iter.c` site.
Mixing atomic and non-atomic operations on the same field is undefined behavior.

The same inconsistency exists for `world->info.queries_ran_total`
(`eval_iter.c:267,313`) which is only statistics.

### TLC counterexample

Shows Worker 1's `ecs_query_iter` increment and a concurrent
`ecs_query_has_table` call both reading `evalCount = 0`, leading to
final `evalCount = 2` instead of expected `3`.

### Impact

- Incorrect profiling/statistics counters
- Technically undefined behavior under C11 memory model
- Low practical impact since `eval_count` doesn't affect system behavior

### Fix

Use `ecs_os_linc` (or atomic operations) consistently at all sites that
modify `eval_count`, not just the `eval_iter.c` site.

---

## Additional Races Found (Not Formally Specified)

These were identified through source code analysis but not given full TLA+
specs because they follow the same lost-update pattern as the above.

### `world->info.observers_ran_total ++` (observer.c:501)

Plain `int64_t` increment on shared world state. Unlike `systems_ran_total`
(which uses `ecs_os_linc`), this always uses plain `++`. Safe under the normal
pipeline (observers fire during single-threaded merge), but inconsistent.

### `world->info.emit_time_total +=` (observable.c:1561)

Non-atomic float accumulation on shared world state. Same category as
`time_spent`, but only triggered during `ecs_emit` which runs single-threaded
during merge.

### `cache->prev_match_count` write (cache_iter.c:77)

Multiple workers write the same value to `cache->prev_match_count` during
`ecs_query_iter`. Benign race (all threads compute the same value), but
technically undefined behavior.

### `qm->ptrs[]` and `qm->table_version` writes (cache_iter.c:181,201)

Multiple workers update shared cache match pointers during iteration. The code
acknowledges this with a comment: "This can be done safely from multiple threads
since all the read data is immutable." Benign in practice but technically UB.

### `world->event_id ++` (observable.c:1260)

Non-atomic increment used for event deduplication. Safe under the normal
pipeline (events only emitted during single-threaded merge/immediate execution),
but has no guard against concurrent `ecs_emit` calls.

---

## Methodology

All bugs were found using TLA+ model checking with the TLC model checker.

**Approach:** We extracted the concurrency-relevant portions of Flecs' C code
into TLA+ specifications, modeling non-atomic read-modify-write operations as
separate Read and Write steps with arbitrary interleaving between threads. This
is the standard technique for finding concurrency bugs via formal methods.

**Model size:** All specifications use small constants (2-3 threads, small
domains) with state constraints to keep TLC runs under 1 second. The bugs
are found at shallow depths (3-14 steps), confirming they are easily reachable
race conditions, not exotic corner cases.

**Tool:** TLC model checker via Clojure/Recife:
```bash
clojure -Sdeps '{:deps {pfeodrippe/recife {:mvn/version "0.22.0"}}}' \
  -M -e '(tlc2.TLC/main (into-array String ["-config" "Spec.cfg" ...]))'
```

**Files:**
- `EnsureDirectWrite.tla` / `.cfg` — Bug 1 (ecs_ensure direct-write race)
- `TimeSpentRace.tla` / `.cfg` — Bug 2 (time_spent lost update)
- `DirtyStateRace.tla` / `.cfg` — Bug 3 (dirty_state change detection race)
- `EvalCountRace.tla` / `.cfg` — Bug 4 (eval_count inconsistent atomicity)
- `EntityIndexRace.tla` / `.cfg` — Phase 2 (invalidated: user error scenario)
- `MultiStageMerge.tla` / `.cfg` — Phase 2 (invalidated: documented behavior)
- `OverrideWriteRace.tla` / `.cfg` — Phase 2 (invalidated: pipeline-protected)

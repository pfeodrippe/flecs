--------------------------- MODULE EntityIndexRace ----------------------------
(*
 * Entity Index Race Conditions — Bug-Hunting Spec for Flecs ECS
 *
 * Models what happens when multiple threads call flecs_entity_index_new_id
 * and flecs_entity_index_remove CONCURRENTLY on the shared entity index,
 * with NO synchronization.
 *
 * In Flecs, the entity index uses:
 *   - dense[]: array of entity IDs (with generation)
 *   - alive_count: partition boundary in dense array
 *   - max_id: highest entity ID ever allocated
 *   - pages[]: sparse array for entity -> record mapping
 *
 * All of these are plain (non-atomic) shared mutable state.
 * In debug builds, ecs_assert(!(EcsWorldMultiThreaded)) guards entity
 * creation. In RELEASE builds, this assert is stripped — leaving zero
 * protection if user code calls ecs_new() from a worker thread.
 *
 * The stale comment in entity.c:147 says "thread safe (uses atomic inc
 * when in threading mode)" — this is FALSE in current code. There are
 * no atomics anywhere in entity_index.c.
 *
 * RACES MODELED:
 *
 * 1. Two threads recycle simultaneously:
 *    Both read alive_count, both return dense[alive_count], both increment.
 *    Result: same entity ID returned to both threads.
 *    Source: entity_index.c: flecs_entity_index_new_id, recycling path
 *
 * 2. Two threads create new IDs simultaneously:
 *    Both read max_id, both get same ID, both increment.
 *    Result: same entity ID allocated twice, dense array corruption.
 *    Source: entity_index.c: flecs_entity_index_new_id, creation path
 *
 * 3. One thread creates while another deletes:
 *    Thread A calls new_id (reads alive_count), Thread B calls remove
 *    (decrements alive_count, swaps dense entries). Thread A now reads
 *    a stale dense slot.
 *    Source: entity_index.c: flecs_entity_index_new_id + _remove
 *
 * We model the NON-ATOMIC read-modify-write as separate Read and Write
 * steps with arbitrary interleaving. This is the standard technique for
 * finding races with TLA+.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Threads,          \* Set of thread IDs (e.g., {t1, t2})
    MaxEntityId,      \* Maximum entity ID space (e.g., 3)
    MaxGeneration     \* Maximum generation for bounding (e.g., 2)

VARIABLES
    (* --- Shared entity index state (NO synchronization) --- *)
    dense,            \* Function: 1..capacity -> entity ID (with gen) or 0
    alive_count,      \* Int: partition point; dense[1..alive_count] = alive
    max_id,           \* Int: highest ID ever issued
    records,          \* Function: entity_id -> [dense_idx, alive]

    (* --- Per-thread local state (modeling interleaved RMW) --- *)
    pc,               \* Thread -> program counter
    local_ac,         \* Thread -> local copy of alive_count (read phase)
    local_maxid,      \* Thread -> local copy of max_id (read phase)
    local_entity,     \* Thread -> entity ID this thread got/is working with
    threadOp,         \* Thread -> "new" | "delete" | "idle"

    (* --- Bug detection --- *)
    allocated         \* Set of entity IDs currently "owned" by some thread

vars == <<dense, alive_count, max_id, records,
          pc, local_ac, local_maxid, local_entity, threadOp,
          allocated>>

EntityIds == 1..MaxEntityId
Generations == 0..MaxGeneration

(* Entity ID with generation — simplified as a record *)
EntityWithGen(id, gen) == [id |-> id, gen |-> gen]

NullEntity == [id |-> 0, gen |-> 0]

Capacity == MaxEntityId + 1  \* dense array capacity (1-indexed, slot 0 unused)

-----------------------------------------------------------------------------
(* Initial state: empty entity index *)

Init ==
    /\ dense = [i \in 1..Capacity |-> NullEntity]
    /\ alive_count = 0
    /\ max_id = 0
    /\ records = [id \in EntityIds |-> [dense_idx |-> 0, alive |-> FALSE]]
    /\ pc = [t \in Threads |-> "idle"]
    /\ local_ac = [t \in Threads |-> 0]
    /\ local_maxid = [t \in Threads |-> 0]
    /\ local_entity = [t \in Threads |-> 0]
    /\ threadOp = [t \in Threads |-> "idle"]
    /\ allocated = {}

-----------------------------------------------------------------------------
(* === OPERATION: flecs_entity_index_new_id (recycling path) ===
 *
 * Real C code:
 *   if (index->alive_count != ecs_vec_count(&index->dense)) {
 *       return dense[alive_count++];  // NON-ATOMIC RMW
 *   }
 *
 * We split this into:
 *   Step 1 (ReadAC): thread reads alive_count into local_ac
 *   Step 2 (CheckRecycle): thread checks if recyclable slots exist
 *   Step 3 (RecycleWrite): thread reads dense[local_ac+1], writes alive_count+1
 *)

(* Thread decides to create a new entity *)
StartNew(t) ==
    /\ pc[t] = "idle"
    /\ threadOp' = [threadOp EXCEPT ![t] = "new"]
    /\ pc' = [pc EXCEPT ![t] = "read_ac"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_maxid, local_entity, allocated>>

(* Step 1: Read alive_count (non-atomic) *)
ReadAC(t) ==
    /\ pc[t] = "read_ac"
    /\ threadOp[t] = "new"
    /\ local_ac' = [local_ac EXCEPT ![t] = alive_count]
    /\ pc' = [pc EXCEPT ![t] = "check_recycle"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_maxid, local_entity, threadOp, allocated>>

(* Step 2: Check if there are recyclable slots *)
CheckRecycle(t) ==
    /\ pc[t] = "check_recycle"
    /\ threadOp[t] = "new"
    \* In real code: alive_count != vec_count(dense)
    \* If local_ac < total entries in dense, there's a recyclable slot
    /\ IF local_ac[t] < max_id THEN
           \* Recyclable path: will read dense[alive_count + 1]
           pc' = [pc EXCEPT ![t] = "recycle_read"]
       ELSE
           \* Creation path: will allocate new ID
           pc' = [pc EXCEPT ![t] = "create_read_maxid"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_maxid, local_entity, threadOp, allocated>>

(* === RECYCLING PATH === *)

(* Step 3a: Read entity from dense[local_ac + 1] — the recyclable slot *)
RecycleRead(t) ==
    /\ pc[t] = "recycle_read"
    /\ threadOp[t] = "new"
    /\ LET idx == local_ac[t] + 1
       IN IF idx >= 1 /\ idx <= Capacity THEN
              local_entity' = [local_entity EXCEPT ![t] = dense[idx].id]
          ELSE
              local_entity' = [local_entity EXCEPT ![t] = 0]
    /\ pc' = [pc EXCEPT ![t] = "recycle_write_ac"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_maxid, threadOp, allocated>>

(* Step 3b: Write alive_count = local_ac + 1 — NON-ATOMIC *)
RecycleWriteAC(t) ==
    /\ pc[t] = "recycle_write_ac"
    /\ threadOp[t] = "new"
    /\ alive_count' = local_ac[t] + 1  \* NOT alive_count + 1!
    /\ pc' = [pc EXCEPT ![t] = "finish_new"]
    /\ UNCHANGED <<dense, max_id, records,
                   local_ac, local_maxid, local_entity, threadOp, allocated>>

(* === CREATION PATH === *)

(* Step 3c: Read max_id *)
CreateReadMaxId(t) ==
    /\ pc[t] = "create_read_maxid"
    /\ threadOp[t] = "new"
    /\ local_maxid' = [local_maxid EXCEPT ![t] = max_id]
    /\ pc' = [pc EXCEPT ![t] = "create_write_maxid"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_entity, threadOp, allocated>>

(* Step 3d: Write max_id = local_maxid + 1 — NON-ATOMIC *)
CreateWriteMaxId(t) ==
    /\ pc[t] = "create_write_maxid"
    /\ threadOp[t] = "new"
    /\ local_maxid[t] + 1 <= MaxEntityId  \* Don't exceed entity space
    /\ max_id' = local_maxid[t] + 1
    /\ local_entity' = [local_entity EXCEPT ![t] = local_maxid[t] + 1]
    /\ pc' = [pc EXCEPT ![t] = "create_write_dense"]
    /\ UNCHANGED <<dense, alive_count, records,
                   local_ac, local_maxid, threadOp, allocated>>

(* Step 3e: Write dense[alive_count + 1] and increment alive_count *)
CreateWriteDense(t) ==
    /\ pc[t] = "create_write_dense"
    /\ threadOp[t] = "new"
    /\ LET newId == local_entity[t]
           idx == local_ac[t] + 1
       IN /\ idx >= 1 /\ idx <= Capacity
          /\ dense' = [dense EXCEPT ![idx] = EntityWithGen(newId, 0)]
          /\ alive_count' = local_ac[t] + 1  \* Uses STALE local_ac
          /\ records' = [records EXCEPT ![newId] =
                            [dense_idx |-> idx, alive |-> TRUE]]
    /\ pc' = [pc EXCEPT ![t] = "finish_new"]
    /\ UNCHANGED <<max_id, local_ac, local_maxid, local_entity,
                   threadOp, allocated>>

(* Finish: thread records its allocated entity *)
FinishNew(t) ==
    /\ pc[t] = "finish_new"
    /\ threadOp[t] = "new"
    /\ local_entity[t] > 0  \* Got a valid entity
    /\ allocated' = allocated \cup {[thread |-> t, entity |-> local_entity[t]]}
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ threadOp' = [threadOp EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_maxid, local_entity>>

-----------------------------------------------------------------------------
(* === OPERATION: flecs_entity_index_remove ===
 *
 * Real C code:
 *   int32_t dense = r->dense;
 *   int32_t i_swap = --index->alive_count;  // NON-ATOMIC
 *   // swap dense[dense] with dense[i_swap]
 *   // bump generation on removed entity
 *
 * We model this as:
 *   Step 1: Read alive_count, pick entity to delete
 *   Step 2: Decrement alive_count, do the swap
 *)

StartDelete(t) ==
    /\ pc[t] = "idle"
    /\ alive_count > 0
    /\ \E eid \in EntityIds :
        /\ records[eid].alive
        /\ threadOp' = [threadOp EXCEPT ![t] = "delete"]
        /\ local_entity' = [local_entity EXCEPT ![t] = eid]
        /\ pc' = [pc EXCEPT ![t] = "delete_read_ac"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_ac, local_maxid, allocated>>

DeleteReadAC(t) ==
    /\ pc[t] = "delete_read_ac"
    /\ threadOp[t] = "delete"
    /\ local_ac' = [local_ac EXCEPT ![t] = alive_count]
    /\ pc' = [pc EXCEPT ![t] = "delete_write"]
    /\ UNCHANGED <<dense, alive_count, max_id, records,
                   local_maxid, local_entity, threadOp, allocated>>

DeleteWrite(t) ==
    /\ pc[t] = "delete_write"
    /\ threadOp[t] = "delete"
    /\ LET eid == local_entity[t]
           r == records[eid]
           swap_idx == local_ac[t]  \* Uses stale local copy!
           dense_idx == r.dense_idx
       IN /\ swap_idx >= 1
          /\ dense_idx >= 1
          /\ dense_idx <= Capacity
          /\ swap_idx <= Capacity
          (* Decrement alive_count using stale local value *)
          /\ alive_count' = local_ac[t] - 1
          (* Swap dense entries *)
          /\ IF dense_idx # swap_idx THEN
                 LET swap_entity == dense[swap_idx]
                 IN /\ dense' = [dense EXCEPT
                         ![dense_idx] = swap_entity,
                         ![swap_idx] = EntityWithGen(eid,
                             IF dense[dense_idx].gen < MaxGeneration
                             THEN dense[dense_idx].gen + 1
                             ELSE MaxGeneration)]
                    /\ records' = [records EXCEPT
                         ![eid] = [dense_idx |-> swap_idx, alive |-> FALSE],
                         ![swap_entity.id] = [dense_idx |-> dense_idx,
                                               alive |-> records[swap_entity.id].alive]]
             ELSE
                 /\ dense' = [dense EXCEPT
                     ![swap_idx] = EntityWithGen(eid,
                         IF dense[dense_idx].gen < MaxGeneration
                         THEN dense[dense_idx].gen + 1
                         ELSE MaxGeneration)]
                 /\ records' = [records EXCEPT
                     ![eid] = [dense_idx |-> swap_idx, alive |-> FALSE]]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ threadOp' = [threadOp EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<max_id, local_ac, local_maxid, local_entity, allocated>>

-----------------------------------------------------------------------------
Next ==
    \E t \in Threads :
        \/ StartNew(t)
        \/ ReadAC(t)
        \/ CheckRecycle(t)
        \/ RecycleRead(t)
        \/ RecycleWriteAC(t)
        \/ CreateReadMaxId(t)
        \/ CreateWriteMaxId(t)
        \/ CreateWriteDense(t)
        \/ FinishNew(t)
        \/ StartDelete(t)
        \/ DeleteReadAC(t)
        \/ DeleteWrite(t)

Spec == Init /\ [][Next]_vars

FairSpec ==
    Spec
    /\ \A t \in Threads :
        /\ WF_vars(ReadAC(t))
        /\ WF_vars(CheckRecycle(t))
        /\ WF_vars(RecycleRead(t))
        /\ WF_vars(RecycleWriteAC(t))
        /\ WF_vars(CreateReadMaxId(t))
        /\ WF_vars(CreateWriteMaxId(t))
        /\ WF_vars(CreateWriteDense(t))
        /\ WF_vars(FinishNew(t))
        /\ WF_vars(DeleteReadAC(t))
        /\ WF_vars(DeleteWrite(t))

StateConstraint ==
    /\ max_id <= MaxEntityId
    /\ \A t \in Threads : local_entity[t] <= MaxEntityId

-----------------------------------------------------------------------------
(* SAFETY INVARIANTS *)

TypeOK ==
    /\ alive_count \in 0..Capacity
    /\ max_id \in 0..MaxEntityId
    /\ \A t \in Threads : pc[t] \in {"idle", "read_ac", "check_recycle",
           "recycle_read", "recycle_write_ac",
           "create_read_maxid", "create_write_maxid", "create_write_dense",
           "finish_new", "delete_read_ac", "delete_write"}

(* ============================================================
 * BUG-FINDING INVARIANT: NoDuplicateEntityAllocation
 *
 * Two threads must NEVER receive the same entity ID from new_id.
 * In Flecs, this IS violated when two threads call
 * flecs_entity_index_new_id concurrently in release mode:
 *   - Both read same alive_count (recycling) or same max_id (creation)
 *   - Both return the same entity ID
 *   - Both write alive_count+1 or max_id+1 (lost update)
 *
 * Source: entity_index.c: flecs_entity_index_new_id
 * ============================================================ *)
NoDuplicateEntityAllocation ==
    \A a1, a2 \in allocated :
        (a1.thread # a2.thread) => (a1.entity # a2.entity)

(* alive_count must never go negative *)
AliveCountNonNegative ==
    alive_count >= 0

(* alive_count must never exceed total entities *)
AliveCountBounded ==
    alive_count <= max_id

(* No entity should have a dense_idx that's out of bounds *)
RecordsConsistent ==
    \A eid \in EntityIds :
        records[eid].alive =>
            /\ records[eid].dense_idx >= 1
            /\ records[eid].dense_idx <= alive_count

-----------------------------------------------------------------------------
(* TEMPORAL PROPERTIES *)

(* If a thread starts creating an entity, it eventually finishes *)
CreationCompletes ==
    \A t \in Threads :
        (pc[t] = "read_ac" /\ threadOp[t] = "new") ~> (pc[t] = "idle")

(* If a thread starts deleting, it eventually finishes *)
DeletionCompletes ==
    \A t \in Threads :
        (pc[t] = "delete_read_ac") ~> (pc[t] = "idle")

(* The system always eventually returns to all-idle *)
EventuallyAllIdle ==
    []<>(\A t \in Threads : pc[t] = "idle")

=============================================================================

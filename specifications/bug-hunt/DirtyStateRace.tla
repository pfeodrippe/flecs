--------------------------- MODULE DirtyStateRace ------------------------------
(*
 * Models the dirty_state[column + 1] ++ race in Flecs change detection.
 *
 * SCENARIO:
 *   - A multi-threaded system has a query with [inout] Position (iterated)
 *     and a fixed-source field like [inout] GlobalConfig($singleton).
 *   - The pipeline dispatches N workers to iterate the system query.
 *   - When each worker finishes iteration (ecs_query_next returns false),
 *     flecs_query_mark_fixed_fields_dirty is called (eval_iter.c:258).
 *   - This function iterates fixed write fields and does:
 *       dirty_state[column + 1] ++
 *     (change_detection.c:526)
 *   - All workers increment the SAME dirty_state entry for the singleton's
 *     table, because the fixed source is the same for all workers.
 *
 * BUG:
 *   `dirty_state[column + 1] ++` is a non-atomic read-modify-write.
 *   With N workers, the expected result is dirty_state incremented by N.
 *   Due to lost updates, the actual increment can be less than N.
 *
 *   This causes change detection to MISS changes: a subsequent query
 *   checking if the singleton was modified may see a dirty_state that
 *   is lower than expected, causing flecs_query_check_match_monitor
 *   to incorrectly conclude the data hasn't changed.
 *
 * The same race also affects flecs_query_mark_fields_dirty
 * (change_detection.c:487) when workers process entities from the
 * same table — they all increment dirty_state for that table's columns.
 *
 * FUNCTIONAL CONSEQUENCE:
 *   Unlike the time_spent or eval_count races (which are statistics only),
 *   dirty_state is used by the change detection system to determine whether
 *   systems need to re-run. A lost increment means the monitor gets out of
 *   sync with reality, potentially causing a system to skip processing
 *   modified data.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Workers,    \* Set of worker thread IDs
    NULL        \* Model value

VARIABLES
    dirtyState,     \* The shared dirty_state[column+1] counter
    workerPC,       \* Per-worker program counter
    workerLocal,    \* Per-worker local register (for read-modify-write)
    phase           \* "running" | "done"

vars == <<dirtyState, workerPC, workerLocal, phase>>

WorkerPCs == {"iterating", "finishIter", "readDirty", "writeDirty", "done"}

------------------------------------------------------------------------
\* Initialization
\* dirty_state starts at some value D (we use 0).
\* Each worker will increment it by 1 when finishing iteration.
------------------------------------------------------------------------

Init ==
    /\ dirtyState = 0
    /\ workerPC = [w \in Workers |-> "iterating"]
    /\ workerLocal = [w \in Workers |-> 0]
    /\ phase = "running"

------------------------------------------------------------------------
\* Worker iteration and dirty state update
------------------------------------------------------------------------

\* Worker finishes iterating (ecs_query_next returns false)
\* This triggers flecs_query_mark_fixed_fields_dirty
WorkerFinishIter(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "iterating"
    /\ workerPC' = [workerPC EXCEPT ![w] = "finishIter"]
    /\ UNCHANGED <<dirtyState, workerLocal, phase>>

\* Worker reads dirty_state[column+1] (the "read" part of ++)
WorkerReadDirty(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "finishIter"
    /\ workerLocal' = [workerLocal EXCEPT ![w] = dirtyState]
    /\ workerPC' = [workerPC EXCEPT ![w] = "readDirty"]
    /\ UNCHANGED <<dirtyState, phase>>

\* Worker writes dirty_state[column+1] = local + 1 (the "write" part of ++)
WorkerWriteDirty(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "readDirty"
    /\ dirtyState' = workerLocal[w] + 1
    /\ workerPC' = [workerPC EXCEPT ![w] = "writeDirty"]
    /\ UNCHANGED <<workerLocal, phase>>

\* Worker done
WorkerDone(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "writeDirty"
    /\ workerPC' = [workerPC EXCEPT ![w] = "done"]
    /\ UNCHANGED <<dirtyState, workerLocal, phase>>

\* All workers done
Finish ==
    /\ phase = "running"
    /\ \A w \in Workers : workerPC[w] = "done"
    /\ phase' = "done"
    /\ UNCHANGED <<dirtyState, workerPC, workerLocal>>

------------------------------------------------------------------------
\* Next-state relation
------------------------------------------------------------------------

Next ==
    \/ \E w \in Workers :
        \/ WorkerFinishIter(w)
        \/ WorkerReadDirty(w)
        \/ WorkerWriteDirty(w)
        \/ WorkerDone(w)
    \/ Finish

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
\* INVARIANTS
------------------------------------------------------------------------

\* The expected final value: each of N workers increments by 1
ExpectedIncrement == Cardinality(Workers)

\* NoLostDirtyUpdate:
\* When all workers are done, dirty_state should have been incremented
\* by exactly the number of workers. Lost updates cause this to be less.
NoLostDirtyUpdate ==
    phase = "done" => dirtyState = ExpectedIncrement

\* ChangeDetectionIntegrity:
\* Weaker check — dirty_state should be at LEAST the expected value.
\* (In a correct system, it should be exactly the expected value.)
ChangeDetectionIntegrity ==
    phase = "done" => dirtyState >= ExpectedIncrement

\* TypeOK
TypeOK ==
    /\ dirtyState \in Nat
    /\ workerPC \in [Workers -> WorkerPCs]
    /\ workerLocal \in [Workers -> Nat]
    /\ phase \in {"running", "done"}

========================================================================

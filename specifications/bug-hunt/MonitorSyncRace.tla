----------------------------- MODULE MonitorSyncRace -----------------------------
(*
 * BUG: flecs_query_sync_match_monitor concurrent write race
 *
 * LOCATION: src/query/cache/change_detection.c:531-580
 *           Called from src/query/engine/eval_iter.c:140
 *
 * DESCRIPTION:
 *   When a multi-threaded system iterates a cached query with change detection,
 *   multiple workers process different rows of the SAME table match. Each worker
 *   has its own iterator, but they all reference the SAME cache match object
 *   (qit->elem points to the same ecs_query_cache_match_t).
 *
 *   When a worker advances to the next batch (redo=true), ecs_query_next calls
 *   flecs_query_change_detection -> flecs_query_sync_match_monitor on the
 *   shared cache match. This function writes to match->_monitor array:
 *     - Line 556: monitor[0] = dirty_state[0]
 *     - Line 574-575: monitor[field + 1] = dirty_state[tc.column + 1]
 *     - Line 579: cache->prev_match_count = cache->match_count
 *
 *   Since dirty_state can be concurrently incremented (Bug #3: DirtyStateRace),
 *   different workers may read different values from dirty_state. The writes
 *   to _monitor are non-atomic, causing:
 *   1. Lost writes when two workers write to the same monitor index
 *   2. Inconsistent state where _monitor records a stale dirty_state value
 *   3. Functional bug: ecs_query_changed() returns incorrect results
 *
 * IMPACT:
 *   - Change detection may report "not changed" when data was actually modified
 *   - Systems relying on change detection may skip processing updates
 *   - Particularly affects singletons and fixed-source queries
 *
 * SEVERITY: HIGH (functional bug affecting correctness, not just counters)
 *
 * TLC VERIFICATION:
 *   The spec finds a trace where two workers both write to the same monitor
 *   field with potentially different values, demonstrating the data race.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Workers,        \* Set of worker IDs (e.g., {1, 2})
    NumFields       \* Number of query fields tracked in monitor

VARIABLES
    dirty_state,    \* Shared dirty_state array [0..NumFields] -> Nat
    monitor,        \* Shared _monitor array [0..NumFields] -> Nat
    worker_phase,   \* Worker phase: "init", "iterate", "sync", "done"
    worker_dirty_snapshot,  \* What each worker read from dirty_state
    concurrent_monitor_writes  \* Tracks if multiple workers wrote to monitor concurrently

vars == <<dirty_state, monitor, worker_phase, worker_dirty_snapshot, concurrent_monitor_writes>>

\* Type invariant
TypeOK ==
    /\ dirty_state \in [0..NumFields -> Nat]
    /\ monitor \in [0..NumFields -> Nat]
    /\ worker_phase \in [Workers -> {"init", "iterate", "sync", "done"}]
    /\ worker_dirty_snapshot \in [Workers -> [0..NumFields -> Nat]]
    /\ concurrent_monitor_writes \in BOOLEAN

\* Initial state
Init ==
    /\ dirty_state = [i \in 0..NumFields |-> 0]
    /\ monitor = [i \in 0..NumFields |-> 0]
    /\ worker_phase = [w \in Workers |-> "init"]
    /\ worker_dirty_snapshot = [w \in Workers |-> [i \in 0..NumFields |-> 0]]
    /\ concurrent_monitor_writes = FALSE

\* Worker starts iterating the cached query
WorkerStartIterate(w) ==
    /\ worker_phase[w] = "init"
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "iterate"]
    /\ UNCHANGED <<dirty_state, monitor, worker_dirty_snapshot, concurrent_monitor_writes>>

\* During iteration, a worker may modify component data.
\* This triggers flecs_query_mark_fields_dirty which increments dirty_state.
\* Multiple workers can increment dirty_state concurrently (Bug #3).
WorkerModifyData(w) ==
    /\ worker_phase[w] = "iterate"
    \* Non-atomic increment (interleaved read-modify-write)
    /\ \E field \in 0..NumFields:
        LET old == dirty_state[field]
        IN dirty_state' = [dirty_state EXCEPT ![field] = old + 1]
    /\ UNCHANGED <<monitor, worker_phase, worker_dirty_snapshot, concurrent_monitor_writes>>

\* Worker reads dirty_state in preparation for sync.
\* This simulates the worker reading dirty_state[column] in sync_match_monitor.
\* Due to concurrent increments, different workers may read different values.
WorkerReadDirtyState(w) ==
    /\ worker_phase[w] = "iterate"
    \* Snapshot the current dirty_state (what this worker sees)
    /\ worker_dirty_snapshot' = [worker_dirty_snapshot EXCEPT ![w] = dirty_state]
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "sync"]
    /\ UNCHANGED <<dirty_state, monitor, concurrent_monitor_writes>>

\* Worker writes to monitor array in flecs_query_sync_match_monitor.
\* This is the core race: multiple workers write to the SAME monitor array.
WorkerWriteMonitor(w) ==
    /\ worker_phase[w] = "sync"
    \* Write the snapshot to monitor (non-atomic writes)
    /\ \E field \in 0..NumFields:
        /\ monitor' = [monitor EXCEPT ![field] = worker_dirty_snapshot[w][field]]
        \* Detect concurrent writes: if another worker is also in "sync" phase
        /\ concurrent_monitor_writes' = 
            IF \E other \in Workers : other # w /\ worker_phase[other] = "sync"
            THEN TRUE
            ELSE concurrent_monitor_writes
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "done"]
    /\ UNCHANGED <<dirty_state, worker_dirty_snapshot>>

\* All workers done
AllDone ==
    /\ \A w \in Workers : worker_phase[w] = "done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ \E w \in Workers : WorkerStartIterate(w)
    \/ \E w \in Workers : WorkerModifyData(w)
    \/ \E w \in Workers : WorkerReadDirtyState(w)
    \/ \E w \in Workers : WorkerWriteMonitor(w)
    \/ AllDone

\* Fairness: all workers eventually complete
Fairness ==
    /\ \A w \in Workers : WF_vars(WorkerStartIterate(w))
    /\ \A w \in Workers : WF_vars(WorkerReadDirtyState(w))
    /\ \A w \in Workers : WF_vars(WorkerWriteMonitor(w))

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

\* INVARIANT: No concurrent monitor writes should occur.
\* If this is violated, we have a race condition.
NoConcurrentMonitorWrites == ~concurrent_monitor_writes

\* INVARIANT: Monitor should accurately reflect the final dirty_state.
\* After all workers are done, monitor should equal dirty_state.
\* Due to the race, this can be violated.
MonitorConsistency ==
    (\A w \in Workers : worker_phase[w] = "done") =>
    (monitor = dirty_state)

\* INVARIANT: Alternative formulation - if workers read different dirty_state
\* values and both write to monitor, monitor is inconsistent.
\* This detects the "stale write wins over fresh write" scenario.
NoStaleMonitorValue ==
    (\A w \in Workers : worker_phase[w] = "done") =>
    (\A field \in 0..NumFields : monitor[field] >= dirty_state[field] - Cardinality(Workers) + 1)

\* PROPERTY: Eventually all workers complete
AllWorkersComplete == <>(\A w \in Workers : worker_phase[w] = "done")

===============================================================================

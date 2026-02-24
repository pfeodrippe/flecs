----------------------------- MODULE MonitorAllocRace -----------------------------
(*
 * BUG: flecs_query_get_match_monitor check-then-act race (memory leak)
 *
 * LOCATION: src/query/cache/change_detection.c:48-93
 *
 * DESCRIPTION:
 *   When a multi-threaded system iterates a cached query with change detection,
 *   `flecs_query_get_match_monitor` is called to lazily initialize the monitor
 *   array for each cache match.
 *
 *   The function has a classic check-then-act race:
 *     Line 48: if (match->_monitor) { return false; }  // CHECK
 *     Line 52: monitor = flecs_balloc(...)             // ALLOCATE
 *     Line 93: match->_monitor = monitor;              // WRITE
 *
 *   When multiple workers concurrently hit this function for the same match:
 *   1. Worker A checks match->_monitor == NULL
 *   2. Worker B checks match->_monitor == NULL (still NULL!)
 *   3. Worker A allocates monitor_A
 *   4. Worker B allocates monitor_B
 *   5. Worker A writes match->_monitor = monitor_A
 *   6. Worker B writes match->_monitor = monitor_B (overwrites!)
 *   7. monitor_A is now leaked (no pointer to it)
 *
 * IMPACT:
 *   - Memory leak: allocated monitors are lost
 *   - Under high concurrency, significant memory can be leaked
 *   - The race compounds over time if queries are repeatedly iterated
 *
 * SEVERITY: MEDIUM (memory leak, not data corruption)
 *
 * TLC VERIFICATION:
 *   The spec finds traces where multiple workers allocate monitors,
 *   resulting in leaked allocations.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    Workers         \* Set of worker IDs (e.g., {1, 2})

VARIABLES
    match_monitor,      \* Shared match->_monitor (NULL or allocation ID)
    worker_phase,       \* Worker phase: "idle", "check", "alloc", "write", "done"
    worker_alloc,       \* Per-worker: allocated monitor ID (0 = none)
    next_alloc_id,      \* Counter for allocation IDs
    total_allocs,       \* Total number of allocations made
    leaked_allocs       \* Number of leaked allocations

vars == <<match_monitor, worker_phase, worker_alloc, next_alloc_id, total_allocs, leaked_allocs>>

\* Type invariant
TypeOK ==
    /\ match_monitor \in Nat  \* 0 = NULL, >0 = allocation ID
    /\ worker_phase \in [Workers -> {"idle", "check", "alloc", "write", "done"}]
    /\ worker_alloc \in [Workers -> Nat]
    /\ next_alloc_id \in Nat
    /\ total_allocs \in Nat
    /\ leaked_allocs \in Nat

\* Initial state
Init ==
    /\ match_monitor = 0  \* NULL
    /\ worker_phase = [w \in Workers |-> "idle"]
    /\ worker_alloc = [w \in Workers |-> 0]
    /\ next_alloc_id = 1
    /\ total_allocs = 0
    /\ leaked_allocs = 0

\* Worker enters flecs_query_get_match_monitor (via query iteration path)
WorkerEnter(w) ==
    /\ worker_phase[w] = "idle"
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "check"]
    /\ UNCHANGED <<match_monitor, worker_alloc, next_alloc_id, total_allocs, leaked_allocs>>

\* Worker checks if (match->_monitor) - line 48
\* If monitor exists, worker is done (return false)
\* If NULL, proceed to allocate
WorkerCheck(w) ==
    /\ worker_phase[w] = "check"
    /\ IF match_monitor > 0
       THEN \* Monitor already exists, return false
            /\ worker_phase' = [worker_phase EXCEPT ![w] = "done"]
            /\ UNCHANGED <<match_monitor, worker_alloc, next_alloc_id, total_allocs, leaked_allocs>>
       ELSE \* Monitor is NULL, proceed to allocate
            /\ worker_phase' = [worker_phase EXCEPT ![w] = "alloc"]
            /\ UNCHANGED <<match_monitor, worker_alloc, next_alloc_id, total_allocs, leaked_allocs>>

\* Worker allocates a monitor - line 52
WorkerAlloc(w) ==
    /\ worker_phase[w] = "alloc"
    /\ worker_alloc' = [worker_alloc EXCEPT ![w] = next_alloc_id]
    /\ next_alloc_id' = next_alloc_id + 1
    /\ total_allocs' = total_allocs + 1
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "write"]
    /\ UNCHANGED <<match_monitor, leaked_allocs>>

\* Worker writes match->_monitor = monitor - line 93
WorkerWrite(w) ==
    /\ worker_phase[w] = "write"
    \* If match_monitor already has a value (another worker wrote first),
    \* that allocation is now leaked
    /\ leaked_allocs' = IF match_monitor > 0 
                        THEN leaked_allocs + 1 
                        ELSE leaked_allocs
    /\ match_monitor' = worker_alloc[w]
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "done"]
    /\ UNCHANGED <<worker_alloc, next_alloc_id, total_allocs>>

\* All workers done (terminal state)
AllDone ==
    /\ \A w \in Workers : worker_phase[w] = "done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ \E w \in Workers : WorkerEnter(w)
    \/ \E w \in Workers : WorkerCheck(w)
    \/ \E w \in Workers : WorkerAlloc(w)
    \/ \E w \in Workers : WorkerWrite(w)
    \/ AllDone

\* Specification
Spec == Init /\ [][Next]_vars

\* Fairness
Fairness ==
    /\ \A w \in Workers : WF_vars(WorkerEnter(w))
    /\ \A w \in Workers : WF_vars(WorkerCheck(w))
    /\ \A w \in Workers : WF_vars(WorkerAlloc(w))
    /\ \A w \in Workers : WF_vars(WorkerWrite(w))

FairSpec == Spec /\ Fairness

\* INVARIANT: No memory should be leaked.
\* A leak occurs when a monitor is allocated but then overwritten by another.
NoMemoryLeak == leaked_allocs = 0

\* INVARIANT: At most one allocation should occur.
\* With proper synchronization, only one worker should allocate.
AtMostOneAlloc ==
    (\A w \in Workers : worker_phase[w] = "done") =>
    (total_allocs <= 1)

\* INVARIANT: If all workers done, exactly one allocation should be in match_monitor.
\* This checks that we don't have both a leak AND correct final state.
ProperAllocation ==
    (\A w \in Workers : worker_phase[w] = "done") =>
    (total_allocs = leaked_allocs + 1)

\* PROPERTY: Eventually all workers complete
AllWorkersComplete == <>(\A w \in Workers : worker_phase[w] = "done")

===============================================================================

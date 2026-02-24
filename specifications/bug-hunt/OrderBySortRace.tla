----------------------------- MODULE OrderBySortRace -----------------------------
(*
 * BUG: flecs_query_cache_sort_tables concurrent execution race
 *
 * LOCATION: src/query/cache/order_by.c:228-316
 *           Called from src/query/cache/cache_iter.c:71
 *
 * DESCRIPTION:
 *   When a cached query has an `order_by` callback configured, the sorting
 *   function `flecs_query_cache_sort_tables` is called during iterator
 *   initialization (`flecs_query_cache_iter_init` → line 71).
 *
 *   In a multi-threaded system, each worker calls `ecs_query_iter()` to create
 *   its own iterator. This calls `flecs_query_cache_iter_init` which calls
 *   `flecs_query_cache_sort_tables` for queries with `order_by`.
 *
 *   The sorting function:
 *   1. Reads cache->prev_match_count (shared)
 *   2. Calls flecs_query_cache_sort_table() which MODIFIES table entity order!
 *   3. Calls flecs_query_cache_build_sorted_tables() which rebuilds table_slices
 *   4. Writes cache->match_count ++ (non-atomic increment)
 *
 *   Multiple workers calling this concurrently causes:
 *   - Concurrent sorting of the same table (data corruption)
 *   - Lost increments to cache->match_count
 *   - Concurrent writes to cache->table_slices
 *
 * IMPACT:
 *   - Table entity ordering becomes corrupted (sort instability)
 *   - Iteration order becomes non-deterministic during concurrent sorting
 *   - cache->match_count counter loses updates
 *
 * SEVERITY: HIGH (data corruption affecting correctness)
 *
 * TLC VERIFICATION:
 *   The spec finds traces where multiple workers concurrently enter the
 *   sorting phase, demonstrating the race condition.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Workers,       \* Set of worker IDs (e.g., {1, 2})
    TableSize      \* Number of entities in table to sort

VARIABLES
    match_count,           \* Shared cache->match_count
    prev_match_count,      \* Shared cache->prev_match_count  
    table_order,           \* Shared table entity order (sequence of entity indices)
    worker_phase,          \* Worker phase: "init", "check", "sort", "build", "inc", "done"
    tables_sorted,         \* Boolean: did any worker actually sort?
    concurrent_sort,       \* Boolean: were there concurrent sorts?
    match_count_snapshot   \* Per-worker snapshot of match_count for RMW

vars == <<match_count, prev_match_count, table_order, worker_phase, 
          tables_sorted, concurrent_sort, match_count_snapshot>>

\* Generate initial table order [1, 2, ..., TableSize]
InitTableOrder == [i \in 1..TableSize |-> i]

\* Type invariant
TypeOK ==
    /\ match_count \in Nat
    /\ prev_match_count \in Nat
    /\ table_order \in [1..TableSize -> 1..TableSize]
    /\ worker_phase \in [Workers -> {"init", "check", "sort", "build", "inc", "done"}]
    /\ tables_sorted \in BOOLEAN
    /\ concurrent_sort \in BOOLEAN
    /\ match_count_snapshot \in [Workers -> Nat]

\* Initial state
Init ==
    /\ match_count = 0
    /\ prev_match_count = 0
    /\ table_order = InitTableOrder
    /\ worker_phase = [w \in Workers |-> "init"]
    /\ tables_sorted = FALSE
    /\ concurrent_sort = FALSE
    /\ match_count_snapshot = [w \in Workers |-> 0]

\* Worker calls ecs_query_iter() which calls flecs_query_cache_iter_init
WorkerStartIter(w) ==
    /\ worker_phase[w] = "init"
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "check"]
    /\ UNCHANGED <<match_count, prev_match_count, table_order, tables_sorted, 
                   concurrent_sort, match_count_snapshot>>

\* Worker checks if sorting is needed (simulates flecs_query_check_table_monitor)
\* For simplicity, we model the case where sorting IS needed (dirty table)
WorkerCheckDirty(w) ==
    /\ worker_phase[w] = "check"
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "sort"]
    /\ UNCHANGED <<match_count, prev_match_count, table_order, tables_sorted, 
                   concurrent_sort, match_count_snapshot>>

\* Worker sorts the table (flecs_query_cache_sort_table)
\* This modifies the shared table_order!
WorkerSortTable(w) ==
    /\ worker_phase[w] = "sort"
    \* Detect concurrent sorting
    /\ concurrent_sort' = 
        IF \E other \in Workers : other # w /\ worker_phase[other] = "sort"
        THEN TRUE
        ELSE concurrent_sort
    \* Model sorting as a permutation of the table (any permutation)
    /\ \E perm \in [1..TableSize -> 1..TableSize]:
        /\ \A i \in 1..TableSize: \E j \in 1..TableSize: perm[j] = i  \* bijection
        /\ table_order' = perm
    /\ tables_sorted' = TRUE
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "build"]
    /\ UNCHANGED <<match_count, prev_match_count, match_count_snapshot>>

\* Worker builds sorted table slices (flecs_query_cache_build_sorted_tables)
WorkerBuildSlices(w) ==
    /\ worker_phase[w] = "build"
    \* This reads match_count for the RMW
    /\ match_count_snapshot' = [match_count_snapshot EXCEPT ![w] = match_count]
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "inc"]
    /\ UNCHANGED <<match_count, prev_match_count, table_order, tables_sorted, concurrent_sort>>

\* Worker increments match_count (non-atomic ++)
WorkerIncrementMatchCount(w) ==
    /\ worker_phase[w] = "inc"
    \* Write based on snapshot (lost update possible!)
    /\ match_count' = match_count_snapshot[w] + 1
    /\ worker_phase' = [worker_phase EXCEPT ![w] = "done"]
    /\ UNCHANGED <<prev_match_count, table_order, tables_sorted, concurrent_sort, match_count_snapshot>>

\* All workers done
AllDone ==
    /\ \A w \in Workers : worker_phase[w] = "done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ \E w \in Workers : WorkerStartIter(w)
    \/ \E w \in Workers : WorkerCheckDirty(w)
    \/ \E w \in Workers : WorkerSortTable(w)
    \/ \E w \in Workers : WorkerBuildSlices(w)
    \/ \E w \in Workers : WorkerIncrementMatchCount(w)
    \/ AllDone

\* Fairness: all workers eventually complete
Fairness ==
    /\ \A w \in Workers : WF_vars(WorkerStartIter(w))
    /\ \A w \in Workers : WF_vars(WorkerCheckDirty(w))
    /\ \A w \in Workers : WF_vars(WorkerSortTable(w))
    /\ \A w \in Workers : WF_vars(WorkerBuildSlices(w))
    /\ \A w \in Workers : WF_vars(WorkerIncrementMatchCount(w))

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

\* INVARIANT: No concurrent sorting should occur.
\* Concurrent sorting causes table corruption.
NoConcurrentSort == ~concurrent_sort

\* INVARIANT: After all workers complete, match_count should reflect
\* the number of workers that sorted (each contributes 1 increment).
\* Due to lost updates, this can be violated.
NoLostMatchCount ==
    (\A w \in Workers : worker_phase[w] = "done") =>
    (match_count >= Cardinality({w \in Workers : TRUE}))

\* PROPERTY: Eventually all workers complete
AllWorkersComplete == <>(\A w \in Workers : worker_phase[w] = "done")

===============================================================================

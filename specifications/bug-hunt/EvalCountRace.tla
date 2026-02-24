--------------------------- MODULE EvalCountRace -------------------------------
(*
 * Models the query->eval_count inconsistent atomicity race in Flecs.
 *
 * SCENARIO:
 *   - A multi-threaded system runs on N worker threads.
 *   - Each worker calls ecs_query_iter(thread_ctx, system_data->query)
 *     (system.c:85) which calls ecs_os_linc(&q->eval_count) (eval_iter.c:551).
 *   - Without FLECS_ACCURATE_COUNTERS (default), ecs_os_linc is ++ on ptr,
 *     a non-atomic read-modify-write on the SHARED query object.
 *
 * ADDITIONAL INCONSISTENCY:
 *   Even WITH FLECS_ACCURATE_COUNTERS, several sites use plain ++/-- on
 *   eval_count and are NEVER atomic:
 *     - query/api.c:492 — q->eval_count ++ (ecs_query_has_table)
 *     - query/api.c:522 — q->eval_count ++ (ecs_query_has_range)
 *     - observer.c:643  — o->query->eval_count -- (observer filter-out)
 *   These always use plain arithmetic regardless of the flag.
 *
 * BUG:
 *   eval_count is a statistics/profiling counter, so data corruption
 *   doesn't affect correctness. But it IS undefined behavior under C11
 *   (concurrent non-atomic read-modify-write on the same object).
 *
 * This spec models N workers calling ecs_query_iter concurrently, each
 * doing ++eval_count. We also model a concurrent ecs_query_has_table call
 * that does its own ++ (showing the inconsistency even with FLECS_ACCURATE_COUNTERS).
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Workers,        \* Worker threads, e.g. {1, 2}
    NULL            \* Model value

VARIABLES
    evalCount,      \* The shared query->eval_count
    workerPC,       \* Per-worker program counter
    workerLocal,    \* Per-worker local register
    hasTablePC,     \* A concurrent ecs_query_has_table caller
    hasTableLocal,  \* Its local register
    phase           \* "running" | "done"

vars == <<evalCount, workerPC, workerLocal, hasTablePC, hasTableLocal, phase>>

WorkerPCs == {"idle", "read", "write", "done"}

------------------------------------------------------------------------
Init ==
    /\ evalCount = 0
    /\ workerPC = [w \in Workers |-> "idle"]
    /\ workerLocal = [w \in Workers |-> 0]
    /\ hasTablePC = "idle"
    /\ hasTableLocal = 0
    /\ phase = "running"

------------------------------------------------------------------------
\* Worker calls ecs_query_iter -> ecs_os_linc(&q->eval_count)
\* Without FLECS_ACCURATE_COUNTERS: ++(*v) = read + increment + write
------------------------------------------------------------------------

WorkerRead(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "idle"
    /\ workerLocal' = [workerLocal EXCEPT ![w] = evalCount]
    /\ workerPC' = [workerPC EXCEPT ![w] = "read"]
    /\ UNCHANGED <<evalCount, hasTablePC, hasTableLocal, phase>>

WorkerWrite(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "read"
    /\ evalCount' = workerLocal[w] + 1
    /\ workerPC' = [workerPC EXCEPT ![w] = "write"]
    /\ UNCHANGED <<workerLocal, hasTablePC, hasTableLocal, phase>>

WorkerDone(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "write"
    /\ workerPC' = [workerPC EXCEPT ![w] = "done"]
    /\ UNCHANGED <<evalCount, workerLocal, hasTablePC, hasTableLocal, phase>>

------------------------------------------------------------------------
\* Concurrent ecs_query_has_table call does q->eval_count++
\* This is ALWAYS non-atomic (plain ++) even with FLECS_ACCURATE_COUNTERS
------------------------------------------------------------------------

HasTableRead ==
    /\ phase = "running"
    /\ hasTablePC = "idle"
    /\ hasTableLocal' = evalCount
    /\ hasTablePC' = "read"
    /\ UNCHANGED <<evalCount, workerPC, workerLocal, phase>>

HasTableWrite ==
    /\ phase = "running"
    /\ hasTablePC = "read"
    /\ evalCount' = hasTableLocal + 1
    /\ hasTablePC' = "write"
    /\ UNCHANGED <<workerPC, workerLocal, hasTableLocal, phase>>

HasTableDone ==
    /\ phase = "running"
    /\ hasTablePC = "write"
    /\ hasTablePC' = "done"
    /\ UNCHANGED <<evalCount, workerPC, workerLocal, hasTableLocal, phase>>

------------------------------------------------------------------------
\* Finish
------------------------------------------------------------------------

AllDone ==
    /\ \A w \in Workers : workerPC[w] = "done"
    /\ hasTablePC = "done"

Finish ==
    /\ phase = "running"
    /\ AllDone
    /\ phase' = "done"
    /\ UNCHANGED <<evalCount, workerPC, workerLocal, hasTablePC, hasTableLocal>>

------------------------------------------------------------------------
Next ==
    \/ \E w \in Workers :
        \/ WorkerRead(w)
        \/ WorkerWrite(w)
        \/ WorkerDone(w)
    \/ HasTableRead
    \/ HasTableWrite
    \/ HasTableDone
    \/ Finish

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
\* INVARIANTS
------------------------------------------------------------------------

\* Total expected increments: one per worker + one for hasTable
ExpectedTotal == Cardinality(Workers) + 1

\* NoLostEvalCount:
\* When done, eval_count should equal the number of incrementors.
NoLostEvalCount ==
    phase = "done" => evalCount = ExpectedTotal

\* TypeOK
TypeOK ==
    /\ evalCount \in Nat
    /\ workerPC \in [Workers -> WorkerPCs]
    /\ workerLocal \in [Workers -> Nat]
    /\ hasTablePC \in WorkerPCs
    /\ hasTableLocal \in Nat
    /\ phase \in {"running", "done"}

========================================================================

--------------------------- MODULE TimeSpentRace -------------------------------
(*
 * Models the system_data->time_spent non-atomic read-modify-write race
 * in Flecs multi-threaded systems.
 *
 * SCENARIO:
 *   - A system is marked multi_threaded.
 *   - EcsWorldMeasureSystemTime is enabled (world->flags & EcsWorldMeasureSystemTime).
 *   - The pipeline dispatches N worker threads to run the same system.
 *   - After each worker finishes iterating, it executes:
 *       system_data->time_spent += (ecs_ftime_t)ecs_time_measure(&time_start);
 *     (system.c:146)
 *
 * BUG:
 *   `system_data` is the SAME ecs_system_t struct for all workers.
 *   `time_spent +=` is a non-atomic read-modify-write on a shared float.
 *   Two workers can:
 *     1. Both read the current time_spent (e.g., 0.0)
 *     2. Both compute 0.0 + their_delta
 *     3. Both write back — second write overwrites the first
 *   Result: one worker's time measurement is silently lost.
 *
 *   This is NOT protected by FLECS_ACCURATE_COUNTERS (which only covers
 *   integer counters like systems_ran_total via ecs_os_linc).
 *   There is no opt-in fix for this race.
 *
 * CONTRAST with counter races:
 *   world->info.systems_ran_total uses ecs_os_linc which becomes atomic
 *   with FLECS_ACCURATE_COUNTERS. But time_spent uses plain `+=` on a
 *   float and has no atomic variant.
 *
 * The spec models the += as a 3-step sequence: read, add, write.
 * Under interleaving, a lost-update anomaly is possible.
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Workers,         \* Set of worker thread IDs, e.g. {1, 2}
    NULL             \* Model value

VARIABLES
    timeSpent,       \* The shared system_data->time_spent (integer model of float)
    workerPC,        \* Per-worker program counter
    workerLocal,     \* Per-worker local register (value read from timeSpent)
    workerDelta,     \* Per-worker measured delta time
    phase            \* "running" | "done"

vars == <<timeSpent, workerPC, workerLocal, workerDelta, phase>>

\* Worker program counter states:
\* "idle"     — not started yet
\* "measure"  — called ecs_time_measure, has delta, about to do +=
\* "read"     — read current timeSpent into local register
\* "write"    — computed local + delta, about to write back
\* "done"     — finished
WorkerPCs == {"idle", "measure", "read", "write", "done"}

------------------------------------------------------------------------
\* Initialization
\* Each worker will measure some delta time. We use distinct small integers
\* to make lost updates detectable.
------------------------------------------------------------------------

Init ==
    /\ timeSpent = 0
    /\ workerPC = [w \in Workers |-> "idle"]
    /\ workerLocal = [w \in Workers |-> 0]
    /\ workerDelta = [w \in Workers |-> w]  \* Worker i measures delta = i
    /\ phase = "running"

------------------------------------------------------------------------
\* Worker execution
\* Models the system callback finishing and reaching line 146
------------------------------------------------------------------------

\* Worker finishes iteration, calls ecs_time_measure to get delta
WorkerMeasure(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "idle"
    /\ workerPC' = [workerPC EXCEPT ![w] = "measure"]
    /\ UNCHANGED <<timeSpent, workerLocal, workerDelta, phase>>

\* Worker reads current timeSpent (the "read" part of +=)
WorkerRead(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "measure"
    /\ workerLocal' = [workerLocal EXCEPT ![w] = timeSpent]  \* Read shared state
    /\ workerPC' = [workerPC EXCEPT ![w] = "read"]
    /\ UNCHANGED <<timeSpent, workerDelta, phase>>

\* Worker writes back local + delta (the "write" part of +=)
WorkerWrite(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "read"
    /\ timeSpent' = workerLocal[w] + workerDelta[w]  \* Write to shared state
    /\ workerPC' = [workerPC EXCEPT ![w] = "write"]
    /\ UNCHANGED <<workerLocal, workerDelta, phase>>

\* Worker done
WorkerDone(w) ==
    /\ phase = "running"
    /\ workerPC[w] = "write"
    /\ workerPC' = [workerPC EXCEPT ![w] = "done"]
    /\ UNCHANGED <<timeSpent, workerLocal, workerDelta, phase>>

\* All workers done => system run complete
Finish ==
    /\ phase = "running"
    /\ \A w \in Workers : workerPC[w] = "done"
    /\ phase' = "done"
    /\ UNCHANGED <<timeSpent, workerPC, workerLocal, workerDelta>>

------------------------------------------------------------------------
\* Next-state relation
------------------------------------------------------------------------

Next ==
    \/ \E w \in Workers :
        \/ WorkerMeasure(w)
        \/ WorkerRead(w)
        \/ WorkerWrite(w)
        \/ WorkerDone(w)
    \/ Finish

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
\* INVARIANTS
------------------------------------------------------------------------

\* The expected correct value of timeSpent when all workers are done
\* is the sum of all deltas: Sum({w : w \in Workers})
ExpectedTotal == LET S == {w : w \in Workers}
                 IN  \* For Workers = {1,2}: expected = 1 + 2 = 3
                     \* For Workers = {1,2,3}: expected = 1 + 2 + 3 = 6
                     \* General sum using CHOOSE-based recursive sum
                     LET RECURSIVE SumSet(_)
                         SumSet(ss) == IF ss = {} THEN 0
                                       ELSE LET x == CHOOSE x \in ss : TRUE
                                            IN  x + SumSet(ss \ {x})
                     IN SumSet(S)

\* NoLostUpdate:
\* When all workers are done, timeSpent should equal the sum of all deltas.
\* This invariant WILL BE VIOLATED when interleaving causes a lost update.
NoLostUpdate ==
    phase = "done" => timeSpent = ExpectedTotal

\* TypeOK
TypeOK ==
    /\ timeSpent \in Nat
    /\ workerPC \in [Workers -> WorkerPCs]
    /\ workerLocal \in [Workers -> Nat]
    /\ phase \in {"running", "done"}

\* LostUpdateWitness:
\* When violated, this shows the exact amount of loss
LostUpdateAmount ==
    phase = "done" => timeSpent >= ExpectedTotal

========================================================================

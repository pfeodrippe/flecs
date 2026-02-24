--------------------------- MODULE EnsureDirectWrite ---------------------------
(*
 * Models the ecs_ensure() direct-write race in Flecs.
 *
 * SCENARIO:
 *   - A multi-threaded system queries [inout] Position.
 *   - The pipeline assigns disjoint entity slices to each worker (safe for
 *     iterated entities).
 *   - Inside the system callback, worker code calls
 *       ecs_ensure(it->world, singleton, Velocity)
 *     where `singleton` is NOT in the iteration set (e.g., a shared config
 *     entity that already has the Velocity component).
 *
 * BUG:
 *   flecs_defer_ensure (commands.c:399-459) calls flecs_defer_get_existing
 *   which returns a raw pointer into the live component table when the entity
 *   already has the component. Unlike flecs_defer_set (commands.c:481-486),
 *   there is NO `if (world->stage_count != 1) { ptr.ptr = NULL; }` guard.
 *
 *   Both workers receive the SAME raw pointer and write to it concurrently.
 *   This is a data race on the component storage.
 *
 *   The same missing guard affects flecs_defer_cpp_set and
 *   flecs_defer_cpp_assign.
 *
 * CONTRAST with flecs_defer_set:
 *   flecs_defer_set detects stage_count != 1 and forces ptr.ptr = NULL,
 *   which causes the value to be copied into per-stage temporary storage.
 *   The merge phase then applies the writes sequentially. This is safe.
 *
 * This spec models both the buggy ecs_ensure path and the correct ecs_set
 * path side by side, and checks that:
 *   - INVARIANT DataRaceDetected: no two workers hold a raw pointer to the
 *     same live component simultaneously (violated by ecs_ensure, not by
 *     ecs_set)
 *   - INVARIANT ComponentIntegrity: the final component value is one of the
 *     values written by a worker, not a torn/mixed value
 *)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Workers,         \* Set of worker thread IDs, e.g. {w1, w2}
    NULL             \* Model value for "no pointer"

VARIABLES
    \* --- Shared world state ---
    componentValue,      \* The live Velocity component on the singleton.
                         \* An integer representing the stored value.

    \* --- Per-worker state ---
    workerPC,            \* Program counter for each worker
    workerPtr,           \* Pointer held by each worker (NULL or "raw")
    workerLocalValue,    \* Value each worker intends to write
    workerStageCmd,      \* Per-stage command buffer (for ecs_set path)

    \* --- Global ---
    phase,               \* "running" | "merging" | "done"
    apiPath              \* "ensure" | "set" — which code path we're testing

vars == <<componentValue, workerPC, workerPtr, workerLocalValue,
          workerStageCmd, phase, apiPath>>

\* Worker program counter states:
\* "idle"        — waiting to start
\* "called"      — called ecs_ensure/ecs_set, obtained pointer
\* "writing"     — writing through the pointer (or into stage buffer)
\* "done"        — finished

WorkerPCs == {"idle", "called", "writing", "done"}
Phases == {"running", "merging", "done"}
Paths == {"ensure", "set"}

------------------------------------------------------------------------
\* Initialization
\* We model a single singleton entity that already has the Velocity component
\* with an initial value of 0. Each worker will try to write its own value.
------------------------------------------------------------------------

Init ==
    /\ componentValue = 0
    /\ workerPC = [w \in Workers |-> "idle"]
    /\ workerPtr = [w \in Workers |-> NULL]
    /\ workerLocalValue = [w \in Workers |-> 0]
    /\ workerStageCmd = [w \in Workers |-> NULL]
    /\ phase = "running"
    /\ apiPath \in Paths   \* nondeterministic choice

------------------------------------------------------------------------
\* Worker calls ecs_ensure on the singleton (BUGGY PATH)
\*
\* flecs_defer_ensure returns the raw pointer to componentValue
\* because the entity already has the component and there is no
\* stage_count guard.
------------------------------------------------------------------------

EnsureCall(w) ==
    /\ phase = "running"
    /\ apiPath = "ensure"
    /\ workerPC[w] = "idle"
    /\ workerPC' = [workerPC EXCEPT ![w] = "called"]
    /\ workerPtr' = [workerPtr EXCEPT ![w] = "raw"]  \* raw pointer to live data!
    /\ workerLocalValue' = [workerLocalValue EXCEPT ![w] = w]  \* each worker writes its ID
    /\ UNCHANGED <<componentValue, workerStageCmd, phase, apiPath>>

\* Worker writes through the raw pointer — directly mutates componentValue
EnsureWrite(w) ==
    /\ phase = "running"
    /\ apiPath = "ensure"
    /\ workerPC[w] = "called"
    /\ workerPtr[w] = "raw"
    /\ componentValue' = workerLocalValue[w]  \* direct write to shared state!
    /\ workerPC' = [workerPC EXCEPT ![w] = "writing"]
    /\ UNCHANGED <<workerPtr, workerLocalValue, workerStageCmd, phase, apiPath>>

\* Worker finishes (releases pointer conceptually)
EnsureFinish(w) ==
    /\ phase = "running"
    /\ apiPath = "ensure"
    /\ workerPC[w] = "writing"
    /\ workerPC' = [workerPC EXCEPT ![w] = "done"]
    /\ workerPtr' = [workerPtr EXCEPT ![w] = NULL]
    /\ UNCHANGED <<componentValue, workerLocalValue, workerStageCmd, phase, apiPath>>

------------------------------------------------------------------------
\* Worker calls ecs_set on the singleton (CORRECT PATH)
\*
\* flecs_defer_set detects stage_count != 1, forces ptr.ptr = NULL,
\* and copies the value into per-stage temporary storage.
------------------------------------------------------------------------

SetCall(w) ==
    /\ phase = "running"
    /\ apiPath = "set"
    /\ workerPC[w] = "idle"
    /\ workerPC' = [workerPC EXCEPT ![w] = "called"]
    /\ workerPtr' = [workerPtr EXCEPT ![w] = NULL]  \* ptr forced to NULL by guard!
    /\ workerLocalValue' = [workerLocalValue EXCEPT ![w] = w]
    /\ UNCHANGED <<componentValue, workerStageCmd, phase, apiPath>>

\* Worker writes into per-stage buffer (NOT shared state)
SetWrite(w) ==
    /\ phase = "running"
    /\ apiPath = "set"
    /\ workerPC[w] = "called"
    /\ workerStageCmd' = [workerStageCmd EXCEPT ![w] = workerLocalValue[w]]
    /\ workerPC' = [workerPC EXCEPT ![w] = "writing"]
    /\ UNCHANGED <<componentValue, workerPtr, workerLocalValue, phase, apiPath>>

\* Worker finishes
SetFinish(w) ==
    /\ phase = "running"
    /\ apiPath = "set"
    /\ workerPC[w] = "writing"
    /\ workerPC' = [workerPC EXCEPT ![w] = "done"]
    /\ UNCHANGED <<componentValue, workerPtr, workerLocalValue, workerStageCmd,
                    phase, apiPath>>

------------------------------------------------------------------------
\* Sync barrier + merge phase
\* All workers must be done before merge begins.
------------------------------------------------------------------------

AllWorkersDone == \A w \in Workers : workerPC[w] = "done"

BeginMerge ==
    /\ phase = "running"
    /\ AllWorkersDone
    /\ phase' = "merging"
    /\ UNCHANGED <<componentValue, workerPC, workerPtr, workerLocalValue,
                    workerStageCmd, apiPath>>

\* Merge: apply per-stage commands sequentially (for ecs_set path)
\* For ecs_ensure path, the writes already happened — merge is a no-op
\* (the command was EcsCmdAdd, which just ensures the component exists).
MergeStage(w) ==
    /\ phase = "merging"
    /\ apiPath = "set"
    /\ workerStageCmd[w] # NULL
    /\ componentValue' = workerStageCmd[w]
    /\ workerStageCmd' = [workerStageCmd EXCEPT ![w] = NULL]
    /\ UNCHANGED <<workerPC, workerPtr, workerLocalValue, phase, apiPath>>

MergeEnsureNoop ==
    /\ phase = "merging"
    /\ apiPath = "ensure"
    \* All "commands" from ensure path were EcsCmdAdd (no data), so merge
    \* does nothing to componentValue
    /\ phase' = "done"
    /\ UNCHANGED <<componentValue, workerPC, workerPtr, workerLocalValue,
                    workerStageCmd, apiPath>>

FinishMerge ==
    /\ phase = "merging"
    /\ apiPath = "set"
    /\ \A w \in Workers : workerStageCmd[w] = NULL
    /\ phase' = "done"
    /\ UNCHANGED <<componentValue, workerPC, workerPtr, workerLocalValue,
                    workerStageCmd, apiPath>>

------------------------------------------------------------------------
\* Next-state relation
------------------------------------------------------------------------

Next ==
    \/ \E w \in Workers :
        \/ EnsureCall(w)
        \/ EnsureWrite(w)
        \/ EnsureFinish(w)
        \/ SetCall(w)
        \/ SetWrite(w)
        \/ SetFinish(w)
        \/ MergeStage(w)
    \/ BeginMerge
    \/ MergeEnsureNoop
    \/ FinishMerge

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------
\* INVARIANTS
------------------------------------------------------------------------

\* DataRaceDetected:
\* Two workers should NEVER simultaneously hold a raw pointer to the same
\* live component storage. This invariant will be VIOLATED on the "ensure"
\* path, demonstrating the bug.
NoDataRace ==
    ~(\E w1, w2 \in Workers :
        /\ w1 # w2
        /\ workerPtr[w1] = "raw"
        /\ workerPtr[w2] = "raw")

\* ConcurrentWriteDetected:
\* An even stronger check: two workers should never be in the "writing"
\* state simultaneously while holding raw pointers. This catches the
\* moment of actual concurrent mutation.
NoConcurrentWrite ==
    ~(\E w1, w2 \in Workers :
        /\ w1 # w2
        /\ workerPC[w1] = "writing"
        /\ workerPC[w2] = "writing"
        /\ apiPath = "ensure")

\* ComponentIntegrity:
\* When done, the component value must be one of the worker values or
\* the initial value (0). This is always satisfied in this model but
\* would fail with torn reads/writes at a lower abstraction level.
ComponentIntegrity ==
    phase = "done" =>
        componentValue \in ({0} \union {w : w \in Workers})

\* TypeOK
TypeOK ==
    /\ componentValue \in (Int)
    /\ workerPC \in [Workers -> WorkerPCs]
    /\ workerPtr \in [Workers -> {NULL, "raw"}]
    /\ phase \in Phases
    /\ apiPath \in Paths

========================================================================

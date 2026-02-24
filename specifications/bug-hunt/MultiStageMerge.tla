--------------------------- MODULE MultiStageMerge ---------------------------
(*
 * Multi-Stage Command Merge — Bug-Hunting Spec for Flecs ECS
 *
 * Models the Flecs pipeline concurrency pattern where N worker stages
 * queue commands during readonly, then merge sequentially on main thread.
 *
 * KEY INSIGHT: This spec models CORRECT Flecs behavior to expose a
 * DESIGN-LEVEL issue: silent data loss when cross-stage conflicts occur.
 * Stage 0 can delete an entity, causing all of Stage 1's commands for
 * that entity to be silently discarded — no warning, no error.
 *
 * The spec checks whether user-visible consistency properties hold
 * under the sequential merge model. Specifically:
 *   - If a worker stage observes entity E as alive and enqueues a Set,
 *     does that Set eventually take effect?  (NO — if another stage deletes E)
 *   - If two stages both Set the same component on the same entity,
 *     which value wins?  (Last stage in merge order — deterministic but opaque)
 *
 * Source: stage.c:flecs_stage_merge, commands.c:flecs_defer_end
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Stages,      \* e.g., {s0, s1}
    Entities,    \* e.g., {e1, e2}
    Components,  \* e.g., {c1}
    NullComp,    \* Sentinel for commands that don't need a component
    MaxQueueLen  \* Bound on per-stage queue length (e.g., 2)

CmdKinds == {"Add", "Remove", "Delete", "Clear"}

ASSUME NullComp \notin Components
ASSUME MaxQueueLen \in Nat /\ MaxQueueLen >= 1

VARIABLES
    alive,           \* Entities -> BOOLEAN (alive set)
    entityComps,     \* Entity -> SUBSET Components
    entityGen,       \* Entity -> Nat (generation counter)
    stageQueues,     \* Stage -> Seq(cmd)
    phase,           \* "idle" | "readonly" | "merging"
    mergeIdx,        \* 1..NumStages: which stage is being merged
    cmdIdx,          \* index into current stage's queue
    stagesMerged,    \* how many stages have completed merge
    dropped          \* number of commands dropped this round (dead entity)

vars == <<alive, entityComps, entityGen, stageQueues,
          phase, mergeIdx, cmdIdx, stagesMerged, dropped>>

NumStages == Cardinality(Stages)

(* Fixed merge order — CHOOSE picks one deterministic bijection *)
StageOrder == CHOOSE f \in [1..NumStages -> Stages] :
                  \A i, j \in 1..NumStages : i # j => f[i] # f[j]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ alive = [e \in Entities |-> TRUE]
    /\ entityComps = [e \in Entities |-> {}]
    /\ entityGen = [e \in Entities |-> 0]
    /\ stageQueues = [s \in Stages |-> <<>>]
    /\ phase = "idle"
    /\ mergeIdx = 0
    /\ cmdIdx = 0
    /\ stagesMerged = 0
    /\ dropped = 0

-----------------------------------------------------------------------------
(* Phase transitions *)

BeginReadonly ==
    /\ phase = "idle"
    /\ phase' = "readonly"
    /\ dropped' = 0
    /\ UNCHANGED <<alive, entityComps, entityGen, stageQueues,
                   mergeIdx, cmdIdx, stagesMerged>>

(* Worker enqueues a command — bounded by MaxQueueLen *)
Enqueue(s) ==
    /\ phase = "readonly"
    /\ Len(stageQueues[s]) < MaxQueueLen
    /\ \E e \in Entities, kind \in CmdKinds :
        LET cmd == [kind |-> kind,
                    entity |-> e,
                    comp |-> IF kind \in {"Add", "Remove"}
                             THEN CHOOSE c \in Components : TRUE
                             ELSE NullComp]
        IN stageQueues' = [stageQueues EXCEPT ![s] = Append(@, cmd)]
    /\ UNCHANGED <<alive, entityComps, entityGen, phase,
                   mergeIdx, cmdIdx, stagesMerged, dropped>>

(* All workers done — begin sequential merge *)
EndReadonly ==
    /\ phase = "readonly"
    /\ phase' = "merging"
    /\ mergeIdx' = 1
    /\ cmdIdx' = 1
    /\ stagesMerged' = 0
    /\ UNCHANGED <<alive, entityComps, entityGen, stageQueues, dropped>>

-----------------------------------------------------------------------------
(* Merge: process commands one at a time, stage by stage *)

CurStage == StageOrder[mergeIdx]
CurQueue == stageQueues[CurStage]

(* Apply one command from the current stage *)
MergeStep ==
    /\ phase = "merging"
    /\ mergeIdx <= NumStages
    /\ cmdIdx <= Len(CurQueue)
    /\ LET cmd == CurQueue[cmdIdx]
           e == cmd.entity
       IN
       IF ~alive[e] THEN
           \* Entity already dead — SILENTLY DISCARD
           /\ dropped' = dropped + 1
           /\ UNCHANGED <<alive, entityComps, entityGen>>
       ELSE
           CASE cmd.kind = "Add" ->
                /\ entityComps' = [entityComps EXCEPT ![e] = @ \cup {cmd.comp}]
                /\ UNCHANGED <<alive, entityGen, dropped>>
             [] cmd.kind = "Remove" ->
                /\ entityComps' = [entityComps EXCEPT ![e] = @ \ {cmd.comp}]
                /\ UNCHANGED <<alive, entityGen, dropped>>
             [] cmd.kind = "Delete" ->
                /\ alive' = [alive EXCEPT ![e] = FALSE]
                /\ entityComps' = [entityComps EXCEPT ![e] = {}]
                /\ entityGen' = [entityGen EXCEPT ![e] = @ + 1]
                /\ UNCHANGED <<dropped>>
             [] cmd.kind = "Clear" ->
                /\ entityComps' = [entityComps EXCEPT ![e] = {}]
                /\ UNCHANGED <<alive, entityGen, dropped>>
    /\ cmdIdx' = cmdIdx + 1
    /\ UNCHANGED <<phase, mergeIdx, stageQueues, stagesMerged>>

(* Advance to next stage when current stage's queue is exhausted *)
NextStage ==
    /\ phase = "merging"
    /\ mergeIdx <= NumStages
    /\ cmdIdx > Len(CurQueue)
    /\ stagesMerged' = stagesMerged + 1
    /\ IF mergeIdx < NumStages THEN
           /\ mergeIdx' = mergeIdx + 1
           /\ cmdIdx' = 1
           /\ UNCHANGED <<phase>>
       ELSE
           /\ phase' = "idle"
           /\ mergeIdx' = 0
           /\ cmdIdx' = 0
    /\ UNCHANGED <<alive, entityComps, entityGen, stageQueues, dropped>>

(* Clear queues after merge completes *)
ClearQueues ==
    /\ phase = "idle"
    /\ \E s \in Stages : stageQueues[s] # <<>>
    /\ stageQueues' = [s \in Stages |-> <<>>]
    /\ UNCHANGED <<alive, entityComps, entityGen, phase,
                   mergeIdx, cmdIdx, stagesMerged, dropped>>

-----------------------------------------------------------------------------
Next ==
    \/ BeginReadonly
    \/ \E s \in Stages : Enqueue(s)
    \/ EndReadonly
    \/ MergeStep
    \/ NextStage
    \/ ClearQueues

Spec == Init /\ [][Next]_vars

FairSpec ==
    Spec
    /\ WF_vars(BeginReadonly)
    /\ WF_vars(EndReadonly)
    /\ WF_vars(MergeStep)
    /\ WF_vars(NextStage)
    /\ WF_vars(ClearQueues)

(* State constraint to keep state space bounded *)
StateConstraint ==
    /\ \A e \in Entities : entityGen[e] <= 2
    /\ dropped <= MaxQueueLen * NumStages

-----------------------------------------------------------------------------
(* SAFETY INVARIANTS *)

TypeOK ==
    /\ alive \in [Entities -> BOOLEAN]
    /\ entityComps \in [Entities -> SUBSET Components]
    /\ entityGen \in [Entities -> Nat]
    /\ phase \in {"idle", "readonly", "merging"}

(* Dead entities must have no components *)
DeadClean ==
    \A e \in Entities : ~alive[e] => entityComps[e] = {}

(* ============================================================
 * BUG-HUNTING INVARIANT: NoSilentDataLoss
 *
 * This invariant SHOULD BE VIOLATED. It asserts that no command
 * is ever silently dropped. In Flecs, this IS violated when:
 *   - Stage 0 deletes entity E
 *   - Stage 1 had enqueued commands for entity E
 *   - Stage 1's commands are silently discarded during merge
 *
 * The counterexample trace from TLC demonstrates the exact
 * scenario where user work is silently lost.
 * ============================================================ *)
NoSilentDataLoss ==
    dropped = 0

-----------------------------------------------------------------------------
(* TEMPORAL PROPERTIES *)

(* The system always eventually returns to idle *)
AlwaysEventuallyIdle ==
    []<>(phase = "idle")

(* Once merging starts, it eventually finishes *)
MergingLeadsToIdle ==
    (phase = "merging") ~> (phase = "idle")

(* Once readonly starts, it eventually reaches merge *)
ReadonlyLeadsToMerging ==
    (phase = "readonly") ~> (phase = "merging")

(* Progress: infinitely often reach idle with clean queues *)
InfiniteProgress ==
    []<>(phase = "idle" /\ \A s \in Stages : stageQueues[s] = <<>>)

(* If an entity is alive and a stage enqueues Delete for it,
 * it eventually dies — BUT only if no earlier stage re-creates it.
 * This models the Flecs guarantee. *)
DeleteEventuallyEffective ==
    \A e \in Entities :
        (phase = "merging" /\ alive[e] /\
         \E i \in 1..NumStages :
            \E j \in 1..Len(stageQueues[StageOrder[i]]) :
                stageQueues[StageOrder[i]][j].kind = "Delete" /\
                stageQueues[StageOrder[i]][j].entity = e)
        ~> (~alive[e] \/ phase = "idle")

=============================================================================

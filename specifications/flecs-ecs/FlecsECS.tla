------------------------------- MODULE FlecsECS --------------------------------
\* TLA+ specification of the Flecs Entity Component System core
\*
\* Scope: Entity lifecycle, component/table management, deferred commands,
\*        cleanup traits (OnDelete policies)
\* Excludes: Query engine, observers/hooks, pipeline scheduling, IsA traversal,
\*           threading (single-stage only)
\*
\* Key domain concepts modeled:
\*   - Entities have a lifecycle: absent -> alive -> dead (recyclable)
\*   - Each alive entity lives in exactly one archetype table (set of components)
\*   - Adding/removing components moves entities between tables
\*   - Operations can be deferred (queued) and flushed later
\*   - Deleting entities used as components triggers cleanup policies

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Entities,       \* Universe of entity IDs
          Components,     \* Universe of component IDs (also entities)
          MaxGeneration,  \* Upper bound on generation counter for model checking
          MaxDefer,       \* Max defer nesting depth
          MaxQueueLen     \* Max command queue length

\* Cleanup policies for when an entity used as a component is deleted
CleanupPolicies == {"remove", "delete", "panic"}

\* Entity lifecycle states
EntityStates == {"absent", "alive", "dead"}

\* Command types for deferred operations
CmdKinds == {"add", "remove", "delete", "clear"}

VARIABLES
    entityState,      \* Entity lifecycle: Entities -> EntityStates
    generation,       \* Generation counter: Entities -> Nat (for safe recycling)
    entityComponents, \* Component set per entity: Entities -> SUBSET Components
    cleanupPolicy,    \* Cleanup policy per component: Components -> CleanupPolicies
    deferDepth,       \* Defer nesting counter: Nat (0 = direct mode, >0 = deferred)
    cmdQueue,         \* Deferred command queue: Seq(Command)
    flushing          \* Whether currently flushing commands: BOOLEAN

vars == << entityState, generation, entityComponents,
           cleanupPolicy, deferDepth, cmdQueue, flushing >>

-----------------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ entityState \in [Entities -> EntityStates]
    /\ generation \in [Entities -> 0..MaxGeneration]
    /\ entityComponents \in [Entities -> SUBSET Components]
    /\ cleanupPolicy \in [Components -> CleanupPolicies]
    /\ deferDepth \in 0..MaxDefer
    /\ cmdQueue \in Seq([kind : CmdKinds, entity : Entities, component : Components \union {"none"}])
    /\ Len(cmdQueue) <= MaxQueueLen
    /\ flushing \in BOOLEAN

\* An entity is alive iff its state is "alive"
IsAlive(e) == entityState[e] = "alive"

\* An entity is dead iff its state is "dead"
IsDead(e) == entityState[e] = "dead"

\* An entity has never existed or was fully recycled back to absent
IsAbsent(e) == entityState[e] = "absent"

\* The archetype "table" for an entity is its component set
\* Two entities with identical component sets are in the same table
TableOf(e) == entityComponents[e]

\* Direct mode: operations apply immediately
DirectMode == deferDepth = 0 /\ ~flushing

\* Deferred mode: operations are queued
DeferredMode == deferDepth > 0

\* All alive entities
AliveEntities == {e \in Entities : IsAlive(e)}

\* All entities that have a specific component
EntitiesWithComponent(c) == {e \in AliveEntities : c \in entityComponents[e]}

-----------------------------------------------------------------------------
\* Safety invariants

\* Dead entities must have empty component sets (cleared on death)
DeadEntitiesHaveNoComponents ==
    \A e \in Entities : IsDead(e) => entityComponents[e] = {}

\* Absent entities must have empty component sets
AbsentEntitiesHaveNoComponents ==
    \A e \in Entities : IsAbsent(e) => entityComponents[e] = {}

\* Generation only increases (checked across transitions via the spec)
\* Modeled as: dead entities have generation > 0 (they were alive at least once)
DeadEntitiesHavePositiveGeneration ==
    \A e \in Entities : IsDead(e) => generation[e] > 0

\* No commands in queue reference absent entities (commands are for alive or
\* recently-alive entities; absent means never created in this generation)
\* Note: commands referencing dead entities are valid (discarded at flush)

\* Components in entity component sets must be from the Components constant
ComponentsAreValid ==
    \A e \in Entities : entityComponents[e] \subseteq Components

\* Not flushing when defer depth > 0
FlushOnlyAtZeroDefer ==
    flushing => deferDepth = 0

-----------------------------------------------------------------------------
\* Initial state: all entities absent, no components, no defer, empty queue

Init ==
    /\ entityState = [e \in Entities |-> "absent"]
    /\ generation = [e \in Entities |-> 0]
    /\ entityComponents = [e \in Entities |-> {}]
    /\ cleanupPolicy = [c \in Components |-> "remove"]
    /\ deferDepth = 0
    /\ cmdQueue = << >>
    /\ flushing = FALSE

-----------------------------------------------------------------------------
\* Actions

\* --- Entity Creation ---
\* Create a new entity (from absent state)
CreateEntity ==
    \E e \in Entities :
        /\ IsAbsent(e)
        /\ ~flushing
        /\ entityState' = [entityState EXCEPT ![e] = "alive"]
        /\ UNCHANGED << generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* Recycle a dead entity (reuse its ID with the already-bumped generation)
RecycleEntity ==
    \E e \in Entities :
        /\ IsDead(e)
        /\ ~flushing
        /\ entityState' = [entityState EXCEPT ![e] = "alive"]
        /\ UNCHANGED << generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Component Operations (Direct Mode) ---
\* Add a component to an alive entity (direct mode)
AddComponentDirect ==
    \E e \in Entities, c \in Components :
        /\ DirectMode
        /\ IsAlive(e)
        /\ c \notin entityComponents[e]
        /\ entityComponents' = [entityComponents EXCEPT ![e] = @ \union {c}]
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* Remove a component from an alive entity (direct mode)
RemoveComponentDirect ==
    \E e \in Entities, c \in Components :
        /\ DirectMode
        /\ IsAlive(e)
        /\ c \in entityComponents[e]
        /\ entityComponents' = [entityComponents EXCEPT ![e] = @ \ {c}]
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Delete Entity (Direct Mode) ---
\* Delete an entity: clear its components, mark as dead, bump generation
\* This is the simple case without cleanup policy cascade
DeleteEntityDirect ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ generation[e] < MaxGeneration
        \* Check no alive entity uses this entity as a component with "panic" policy
        /\ ~(\E c \in Components : c = e /\ cleanupPolicy[c] = "panic"
              /\ \E other \in AliveEntities : c \in entityComponents[other])
        /\ entityState' = [entityState EXCEPT ![e] = "dead"]
        /\ entityComponents' = [entityComponents EXCEPT ![e] = {}]
        /\ generation' = [generation EXCEPT ![e] = @ + 1]
        /\ UNCHANGED << cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Clear Entity (Direct Mode) ---
\* Remove all components from an entity but keep it alive
ClearEntityDirect ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ entityComponents[e] # {}
        /\ entityComponents' = [entityComponents EXCEPT ![e] = {}]
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Cleanup Policy: OnDelete Remove ---
\* When a component entity is deleted, remove that component from all entities
\* that have it (if the policy is "remove")
DeleteEntityWithRemovePolicy ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ e \in Components
        /\ cleanupPolicy[e] = "remove"
        /\ generation[e] < MaxGeneration
        /\ entityState' = [entityState EXCEPT ![e] = "dead"]
        /\ entityComponents' = [ent \in Entities |->
            IF ent = e THEN {}
            ELSE entityComponents[ent] \ {e}]
        /\ generation' = [generation EXCEPT ![e] = @ + 1]
        /\ UNCHANGED << cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Cleanup Policy: OnDelete Delete ---
\* When a component entity is deleted, delete all entities that have it
DeleteEntityWithDeletePolicy ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ e \in Components
        /\ cleanupPolicy[e] = "delete"
        /\ LET victims == {ent \in AliveEntities : e \in entityComponents[ent]}
               allDying == victims \union {e}
           IN
           \* All dying entities need generation headroom
           /\ \A d \in allDying : generation[d] < MaxGeneration
           /\ entityState' = [ent \in Entities |->
               IF ent \in allDying THEN "dead"
               ELSE entityState[ent]]
           /\ entityComponents' = [ent \in Entities |->
               IF ent \in allDying THEN {}
               ELSE entityComponents[ent]]
           /\ generation' = [ent \in Entities |->
               IF ent \in allDying THEN generation[ent] + 1
               ELSE generation[ent]]
        /\ UNCHANGED << cleanupPolicy,
                        deferDepth, cmdQueue, flushing >>

\* --- Set Cleanup Policy ---
\* Configure the cleanup policy for a component
SetCleanupPolicy ==
    \E c \in Components, policy \in CleanupPolicies :
        /\ ~flushing
        /\ cleanupPolicy[c] # policy
        /\ cleanupPolicy' = [cleanupPolicy EXCEPT ![c] = policy]
        /\ UNCHANGED << entityState, generation, entityComponents,
                        deferDepth, cmdQueue, flushing >>

\* --- Deferred Operations ---

\* Begin deferring: increment defer counter
DeferBegin ==
    /\ deferDepth < MaxDefer
    /\ ~flushing
    /\ deferDepth' = deferDepth + 1
    /\ UNCHANGED << entityState, generation, entityComponents,
                    cleanupPolicy, cmdQueue, flushing >>

\* Enqueue an Add command (deferred mode)
AddComponentDeferred ==
    \E e \in Entities, c \in Components :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "add", entity |-> e, component |-> c])
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing >>

\* Enqueue a Remove command (deferred mode)
RemoveComponentDeferred ==
    \E e \in Entities, c \in Components :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "remove", entity |-> e, component |-> c])
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing >>

\* Enqueue a Delete command (deferred mode)
DeleteEntityDeferred ==
    \E e \in Entities :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "delete", entity |-> e, component |-> "none"])
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing >>

\* Enqueue a Clear command (deferred mode)
ClearEntityDeferred ==
    \E e \in Entities :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "clear", entity |-> e, component |-> "none"])
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing >>

\* --- Command Flush ---

\* Apply a single command to the world state
\* Returns the new state as a record. We model this as a recursive operator.
ApplyCmd(cmd, es, ec, gen) ==
    IF ~(es[cmd.entity] = "alive") THEN
        \* Entity is dead or absent: discard command
        [entityState |-> es, entityComponents |-> ec, generation |-> gen]
    ELSE
        CASE cmd.kind = "add" ->
            [entityState |-> es,
             entityComponents |-> [ec EXCEPT ![cmd.entity] = @ \union {cmd.component}],
             generation |-> gen]
        [] cmd.kind = "remove" ->
            [entityState |-> es,
             entityComponents |-> [ec EXCEPT ![cmd.entity] = @ \ {cmd.component}],
             generation |-> gen]
        [] cmd.kind = "delete" ->
            IF gen[cmd.entity] < MaxGeneration THEN
                [entityState |-> [es EXCEPT ![cmd.entity] = "dead"],
                 entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
                 generation |-> [gen EXCEPT ![cmd.entity] = @ + 1]]
            ELSE
                \* At max generation, still delete but cap generation
                [entityState |-> [es EXCEPT ![cmd.entity] = "dead"],
                 entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
                 generation |-> gen]
        [] cmd.kind = "clear" ->
            [entityState |-> es,
             entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
             generation |-> gen]

\* Flush: apply all queued commands sequentially, then clear queue
\* This models the core flush semantics: commands execute in order,
\* dead entity commands are discarded, and the queue drains completely.
RECURSIVE ApplyAllCmds(_, _, _, _)
ApplyAllCmds(queue, es, ec, gen) ==
    IF queue = << >> THEN [entityState |-> es, entityComponents |-> ec, generation |-> gen]
    ELSE
        LET result == ApplyCmd(Head(queue), es, ec, gen)
        IN ApplyAllCmds(Tail(queue), result.entityState, result.entityComponents, result.generation)

DeferEnd ==
    /\ deferDepth = 1  \* Outermost defer_end triggers flush
    /\ ~flushing
    /\ LET result == ApplyAllCmds(cmdQueue, entityState, entityComponents, generation)
       IN
        /\ entityState' = result.entityState
        /\ entityComponents' = result.entityComponents
        /\ generation' = result.generation
    /\ deferDepth' = 0
    /\ cmdQueue' = << >>
    /\ flushing' = FALSE
    /\ UNCHANGED << cleanupPolicy >>

\* Decrement defer depth without flushing (nested defer_end)
DeferEndNested ==
    /\ deferDepth > 1
    /\ deferDepth' = deferDepth - 1
    /\ UNCHANGED << entityState, generation, entityComponents,
                    cleanupPolicy, cmdQueue, flushing >>

-----------------------------------------------------------------------------
\* Next-state relation

Next ==
    \* Entity lifecycle
    \/ CreateEntity
    \/ RecycleEntity
    \* Direct-mode component operations
    \/ AddComponentDirect
    \/ RemoveComponentDirect
    \/ ClearEntityDirect
    \* Direct-mode delete (simple + policy variants)
    \/ DeleteEntityDirect
    \/ DeleteEntityWithRemovePolicy
    \/ DeleteEntityWithDeletePolicy
    \* Cleanup policy configuration
    \/ SetCleanupPolicy
    \* Defer system
    \/ DeferBegin
    \/ AddComponentDeferred
    \/ RemoveComponentDeferred
    \/ DeleteEntityDeferred
    \/ ClearEntityDeferred
    \/ DeferEnd
    \/ DeferEndNested

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Liveness specification (with fairness)

FairSpec ==
    Spec
    /\ WF_vars(DeferEnd)
    /\ WF_vars(DeferEndNested)

\* If defer begins, it eventually ends (queue eventually flushes)
DeferEventuallyEnds ==
    [](deferDepth > 0 ~> deferDepth = 0)

=============================================================================

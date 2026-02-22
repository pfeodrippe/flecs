------------------------------- MODULE FlecsECS --------------------------------
\* TLA+ specification of the Flecs Entity Component System core
\*
\* Scope: Entity lifecycle, component/table management, deferred commands,
\*        cleanup traits (OnDelete policies), observer/hook event system
\* Excludes: Query engine, pipeline scheduling, IsA traversal,
\*           threading (single-stage only), pair/relationship encoding
\*
\* Key domain concepts modeled:
\*   - Entities have a lifecycle: absent -> alive -> dead (recyclable)
\*   - Each alive entity lives in exactly one archetype table (set of components)
\*   - Adding/removing components moves entities between tables
\*   - Operations can be deferred (queued) and flushed later
\*   - Deleting entities used as components triggers cleanup policies
\*   - Observers watch for OnAdd/OnRemove/OnSet events on specific components
\*   - Hooks fire in a defined order relative to observers:
\*       Add:    hook(on_add) -> observer(OnAdd) -> hook(on_set) -> observer(OnSet)
\*       Remove: observer(OnRemove) -> hook(on_remove)
\*   - Observer callbacks run with deferring active; their mutations queue as commands

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

\* Event kinds emitted by the system
\* hook_on_add:    component lifecycle hook, fires FIRST on add
\* obs_on_add:     observer notification, fires AFTER hook_on_add
\* hook_on_set:    component lifecycle hook, fires after obs_on_add (for valued components)
\* obs_on_set:     observer notification, fires AFTER hook_on_set
\* obs_on_remove:  observer notification, fires FIRST on remove
\* hook_on_remove: component lifecycle hook, fires AFTER obs_on_remove
EventKinds == {"hook_on_add", "obs_on_add", "hook_on_set", "obs_on_set",
               "obs_on_remove", "hook_on_remove"}

VARIABLES
    entityState,      \* Entity lifecycle: Entities -> EntityStates
    generation,       \* Generation counter: Entities -> Nat (for safe recycling)
    entityComponents, \* Component set per entity: Entities -> SUBSET Components
    cleanupPolicy,    \* Cleanup policy per component: Components -> CleanupPolicies
    deferDepth,       \* Defer nesting counter: Nat (0 = direct mode, >0 = deferred)
    cmdQueue,         \* Deferred command queue: Seq(Command)
    flushing,         \* Whether currently flushing commands: BOOLEAN
    \* --- Observer/Hook variables ---
    observers,        \* Set of active observers: SUBSET [event: EventKinds, component: Components]
    hookEnabled,      \* Which components have hooks registered: Components -> BOOLEAN
    lastEventBatch    \* Events from the most recent operation: Seq(EventRecord)

vars == << entityState, generation, entityComponents,
           cleanupPolicy, deferDepth, cmdQueue, flushing,
           observers, hookEnabled, lastEventBatch >>

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
    /\ observers \subseteq [event : {"obs_on_add", "obs_on_remove", "obs_on_set"}, component : Components]
    /\ hookEnabled \in [Components -> BOOLEAN]
    \* lastEventBatch is a sequence of event records
    /\ \A i \in 1..Len(lastEventBatch) :
        /\ lastEventBatch[i].kind \in EventKinds
        /\ lastEventBatch[i].entity \in Entities
        /\ lastEventBatch[i].component \in Components

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
\* Event emission helpers

\* Generate the event trace for adding a component c to entity e.
\* Order: hook_on_add -> obs_on_add -> hook_on_set -> obs_on_set
\* Hooks only fire if hookEnabled[c] = TRUE
\* Observers only fire if a matching observer is registered
AddEvents(e, c) ==
    LET hookAdd    == IF hookEnabled[c]
                      THEN << [kind |-> "hook_on_add", entity |-> e, component |-> c] >>
                      ELSE << >>
        obsAdd     == IF \E obs \in observers : obs.event = "obs_on_add" /\ obs.component = c
                      THEN << [kind |-> "obs_on_add", entity |-> e, component |-> c] >>
                      ELSE << >>
        hookSet    == IF hookEnabled[c]
                      THEN << [kind |-> "hook_on_set", entity |-> e, component |-> c] >>
                      ELSE << >>
        obsSet     == IF \E obs \in observers : obs.event = "obs_on_set" /\ obs.component = c
                      THEN << [kind |-> "obs_on_set", entity |-> e, component |-> c] >>
                      ELSE << >>
    IN hookAdd \o obsAdd \o hookSet \o obsSet

\* Generate the event trace for removing a component c from entity e.
\* Order: obs_on_remove -> hook_on_remove
RemoveEvents(e, c) ==
    LET obsRemove  == IF \E obs \in observers : obs.event = "obs_on_remove" /\ obs.component = c
                      THEN << [kind |-> "obs_on_remove", entity |-> e, component |-> c] >>
                      ELSE << >>
        hookRemove == IF hookEnabled[c]
                      THEN << [kind |-> "hook_on_remove", entity |-> e, component |-> c] >>
                      ELSE << >>
    IN obsRemove \o hookRemove

\* Generate events for removing ALL components from an entity (clear/delete).
\* Each component fires its own remove events.
RECURSIVE RemoveAllEvents(_, _)
RemoveAllEvents(e, comps) ==
    IF comps = {} THEN << >>
    ELSE
        LET c == CHOOSE x \in comps : TRUE
        IN RemoveEvents(e, c) \o RemoveAllEvents(e, comps \ {c})

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

\* Components in entity component sets must be from the Components constant
ComponentsAreValid ==
    \A e \in Entities : entityComponents[e] \subseteq Components

\* Not flushing when defer depth > 0
FlushOnlyAtZeroDefer ==
    flushing => deferDepth = 0

\* --- Observer/Hook event correctness invariants ---
\*
\* The lastEventBatch captures all events emitted by the most recent step.
\* We verify semantic correctness properties about when events fire.

\* Observer events only fire when a matching observer is registered.
\* If obs_on_add/obs_on_remove/obs_on_set appears in the batch, there must
\* be a corresponding observer.
ObserverEventsRequireRegistration ==
    \A i \in 1..Len(lastEventBatch) :
        LET evt == lastEventBatch[i] IN
        \/ evt.kind \notin {"obs_on_add", "obs_on_remove", "obs_on_set"}
        \/ \E obs \in observers : obs.event = evt.kind /\ obs.component = evt.component

\* Hook events only fire when hooks are enabled for the component.
HookEventsRequireEnabled ==
    \A i \in 1..Len(lastEventBatch) :
        LET evt == lastEventBatch[i] IN
        \/ evt.kind \notin {"hook_on_add", "hook_on_remove", "hook_on_set"}
        \/ hookEnabled[evt.component] = TRUE

\* Within the lastEventBatch, events from a single AddEvents(e,c) call
\* are emitted in order: hook_on_add -> obs_on_add -> hook_on_set -> obs_on_set.
\* Events from a single RemoveEvents(e,c) call are in order:
\*   obs_on_remove -> hook_on_remove.
\*
\* Since AddEvents and RemoveEvents produce events in order by construction,
\* and commands are applied sequentially (batch = cmd1_events ++ cmd2_events ++ ...),
\* the ordering within each per-command sub-batch is guaranteed by construction.
\*
\* We verify this with a weaker but still useful invariant: for adjacent events
\* in the batch for the same (entity, component), certain "impossible" transitions
\* never occur. These are transitions that would violate the per-operation ordering.

\* obs_on_add can never immediately precede hook_on_add for the same (e,c)
\* (because hook fires before observer in an add operation)
NoReversedAddHookObserver ==
    \A i \in 1..(Len(lastEventBatch) - 1) :
        ~(/\ lastEventBatch[i].kind = "obs_on_add"
          /\ lastEventBatch[i+1].kind = "hook_on_add"
          /\ lastEventBatch[i].entity = lastEventBatch[i+1].entity
          /\ lastEventBatch[i].component = lastEventBatch[i+1].component)

\* hook_on_remove can never immediately precede obs_on_remove for the same (e,c)
\* (because observer fires before hook in a remove operation)
NoReversedRemoveObserverHook ==
    \A i \in 1..(Len(lastEventBatch) - 1) :
        ~(/\ lastEventBatch[i].kind = "hook_on_remove"
          /\ lastEventBatch[i+1].kind = "obs_on_remove"
          /\ lastEventBatch[i].entity = lastEventBatch[i+1].entity
          /\ lastEventBatch[i].component = lastEventBatch[i+1].component)

\* obs_on_set can never immediately precede hook_on_set for the same (e,c)
\* (because hook_on_set fires before obs_on_set)
NoReversedSetHookObserver ==
    \A i \in 1..(Len(lastEventBatch) - 1) :
        ~(/\ lastEventBatch[i].kind = "obs_on_set"
          /\ lastEventBatch[i+1].kind = "hook_on_set"
          /\ lastEventBatch[i].entity = lastEventBatch[i+1].entity
          /\ lastEventBatch[i].component = lastEventBatch[i+1].component)

\* obs_on_add can never immediately precede hook_on_set for the same (e,c)
\* within the SAME add operation. However, across operations this is fine
\* (e.g. add then remove then add). Since we can't distinguish operation
\* boundaries in the flat batch, we only check the above adjacency constraints.
\* The construction of AddEvents/RemoveEvents provides the stronger guarantee.

-----------------------------------------------------------------------------
\* Initial state: all entities absent, no components, no defer, empty queue,
\*                no observers, no hooks, empty event batch

Init ==
    /\ entityState = [e \in Entities |-> "absent"]
    /\ generation = [e \in Entities |-> 0]
    /\ entityComponents = [e \in Entities |-> {}]
    /\ cleanupPolicy = [c \in Components |-> "remove"]
    /\ deferDepth = 0
    /\ cmdQueue = << >>
    /\ flushing = FALSE
    /\ observers = {}
    /\ hookEnabled = [c \in Components |-> FALSE]
    /\ lastEventBatch = << >>

-----------------------------------------------------------------------------
\* Actions

\* --- Entity Creation ---
\* Create a new entity (from absent state)
CreateEntity ==
    \E e \in Entities :
        /\ IsAbsent(e)
        /\ ~flushing
        /\ entityState' = [entityState EXCEPT ![e] = "alive"]
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* Recycle a dead entity (reuse its ID with the already-bumped generation)
RecycleEntity ==
    \E e \in Entities :
        /\ IsDead(e)
        /\ ~flushing
        /\ entityState' = [entityState EXCEPT ![e] = "alive"]
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* --- Observer Registration ---
\* Register an observer for a specific event+component pair
RegisterObserver ==
    \E c \in Components, evtKind \in {"obs_on_add", "obs_on_remove", "obs_on_set"} :
        /\ ~flushing
        /\ [event |-> evtKind, component |-> c] \notin observers
        /\ observers' = observers \union {[event |-> evtKind, component |-> c]}
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing, hookEnabled >>

\* Unregister an observer
UnregisterObserver ==
    \E obs \in observers :
        /\ ~flushing
        /\ observers' = observers \ {obs}
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing, hookEnabled >>

\* --- Hook Registration ---
\* Enable hooks for a component (must be done before the component is in use,
\* but we relax this in the spec for modeling flexibility)
EnableHook ==
    \E c \in Components :
        /\ ~flushing
        /\ hookEnabled[c] = FALSE
        /\ hookEnabled' = [hookEnabled EXCEPT ![c] = TRUE]
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents, cleanupPolicy,
                        deferDepth, cmdQueue, flushing, observers >>

\* --- Component Operations (Direct Mode) ---
\* Add a component to an alive entity (direct mode)
\* Emits: hook_on_add -> obs_on_add -> hook_on_set -> obs_on_set
AddComponentDirect ==
    \E e \in Entities, c \in Components :
        /\ DirectMode
        /\ IsAlive(e)
        /\ c \notin entityComponents[e]
        /\ entityComponents' = [entityComponents EXCEPT ![e] = @ \union {c}]
        /\ lastEventBatch' = AddEvents(e, c)
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* Remove a component from an alive entity (direct mode)
\* Emits: obs_on_remove -> hook_on_remove
RemoveComponentDirect ==
    \E e \in Entities, c \in Components :
        /\ DirectMode
        /\ IsAlive(e)
        /\ c \in entityComponents[e]
        /\ entityComponents' = [entityComponents EXCEPT ![e] = @ \ {c}]
        /\ lastEventBatch' = RemoveEvents(e, c)
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* --- Delete Entity (Direct Mode) ---
\* Delete an entity: emit remove events for all components, clear, mark dead, bump gen
DeleteEntityDirect ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ generation[e] < MaxGeneration
        \* Check no alive entity uses this entity as a component with "panic" policy
        /\ ~(\E c \in Components : c = e /\ cleanupPolicy[c] = "panic"
              /\ \E other \in AliveEntities : c \in entityComponents[other])
        /\ entityState' = [entityState EXCEPT ![e] = "dead"]
        /\ lastEventBatch' = RemoveAllEvents(e, entityComponents[e])
        /\ entityComponents' = [entityComponents EXCEPT ![e] = {}]
        /\ generation' = [generation EXCEPT ![e] = @ + 1]
        /\ UNCHANGED << cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* --- Clear Entity (Direct Mode) ---
\* Remove all components from an entity but keep it alive
\* Emits remove events for each component
ClearEntityDirect ==
    \E e \in Entities :
        /\ DirectMode
        /\ IsAlive(e)
        /\ entityComponents[e] # {}
        /\ lastEventBatch' = RemoveAllEvents(e, entityComponents[e])
        /\ entityComponents' = [entityComponents EXCEPT ![e] = {}]
        /\ UNCHANGED << entityState, generation, cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

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
        \* Emit remove events for the dying entity's own components
        /\ LET ownRemoveEvts == RemoveAllEvents(e, entityComponents[e])
               \* Emit remove events for all other entities losing component e
               affectedEnts == EntitiesWithComponent(e) \ {e}
           IN
           LET RECURSIVE AffectedEvents(_)
               AffectedEvents(ents) ==
                   IF ents = {} THEN << >>
                   ELSE LET ent == CHOOSE x \in ents : TRUE
                        IN RemoveEvents(ent, e) \o AffectedEvents(ents \ {ent})
               allEvents == ownRemoveEvts \o AffectedEvents(affectedEnts)
           IN lastEventBatch' = allEvents
        /\ entityState' = [entityState EXCEPT ![e] = "dead"]
        /\ entityComponents' = [ent \in Entities |->
            IF ent = e THEN {}
            ELSE entityComponents[ent] \ {e}]
        /\ generation' = [generation EXCEPT ![e] = @ + 1]
        /\ UNCHANGED << cleanupPolicy,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

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
           \* Emit remove events for all dying entities' components
           /\ LET RECURSIVE DyingEvents(_)
                  DyingEvents(ents) ==
                      IF ents = {} THEN << >>
                      ELSE LET ent == CHOOSE x \in ents : TRUE
                           IN RemoveAllEvents(ent, entityComponents[ent])
                              \o DyingEvents(ents \ {ent})
                  allEvents == DyingEvents(allDying)
              IN lastEventBatch' = allEvents
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
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* --- Set Cleanup Policy ---
SetCleanupPolicy ==
    \E c \in Components, policy \in CleanupPolicies :
        /\ ~flushing
        /\ cleanupPolicy[c] # policy
        /\ cleanupPolicy' = [cleanupPolicy EXCEPT ![c] = policy]
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents,
                        deferDepth, cmdQueue, flushing,
                        observers, hookEnabled >>

\* --- Deferred Operations ---

\* Begin deferring: increment defer counter
DeferBegin ==
    /\ deferDepth < MaxDefer
    /\ ~flushing
    /\ deferDepth' = deferDepth + 1
    /\ lastEventBatch' = << >>
    /\ UNCHANGED << entityState, generation, entityComponents,
                    cleanupPolicy, cmdQueue, flushing,
                    observers, hookEnabled >>

\* Enqueue an Add command (deferred mode)
AddComponentDeferred ==
    \E e \in Entities, c \in Components :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "add", entity |-> e, component |-> c])
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing,
                        observers, hookEnabled >>

\* Enqueue a Remove command (deferred mode)
RemoveComponentDeferred ==
    \E e \in Entities, c \in Components :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "remove", entity |-> e, component |-> c])
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing,
                        observers, hookEnabled >>

\* Enqueue a Delete command (deferred mode)
DeleteEntityDeferred ==
    \E e \in Entities :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "delete", entity |-> e, component |-> "none"])
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing,
                        observers, hookEnabled >>

\* Enqueue a Clear command (deferred mode)
ClearEntityDeferred ==
    \E e \in Entities :
        /\ DeferredMode
        /\ IsAlive(e)
        /\ Len(cmdQueue) < MaxQueueLen
        /\ cmdQueue' = Append(cmdQueue, [kind |-> "clear", entity |-> e, component |-> "none"])
        /\ lastEventBatch' = << >>
        /\ UNCHANGED << entityState, generation, entityComponents,
                        cleanupPolicy, deferDepth, flushing,
                        observers, hookEnabled >>

\* --- Command Flush ---

\* Apply a single command to the world state, also producing events.
\* Returns the new state as a record including the cumulated event batch.
ApplyCmd(cmd, es, ec, gen, batch, obs, hk) ==
    IF ~(es[cmd.entity] = "alive") THEN
        \* Entity is dead or absent: discard command (no events)
        [entityState |-> es, entityComponents |-> ec, generation |-> gen, batch |-> batch]
    ELSE
        CASE cmd.kind = "add" ->
            LET newEc == [ec EXCEPT ![cmd.entity] = @ \union {cmd.component}]
                \* Only emit events if the component was actually new
                events == IF cmd.component \notin ec[cmd.entity]
                          THEN AddEvents(cmd.entity, cmd.component)
                          ELSE << >>
            IN [entityState |-> es,
                entityComponents |-> newEc,
                generation |-> gen,
                batch |-> batch \o events]
        [] cmd.kind = "remove" ->
            LET newEc == [ec EXCEPT ![cmd.entity] = @ \ {cmd.component}]
                \* Only emit events if the component was actually present
                events == IF cmd.component \in ec[cmd.entity]
                          THEN RemoveEvents(cmd.entity, cmd.component)
                          ELSE << >>
            IN [entityState |-> es,
                entityComponents |-> newEc,
                generation |-> gen,
                batch |-> batch \o events]
        [] cmd.kind = "delete" ->
            LET removeEvts == RemoveAllEvents(cmd.entity, ec[cmd.entity])
            IN IF gen[cmd.entity] < MaxGeneration THEN
                [entityState |-> [es EXCEPT ![cmd.entity] = "dead"],
                 entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
                 generation |-> [gen EXCEPT ![cmd.entity] = @ + 1],
                 batch |-> batch \o removeEvts]
            ELSE
                \* At max generation, still delete but cap generation
                [entityState |-> [es EXCEPT ![cmd.entity] = "dead"],
                 entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
                 generation |-> gen,
                 batch |-> batch \o removeEvts]
        [] cmd.kind = "clear" ->
            LET removeEvts == RemoveAllEvents(cmd.entity, ec[cmd.entity])
            IN [entityState |-> es,
                entityComponents |-> [ec EXCEPT ![cmd.entity] = {}],
                generation |-> gen,
                batch |-> batch \o removeEvts]

\* Flush: apply all queued commands sequentially, then clear queue
RECURSIVE ApplyAllCmds(_, _, _, _, _, _, _)
ApplyAllCmds(queue, es, ec, gen, batch, obs, hk) ==
    IF queue = << >> THEN
        [entityState |-> es, entityComponents |-> ec, generation |-> gen, batch |-> batch]
    ELSE
        LET result == ApplyCmd(Head(queue), es, ec, gen, batch, obs, hk)
        IN ApplyAllCmds(Tail(queue),
                        result.entityState, result.entityComponents,
                        result.generation, result.batch, obs, hk)

DeferEnd ==
    /\ deferDepth = 1  \* Outermost defer_end triggers flush
    /\ ~flushing
    /\ LET result == ApplyAllCmds(cmdQueue, entityState, entityComponents,
                                  generation, << >>, observers, hookEnabled)
       IN
        /\ entityState' = result.entityState
        /\ entityComponents' = result.entityComponents
        /\ generation' = result.generation
        /\ lastEventBatch' = result.batch
    /\ deferDepth' = 0
    /\ cmdQueue' = << >>
    /\ flushing' = FALSE
    /\ UNCHANGED << cleanupPolicy, observers, hookEnabled >>

\* Decrement defer depth without flushing (nested defer_end)
DeferEndNested ==
    /\ deferDepth > 1
    /\ deferDepth' = deferDepth - 1
    /\ lastEventBatch' = << >>
    /\ UNCHANGED << entityState, generation, entityComponents,
                    cleanupPolicy, cmdQueue, flushing,
                    observers, hookEnabled >>

-----------------------------------------------------------------------------
\* Next-state relation

Next ==
    \* Entity lifecycle
    \/ CreateEntity
    \/ RecycleEntity
    \* Observer/hook registration
    \/ RegisterObserver
    \/ UnregisterObserver
    \/ EnableHook
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

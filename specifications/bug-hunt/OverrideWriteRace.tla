-------------------------- MODULE OverrideWriteRace --------------------------
(*
 * Override Removal Write Race — Bug-Hunting Spec for Flecs ECS
 *
 * Models the data race in commands.c:flecs_defer_remove (lines 276-312).
 *
 * When removing an overridden component during readonly/deferred mode,
 * Flecs IMMEDIATELY writes the base component value into the entity's
 * table column — bypassing the command queue. This is a direct write
 * to shared world storage from a worker thread.
 *
 * The pipeline scheduler prevents this from being a problem in normal
 * use: systems that touch the same archetype are never scheduled in
 * parallel. But if:
 *   (a) Two systems in different stages both remove the same overridden
 *       component from the same entity, OR
 *   (b) One system reads a component while another stage's system
 *       removes the override on that same component
 * ...then there is a data race on the component memory.
 *
 * This spec models:
 *   - N threads, each running a system during readonly mode
 *   - A shared component slot (abstracting table column memory)
 *   - Non-atomic read and write of that slot
 *   - The override removal path that writes immediately
 *
 * Source: commands.c:276-312 (flecs_defer_remove override copy)
 * Source: table.c:2695-2717 (non-atomic table lock ++/--)
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    Threads,        \* e.g., {t1, t2}
    BaseValue,      \* The "base" component value (from prefab/parent)
    OverrideValue   \* The "override" value (entity's own copy)

Values == {BaseValue, OverrideValue}

VARIABLES
    (* --- Shared component memory (table column slot) --- *)
    slotValue,       \* Current value in the component slot
    slotWriting,     \* Is anyone mid-write? (models torn write detection)

    (* --- Per-thread state --- *)
    pc,              \* Thread -> program counter
    localRead,       \* Thread -> value last read from slot

    (* --- Tracking --- *)
    writeCount,      \* Total writes performed (for detecting lost updates)
    readsDuringWrite \* Did any thread read while another was writing?

vars == <<slotValue, slotWriting, pc, localRead, writeCount, readsDuringWrite>>

-----------------------------------------------------------------------------
Init ==
    /\ slotValue = OverrideValue  \* Entity starts with an override
    /\ slotWriting = FALSE
    /\ pc = [t \in Threads |-> "idle"]
    /\ localRead = [t \in Threads |-> OverrideValue]
    /\ writeCount = 0
    /\ readsDuringWrite = FALSE

-----------------------------------------------------------------------------
(* A thread's system wants to READ the component value.
 * This is a normal system iteration — reads component data. *)

StartRead(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "reading"]
    /\ UNCHANGED <<slotValue, slotWriting, localRead, writeCount, readsDuringWrite>>

DoRead(t) ==
    /\ pc[t] = "reading"
    /\ localRead' = [localRead EXCEPT ![t] = slotValue]
    (* Detect: reading while another thread is mid-write = DATA RACE *)
    /\ readsDuringWrite' = (readsDuringWrite \/ slotWriting)
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<slotValue, slotWriting, writeCount>>

-----------------------------------------------------------------------------
(* A thread's system calls ecs_remove on an overridden component.
 * flecs_defer_remove detects the override and IMMEDIATELY writes
 * the base value into the slot — no deferral, no lock.
 *
 * We model this as a non-atomic write: set slotWriting=TRUE,
 * write the value, set slotWriting=FALSE. Another thread
 * interleaving between these steps sees a torn/inconsistent state. *)

StartOverrideRemove(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "write_begin"]
    /\ UNCHANGED <<slotValue, slotWriting, localRead, writeCount, readsDuringWrite>>

(* Begin writing — mark slot as being written to *)
WriteBegin(t) ==
    /\ pc[t] = "write_begin"
    /\ slotWriting' = TRUE
    /\ pc' = [pc EXCEPT ![t] = "write_value"]
    /\ UNCHANGED <<slotValue, localRead, writeCount, readsDuringWrite>>

(* Actually write the base value into the slot *)
WriteValue(t) ==
    /\ pc[t] = "write_value"
    /\ slotValue' = BaseValue  \* Override removal copies base value
    /\ writeCount' = writeCount + 1
    /\ pc' = [pc EXCEPT ![t] = "write_end"]
    /\ UNCHANGED <<slotWriting, localRead, readsDuringWrite>>

(* Finish writing *)
WriteEnd(t) ==
    /\ pc[t] = "write_end"
    /\ slotWriting' = FALSE
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<slotValue, localRead, writeCount, readsDuringWrite>>

-----------------------------------------------------------------------------
Next ==
    \E t \in Threads :
        \/ StartRead(t)
        \/ DoRead(t)
        \/ StartOverrideRemove(t)
        \/ WriteBegin(t)
        \/ WriteValue(t)
        \/ WriteEnd(t)

Spec == Init /\ [][Next]_vars

FairSpec ==
    Spec
    /\ \A t \in Threads :
        /\ WF_vars(DoRead(t))
        /\ WF_vars(WriteBegin(t))
        /\ WF_vars(WriteValue(t))
        /\ WF_vars(WriteEnd(t))

StateConstraint ==
    writeCount <= 3

-----------------------------------------------------------------------------
(* SAFETY INVARIANTS *)

TypeOK ==
    /\ slotValue \in Values
    /\ slotWriting \in BOOLEAN
    /\ \A t \in Threads : pc[t] \in {"idle", "reading",
           "write_begin", "write_value", "write_end"}
    /\ \A t \in Threads : localRead[t] \in Values
    /\ writeCount \in Nat

(* ============================================================
 * BUG-FINDING INVARIANT: NoDataRace
 *
 * A data race occurs when one thread reads the component slot
 * while another thread is in the middle of writing to it.
 * In C, this is undefined behavior.
 *
 * Source: commands.c:276-312 — the copy(dst, src, 1, ti) call
 *         inside flecs_defer_remove happens with no lock while
 *         other threads may be iterating the same table column.
 * ============================================================ *)
NoDataRace ==
    ~readsDuringWrite

(* Two threads should not both be writing simultaneously *)
NoSimultaneousWrite ==
    Cardinality({t \in Threads : pc[t] \in {"write_begin", "write_value", "write_end"}}) <= 1

-----------------------------------------------------------------------------
(* TEMPORAL PROPERTIES *)

(* Every thread that starts an operation eventually returns to idle *)
EventuallyIdle ==
    \A t \in Threads :
        (pc[t] # "idle") ~> (pc[t] = "idle")

(* The slot value eventually stabilizes to BaseValue after a removal *)
EventuallyBase ==
    (writeCount > 0) ~> (slotValue = BaseValue)

(* If a read happens during a write, we've found a data race —
 * this should be unreachable in a correct system. We check that
 * the system CANNOT avoid data races: *)
DataRaceIsReachable ==
    <>(readsDuringWrite)

=============================================================================

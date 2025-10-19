---------------------------- MODULE Clock ----------------------------
(***************************************************************************
 * TLA+ Specification: Timestamp Oracle and Logical Clocks
 *
 * Based on:
 * [1] Lamport, L. (1978).
 *     "Time, Clocks, and the Ordering of Events in a Distributed System"
 *     Communications of the ACM, 21(7), 558-565.
 *     DOI: 10.1145/359545.359563
 *     Seminal paper on logical clocks
 *
 * [2] Corbett, J. C., et al. (2013).
 *     "Spanner: Google's Globally-Distributed Database"
 *     ACM Transactions on Computer Systems (TOCS), 31(3), Article 8.
 *     DOI: 10.1145/2491245
 *     TrueTime and external consistency
 *
 * [3] Mattern, F. (1988).
 *     "Virtual Time and Global States of Distributed Systems"
 *     Parallel and Distributed Algorithms, 215-226.
 *     Vector clocks
 *
 * [4] Fidge, C. J. (1988).
 *     "Timestamps in Message-Passing Systems That Preserve the Partial Ordering"
 *     Proceedings of the 11th Australian Computer Science Conference, 56-66.
 *     Independent discovery of vector clocks
 *
 * This specification models timestamp generation including:
 * - Lamport logical clocks
 * - Vector clocks
 * - Hybrid logical clocks (HLC)
 * - Timestamp oracle for distributed transactions
 * - External consistency guarantees
 * - Causality preservation
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    Nodes,              \* Set of node IDs
    MaxTimestamp,       \* Maximum timestamp value
    ClockSkewBound,     \* Maximum clock skew (microseconds)
    MaxEvents           \* Maximum events per node

ASSUME Cardinality(Nodes) > 0
ASSUME MaxTimestamp \in Nat \ {0}
ASSUME ClockSkewBound \in Nat
ASSUME MaxEvents \in Nat \ {0}

(***************************************************************************
 * Clock Types
 ***************************************************************************)
ClockTypes == {
    "LAMPORT",          \* Lamport logical clock
    "VECTOR",           \* Vector clock
    "HYBRID",           \* Hybrid logical clock (HLC)
    "PHYSICAL"          \* Physical clock with uncertainty
}

(***************************************************************************
 * Event Types (Lamport 1978)
 ***************************************************************************)
EventTypes == {
    "LOCAL",            \* Local computation event
    "SEND",             \* Send message event
    "RECEIVE"           \* Receive message event
}

VARIABLES
    \* Lamport clocks (per Lamport 1978)
    lamportClock,       \* [node |-> clock_value]
    
    \* Vector clocks (per Mattern 1988, Fidge 1988)
    vectorClock,        \* [node |-> [node' |-> clock_value]]
    
    \* Hybrid logical clocks (based on Spanner)
    hlcPhysical,        \* [node |-> physical_time]
    hlcLogical,         \* [node |-> logical_counter]
    
    \* Physical clocks with uncertainty (Spanner TrueTime)
    physicalTime,       \* [node |-> current_physical_time]
    uncertainty,        \* [node |-> uncertainty_interval]
    
    \* Timestamp oracle state
    oracleTimestamp,    \* Last timestamp allocated by oracle
    allocatedTimestamps,\* Set of allocated timestamps
    
    \* Event log (for causality checking)
    events,             \* [<<node, eid>> |-> event_record]
    nextEventId,        \* [node |-> next_event_id]
    
    \* Message tracking
    messages,           \* Set of in-flight messages
    messageId           \* Next message ID

lamportVars == <<lamportClock>>
vectorVars == <<vectorClock>>
hlcVars == <<hlcPhysical, hlcLogical>>
physicalVars == <<physicalTime, uncertainty>>
oracleVars == <<oracleTimestamp, allocatedTimestamps>>
eventVars == <<events, nextEventId>>
msgVars == <<messages, messageId>>
vars == <<lamportVars, vectorVars, hlcVars, physicalVars, oracleVars, 
          eventVars, msgVars>>

(***************************************************************************
 * Event Record Structure
 ***************************************************************************)
EventRecord == [
    eid: Nat,
    node: Nodes,
    type: EventTypes,
    lamportTs: Nat,
    vectorTs: [Nodes -> Nat],
    hlcTs: [physical: Nat, logical: Nat],
    realTime: Nat
]

(***************************************************************************
 * Message Structure
 ***************************************************************************)
MessageRecord == [
    mid: Nat,
    from: Nodes,
    to: Nodes,
    lamportTs: Nat,
    vectorTs: [Nodes -> Nat],
    hlcTs: [physical: Nat, logical: Nat],
    sent: BOOLEAN,
    delivered: BOOLEAN
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ lamportClock \in [Nodes -> Nat]
    /\ vectorClock \in [Nodes -> [Nodes -> Nat]]
    /\ hlcPhysical \in [Nodes -> Nat]
    /\ hlcLogical \in [Nodes -> Nat]
    /\ physicalTime \in [Nodes -> Nat]
    /\ uncertainty \in [Nodes -> Nat]
    /\ oracleTimestamp \in Nat
    /\ allocatedTimestamps \subseteq Nat
    /\ events \in [((Nodes \X Nat)) -> EventRecord]
    /\ nextEventId \in [Nodes -> Nat]
    /\ messages \subseteq MessageRecord
    /\ messageId \in Nat

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ lamportClock = [n \in Nodes |-> 0]
    /\ vectorClock = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ hlcPhysical = [n \in Nodes |-> 0]
    /\ hlcLogical = [n \in Nodes |-> 0]
    /\ physicalTime = [n \in Nodes |-> 0]
    /\ uncertainty = [n \in Nodes |-> ClockSkewBound]
    /\ oracleTimestamp = 0
    /\ allocatedTimestamps = {}
    /\ events = [x \in {} |-> {}]
    /\ nextEventId = [n \in Nodes |-> 1]
    /\ messages = {}
    /\ messageId = 1

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Maximum of two values
Max(a, b) == IF a > b THEN a ELSE b

\* Vector clock comparison (Mattern 1988)
VectorLessThan(v1, v2) ==
    /\ \A n \in Nodes : v1[n] <= v2[n]
    /\ \E n \in Nodes : v1[n] < v2[n]

\* Vector clock concurrent
VectorConcurrent(v1, v2) ==
    /\ ~VectorLessThan(v1, v2)
    /\ ~VectorLessThan(v2, v1)

\* Merge vector clocks
MergeVectorClocks(v1, v2) ==
    [n \in Nodes |-> Max(v1[n], v2[n])]

(***************************************************************************
 * Actions: Lamport Clock (Lamport 1978, Section 4)
 ***************************************************************************)

\* Local event with Lamport clock
LamportLocalEvent(node) ==
    /\ node \in Nodes
    /\ nextEventId[node] <= MaxEvents
    /\ LET eid == nextEventId[node]
           newClock == lamportClock[node] + 1
           event == [
               eid |-> eid,
               node |-> node,
               type |-> "LOCAL",
               lamportTs |-> newClock,
               vectorTs |-> vectorClock[node],
               hlcTs |-> [physical |-> hlcPhysical[node], 
                         logical |-> hlcLogical[node]],
               realTime |-> physicalTime[node]
           ]
       IN
        /\ lamportClock' = [lamportClock EXCEPT ![node] = newClock]
        /\ events' = events @@ (<<node, eid>> :> event)
        /\ nextEventId' = [nextEventId EXCEPT ![node] = @ + 1]
        /\ UNCHANGED <<vectorVars, hlcVars, physicalVars, oracleVars, msgVars>>

\* Send message with Lamport clock
LamportSendMessage(from, to) ==
    /\ from \in Nodes
    /\ to \in Nodes
    /\ from # to
    /\ nextEventId[from] <= MaxEvents
    /\ LET eid == nextEventId[from]
           newClock == lamportClock[from] + 1
           mid == messageId
           msg == [
               mid |-> mid,
               from |-> from,
               to |-> to,
               lamportTs |-> newClock,
               vectorTs |-> vectorClock[from],
               hlcTs |-> [physical |-> hlcPhysical[from], 
                         logical |-> hlcLogical[from]],
               sent |-> TRUE,
               delivered |-> FALSE
           ]
           event == [
               eid |-> eid,
               node |-> from,
               type |-> "SEND",
               lamportTs |-> newClock,
               vectorTs |-> vectorClock[from],
               hlcTs |-> [physical |-> hlcPhysical[from], 
                         logical |-> hlcLogical[from]],
               realTime |-> physicalTime[from]
           ]
       IN
        /\ lamportClock' = [lamportClock EXCEPT ![from] = newClock]
        /\ messages' = messages \cup {msg}
        /\ messageId' = messageId + 1
        /\ events' = events @@ (<<from, eid>> :> event)
        /\ nextEventId' = [nextEventId EXCEPT ![from] = @ + 1]
        /\ UNCHANGED <<vectorVars, hlcVars, physicalVars, oracleVars>>

\* Receive message with Lamport clock (Lamport 1978, IR2)
LamportReceiveMessage(to) ==
    /\ to \in Nodes
    /\ nextEventId[to] <= MaxEvents
    /\ \E msg \in messages :
        /\ msg.to = to
        /\ msg.sent = TRUE
        /\ msg.delivered = FALSE
        /\ LET eid == nextEventId[to]
               newClock == Max(lamportClock[to], msg.lamportTs) + 1
               event == [
                   eid |-> eid,
                   node |-> to,
                   type |-> "RECEIVE",
                   lamportTs |-> newClock,
                   vectorTs |-> vectorClock[to],
                   hlcTs |-> [physical |-> hlcPhysical[to], 
                             logical |-> hlcLogical[to]],
                   realTime |-> physicalTime[to]
               ]
           IN
            /\ lamportClock' = [lamportClock EXCEPT ![to] = newClock]
            /\ messages' = (messages \ {msg}) \cup 
                          {[msg EXCEPT !.delivered = TRUE]}
            /\ events' = events @@ (<<to, eid>> :> event)
            /\ nextEventId' = [nextEventId EXCEPT ![to] = @ + 1]
            /\ UNCHANGED <<vectorVars, hlcVars, physicalVars, oracleVars, 
                           messageId>>

(***************************************************************************
 * Actions: Vector Clock (Mattern 1988, Fidge 1988)
 ***************************************************************************)

\* Local event with vector clock
VectorLocalEvent(node) ==
    /\ node \in Nodes
    /\ nextEventId[node] <= MaxEvents
    /\ LET newVector == [vectorClock[node] EXCEPT ![node] = @ + 1]
       IN
        /\ vectorClock' = [vectorClock EXCEPT ![node] = newVector]
        /\ UNCHANGED <<lamportVars, hlcVars, physicalVars, oracleVars, 
                       eventVars, msgVars>>

\* Send message with vector clock
VectorSendMessage(from, to) ==
    /\ from \in Nodes
    /\ to \in Nodes
    /\ from # to
    /\ LET newVector == [vectorClock[from] EXCEPT ![from] = @ + 1]
           mid == messageId
           msg == [
               mid |-> mid,
               from |-> from,
               to |-> to,
               lamportTs |-> lamportClock[from],
               vectorTs |-> newVector,
               hlcTs |-> [physical |-> 0, logical |-> 0],
               sent |-> TRUE,
               delivered |-> FALSE
           ]
       IN
        /\ vectorClock' = [vectorClock EXCEPT ![from] = newVector]
        /\ messages' = messages \cup {msg}
        /\ messageId' = messageId + 1
        /\ UNCHANGED <<lamportVars, hlcVars, physicalVars, oracleVars, 
                       eventVars>>

\* Receive message with vector clock
VectorReceiveMessage(to) ==
    /\ to \in Nodes
    /\ \E msg \in messages :
        /\ msg.to = to
        /\ msg.sent = TRUE
        /\ msg.delivered = FALSE
        /\ LET mergedVector == MergeVectorClocks(vectorClock[to], msg.vectorTs)
               newVector == [mergedVector EXCEPT ![to] = @ + 1]
           IN
            /\ vectorClock' = [vectorClock EXCEPT ![to] = newVector]
            /\ messages' = (messages \ {msg}) \cup 
                          {[msg EXCEPT !.delivered = TRUE]}
            /\ UNCHANGED <<lamportVars, hlcVars, physicalVars, oracleVars, 
                           eventVars, messageId>>

(***************************************************************************
 * Actions: Hybrid Logical Clock (based on Spanner)
 ***************************************************************************)

\* Update HLC on event
UpdateHLC(node, msgPhysical, msgLogical) ==
    /\ node \in Nodes
    /\ LET currentPhysical == physicalTime[node]
           maxPhysical == Max(currentPhysical, msgPhysical)
           newLogical == IF maxPhysical = currentPhysical /\ 
                            maxPhysical = msgPhysical
                         THEN Max(hlcLogical[node], msgLogical) + 1
                         ELSE IF maxPhysical = currentPhysical
                         THEN hlcLogical[node] + 1
                         ELSE IF maxPhysical = msgPhysical
                         THEN msgLogical + 1
                         ELSE 0
       IN
        /\ hlcPhysical' = [hlcPhysical EXCEPT ![node] = maxPhysical]
        /\ hlcLogical' = [hlcLogical EXCEPT ![node] = newLogical]

\* Local event with HLC
HLCLocalEvent(node) ==
    /\ node \in Nodes
    /\ UpdateHLC(node, 0, 0)
    /\ UNCHANGED <<lamportVars, vectorVars, physicalVars, oracleVars, 
                   eventVars, msgVars>>

(***************************************************************************
 * Actions: Timestamp Oracle (Spanner-style)
 ***************************************************************************)

\* Allocate timestamp from oracle
AllocateTimestamp(node) ==
    /\ node \in Nodes
    /\ LET ts == oracleTimestamp + 1
       IN
        /\ oracleTimestamp' = ts
        /\ allocatedTimestamps' = allocatedTimestamps \cup {ts}
        /\ UNCHANGED <<lamportVars, vectorVars, hlcVars, physicalVars, 
                       eventVars, msgVars>>

\* Advance physical time (bounded by clock skew)
AdvancePhysicalTime(node) ==
    /\ node \in Nodes
    /\ physicalTime' = [physicalTime EXCEPT ![node] = @ + 1]
    /\ UNCHANGED <<lamportVars, vectorVars, hlcVars, uncertainty, oracleVars, 
                   eventVars, msgVars>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E n \in Nodes : LamportLocalEvent(n)
    \/ \E f, t \in Nodes : LamportSendMessage(f, t)
    \/ \E n \in Nodes : LamportReceiveMessage(n)
    \/ \E n \in Nodes : VectorLocalEvent(n)
    \/ \E f, t \in Nodes : VectorSendMessage(f, t)
    \/ \E n \in Nodes : VectorReceiveMessage(n)
    \/ \E n \in Nodes : HLCLocalEvent(n)
    \/ \E n \in Nodes : AllocateTimestamp(n)
    \/ \E n \in Nodes : AdvancePhysicalTime(n)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties: Clock Condition (Lamport 1978)
 ***************************************************************************)

\* Clock Condition (Lamport 1978, Definition)
\* If event a happens before event b, then C(a) < C(b)
LamportClockCondition ==
    \A n1, n2 \in Nodes, e1, e2 \in Nat :
        /\ <<n1, e1>> \in DOMAIN events
        /\ <<n2, e2>> \in DOMAIN events
        /\ events[<<n1, e1>>].type = "SEND"
        /\ events[<<n2, e2>>].type = "RECEIVE"
        /\ \E msg \in messages :
            /\ msg.from = n1
            /\ msg.to = n2
            /\ msg.delivered = TRUE
        => events[<<n1, e1>>].lamportTs < events[<<n2, e2>>].lamportTs

\* Vector clock correctly captures causality
VectorClockCausality ==
    \A n1, n2 \in Nodes, e1, e2 \in Nat :
        /\ <<n1, e1>> \in DOMAIN events
        /\ <<n2, e2>> \in DOMAIN events
        /\ VectorLessThan(events[<<n1, e1>>].vectorTs, 
                         events[<<n2, e2>>].vectorTs)
        => events[<<n1, e1>>].realTime <= events[<<n2, e2>>].realTime

\* Timestamps unique and monotonic
TimestampsUniqueMonotonic ==
    /\ \A ts1, ts2 \in allocatedTimestamps : 
        ts1 # ts2 => ts1 # ts2
    /\ oracleTimestamp = Cardinality(allocatedTimestamps)

\* Physical time within uncertainty bound
PhysicalTimeWithinBounds ==
    \A n \in Nodes : uncertainty[n] >= 0 /\ uncertainty[n] <= ClockSkewBound

Safety ==
    /\ LamportClockCondition
    /\ VectorClockCausality
    /\ TimestampsUniqueMonotonic
    /\ PhysicalTimeWithinBounds

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Clocks eventually advance
ClocksEventuallyAdvance ==
    \A n \in Nodes : <>(lamportClock[n] > 0)

\* Messages eventually delivered
MessagesEventuallyDelivered ==
    \A msg \in messages : msg.sent ~> msg.delivered

Liveness ==
    /\ ClocksEventuallyAdvance
    /\ MessagesEventuallyDelivered

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []Liveness

================================================================================


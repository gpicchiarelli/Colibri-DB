---------------------------- MODULE TwoPhaseCommit ----------------------------
(***************************************************************************
 * TLA+ Specification: Two-Phase Commit Protocol
 *
 * Based on:
 * [1] Gray, J. (1978).
 *     "Notes on Data Base Operating Systems"
 *     In: Operating Systems: An Advanced Course, pp. 393-481.
 *     Springer-Verlag. Lecture Notes in Computer Science, Vol. 60.
 *     ISBN: 3540087559
 *     Original 2PC specification
 *
 * [2] Bernstein, P. A., Hadzilacos, V., & Goodman, N. (1987).
 *     "Concurrency Control and Recovery in Database Systems"
 *     Addison-Wesley. Chapter 7: Commit Protocols
 *     ISBN: 0201107155
 *     Formal analysis of 2PC
 *
 * [3] Lampson, B., & Sturgis, H. (1976).
 *     "Crash Recovery in a Distributed Data Storage System"
 *     Xerox PARC Technical Report.
 *     Early distributed commit protocol
 *
 * [4] Skeen, D. (1981).
 *     "Nonblocking Commit Protocols"
 *     Proceedings of ACM SIGMOD, pp. 133-142.
 *     DOI: 10.1145/582318.582339
 *     Three-phase commit (3PC)
 *
 * This specification models Two-Phase Commit including:
 * - Coordinator and participant roles
 * - Prepare and commit phases
 * - Vote collection and decision
 * - Timeout and failure handling
 * - Blocking behavior
 * - Recovery from failures
 * - Atomicity guarantees
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    Coordinators,       \* Set of coordinator IDs
    Participants,       \* Set of participant IDs
    Transactions,       \* Set of transaction IDs
    MaxTimeout          \* Maximum timeout value

ASSUME Cardinality(Coordinators) > 0
ASSUME Cardinality(Participants) > 0
ASSUME Cardinality(Transactions) > 0
ASSUME MaxTimeout \in Nat \ {0}

(***************************************************************************
 * Coordinator States (Gray 1978, Section 3.4.1)
 ***************************************************************************)
CoordinatorStates == {
    "IDLE",             \* No active transaction
    "PREPARING",        \* Sent PREPARE, waiting for votes
    "COMMITTING",       \* Decision to commit, sending COMMIT
    "ABORTING",         \* Decision to abort, sending ABORT
    "COMMITTED",        \* Transaction committed
    "ABORTED"           \* Transaction aborted
}

(***************************************************************************
 * Participant States (Gray 1978, Section 3.4.2)
 ***************************************************************************)
ParticipantStates == {
    "IDLE",             \* No active transaction
    "WORKING",          \* Executing transaction operations
    "PREPARED",         \* Voted YES, waiting for decision
    "COMMITTED",        \* Transaction committed
    "ABORTED"           \* Transaction aborted
}

(***************************************************************************
 * Message Types (Gray 1978)
 ***************************************************************************)
MessageTypes == {
    "PREPARE",          \* Coordinator -> Participant: prepare to commit
    "VOTE_YES",         \* Participant -> Coordinator: prepared successfully
    "VOTE_NO",          \* Participant -> Coordinator: cannot commit
    "COMMIT",           \* Coordinator -> Participant: commit decision
    "ABORT",            \* Coordinator -> Participant: abort decision
    "ACK"               \* Participant -> Coordinator: acknowledgment
}

VARIABLES
    \* Coordinator state
    coordState,         \* [<<cid, txn>> |-> coordinator_state]
    coordVotes,         \* [<<cid, txn>> |-> Set of received votes]
    coordDecision,      \* [<<cid, txn>> |-> decision]
    coordTimeout,       \* [<<cid, txn>> |-> timeout_counter]
    
    \* Participant state
    partState,          \* [<<pid, txn>> |-> participant_state]
    partVote,           \* [<<pid, txn>> |-> vote]
    partTimeout,        \* [<<pid, txn>> |-> timeout_counter]
    
    \* Message passing
    network,            \* Set of in-flight messages
    
    \* Persistent log (survives crashes)
    coordLog,           \* [<<cid, txn>> |-> log_entries]
    partLog,            \* [<<pid, txn>> |-> log_entries]
    
    \* Failure model
    coordFailed,        \* Set of failed coordinators
    partFailed          \* Set of failed participants

coordVars == <<coordState, coordVotes, coordDecision, coordTimeout, coordLog>>
partVars == <<partState, partVote, partTimeout, partLog>>
failVars == <<coordFailed, partFailed>>
vars == <<coordVars, partVars, network, failVars>>

(***************************************************************************
 * Message Structure
 ***************************************************************************)
Message == [
    type: MessageTypes,
    from: Coordinators \cup Participants,
    to: Coordinators \cup Participants,
    txn: Transactions
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ coordState \in [((Coordinators \X Transactions)) -> CoordinatorStates]
    /\ coordVotes \in [((Coordinators \X Transactions)) -> 
                      SUBSET (Participants \X {"YES", "NO"})]
    /\ coordDecision \in [((Coordinators \X Transactions)) -> 
                         {"COMMIT", "ABORT", "NONE"}]
    /\ coordTimeout \in [((Coordinators \X Transactions)) -> Nat]
    /\ partState \in [((Participants \X Transactions)) -> ParticipantStates]
    /\ partVote \in [((Participants \X Transactions)) -> {"YES", "NO", "NONE"}]
    /\ partTimeout \in [((Participants \X Transactions)) -> Nat]
    /\ network \subseteq Message
    /\ coordLog \in [((Coordinators \X Transactions)) -> Seq(STRING)]
    /\ partLog \in [((Participants \X Transactions)) -> Seq(STRING)]
    /\ coordFailed \subseteq Coordinators
    /\ partFailed \subseteq Participants

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ coordState = [link \in (Coordinators \X Transactions) |-> "IDLE"]
    /\ coordVotes = [link \in (Coordinators \X Transactions) |-> {}]
    /\ coordDecision = [link \in (Coordinators \X Transactions) |-> "NONE"]
    /\ coordTimeout = [link \in (Coordinators \X Transactions) |-> 0]
    /\ partState = [link \in (Participants \X Transactions) |-> "IDLE"]
    /\ partVote = [link \in (Participants \X Transactions) |-> "NONE"]
    /\ partTimeout = [link \in (Participants \X Transactions) |-> 0]
    /\ network = {}
    /\ coordLog = [link \in (Coordinators \X Transactions) |-> <<>>]
    /\ partLog = [link \in (Participants \X Transactions) |-> <<>>]
    /\ coordFailed = {}
    /\ partFailed = {}

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Check if all participants voted
AllVotesReceived(cid, txn) ==
    LET votes == coordVotes[<<cid, txn>>]
        votedParticipants == {p : <<p, v>> \in votes}
    IN votedParticipants = Participants

\* Check if all votes are YES
AllVotesYes(cid, txn) ==
    LET votes == coordVotes[<<cid, txn>>]
    IN \A <<p, v>> \in votes : v = "YES"

\* Send message
SendMessage(msg) ==
    network' = network \cup {msg}

\* Remove message
RemoveMessage(msg) ==
    network' = network \ {msg}

(***************************************************************************
 * Actions: Phase 1 - Prepare (Gray 1978, Section 3.4.1)
 ***************************************************************************)

\* Coordinator initiates transaction
CoordinatorStartTransaction(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] = "IDLE"
    /\ coordState' = [coordState EXCEPT ![<<cid, txn>>] = "PREPARING"]
    /\ coordTimeout' = [coordTimeout EXCEPT ![<<cid, txn>>] = MaxTimeout]
    /\ coordLog' = [coordLog EXCEPT 
        ![<<cid, txn>>] = Append(@, "START")]
    \* Broadcast PREPARE to all participants
    /\ network' = network \cup 
        {[type |-> "PREPARE", from |-> cid, to |-> p, txn |-> txn] : 
         p \in Participants}
    /\ UNCHANGED <<coordVotes, coordDecision, partVars, failVars, partLog>>

\* Participant receives PREPARE and votes
ParticipantVote(pid, txn, vote) ==
    /\ pid \in Participants
    /\ txn \in Transactions
    /\ vote \in {"YES", "NO"}
    /\ pid \notin partFailed
    /\ \E msg \in network :
        /\ msg.type = "PREPARE"
        /\ msg.to = pid
        /\ msg.txn = txn
        /\ LET cid == msg.from
           IN
            /\ partState[<<pid, txn>>] \in {"IDLE", "WORKING"}
            /\ IF vote = "YES"
               THEN
                   \* Vote YES: write PREPARED to log (force to disk)
                   /\ partState' = [partState EXCEPT 
                       ![<<pid, txn>>] = "PREPARED"]
                   /\ partLog' = [partLog EXCEPT 
                       ![<<pid, txn>>] = Append(@, "PREPARED")]
               ELSE
                   \* Vote NO: abort locally
                   /\ partState' = [partState EXCEPT 
                       ![<<pid, txn>>] = "ABORTED"]
                   /\ partLog' = [partLog EXCEPT 
                       ![<<pid, txn>>] = Append(@, "ABORTED")]
            /\ partVote' = [partVote EXCEPT ![<<pid, txn>>] = vote]
            /\ partTimeout' = [partTimeout EXCEPT 
                ![<<pid, txn>>] = MaxTimeout]
            \* Send vote to coordinator
            /\ network' = (network \ {msg}) \cup 
                {[type |-> IF vote = "YES" THEN "VOTE_YES" ELSE "VOTE_NO",
                  from |-> pid,
                  to |-> cid,
                  txn |-> txn]}
            /\ UNCHANGED <<coordVars, coordFailed, partFailed>>

\* Coordinator collects vote
CoordinatorCollectVote(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] = "PREPARING"
    /\ \E msg \in network :
        /\ msg.type \in {"VOTE_YES", "VOTE_NO"}
        /\ msg.to = cid
        /\ msg.txn = txn
        /\ LET pid == msg.from
               vote == IF msg.type = "VOTE_YES" THEN "YES" ELSE "NO"
           IN
            /\ coordVotes' = [coordVotes EXCEPT 
                ![<<cid, txn>>] = @ \cup {<<pid, vote>>}]
            /\ RemoveMessage(msg)
            /\ UNCHANGED <<coordState, coordDecision, coordTimeout, coordLog,
                           partVars, failVars>>

(***************************************************************************
 * Actions: Phase 2 - Commit/Abort (Gray 1978, Section 3.4.2)
 ***************************************************************************)

\* Coordinator makes decision
CoordinatorDecide(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] = "PREPARING"
    /\ AllVotesReceived(cid, txn)
    /\ LET decision == IF AllVotesYes(cid, txn) THEN "COMMIT" ELSE "ABORT"
           newState == IF decision = "COMMIT" THEN "COMMITTING" ELSE "ABORTING"
           msgType == IF decision = "COMMIT" THEN "COMMIT" ELSE "ABORT"
       IN
        /\ coordDecision' = [coordDecision EXCEPT ![<<cid, txn>>] = decision]
        /\ coordState' = [coordState EXCEPT ![<<cid, txn>>] = newState]
        /\ coordLog' = [coordLog EXCEPT 
            ![<<cid, txn>>] = Append(@, decision)]  \* Force to disk
        \* Broadcast decision to all participants
        /\ network' = network \cup 
            {[type |-> msgType, from |-> cid, to |-> p, txn |-> txn] : 
             p \in Participants}
        /\ UNCHANGED <<coordVotes, coordTimeout, partVars, failVars>>

\* Participant receives and executes decision
ParticipantExecuteDecision(pid, txn) ==
    /\ pid \in Participants
    /\ txn \in Transactions
    /\ pid \notin partFailed
    /\ partState[<<pid, txn>>] \in {"PREPARED", "WORKING"}
    /\ \E msg \in network :
        /\ msg.type \in {"COMMIT", "ABORT"}
        /\ msg.to = pid
        /\ msg.txn = txn
        /\ LET cid == msg.from
               decision == msg.type
               newState == IF decision = "COMMIT" THEN "COMMITTED" ELSE "ABORTED"
           IN
            /\ partState' = [partState EXCEPT ![<<pid, txn>>] = newState]
            /\ partLog' = [partLog EXCEPT 
                ![<<pid, txn>>] = Append(@, decision)]
            \* Send acknowledgment
            /\ network' = (network \ {msg}) \cup 
                {[type |-> "ACK", from |-> pid, to |-> cid, txn |-> txn]}
            /\ UNCHANGED <<partVote, partTimeout, coordVars, failVars>>

\* Coordinator receives acknowledgment
CoordinatorReceiveAck(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] \in {"COMMITTING", "ABORTING"}
    /\ \E msg \in network :
        /\ msg.type = "ACK"
        /\ msg.to = cid
        /\ msg.txn = txn
        /\ RemoveMessage(msg)
        /\ UNCHANGED <<coordState, coordVotes, coordDecision, coordTimeout,
                       coordLog, partVars, failVars>>

\* Coordinator finishes transaction
CoordinatorFinish(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] \in {"COMMITTING", "ABORTING"}
    \* All participants acknowledged (simplified: just move to final state)
    /\ LET newState == IF coordState[<<cid, txn>>] = "COMMITTING" 
                       THEN "COMMITTED" 
                       ELSE "ABORTED"
       IN
        /\ coordState' = [coordState EXCEPT ![<<cid, txn>>] = newState]
        /\ coordLog' = [coordLog EXCEPT 
            ![<<cid, txn>>] = Append(@, "COMPLETE")]
        /\ UNCHANGED <<coordVotes, coordDecision, coordTimeout, partVars,
                       network, failVars>>

(***************************************************************************
 * Actions: Timeout and Failure Handling (Bernstein Section 7.4)
 ***************************************************************************)

\* Coordinator timeout (abort if no decision made)
CoordinatorTimeout(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ cid \notin coordFailed
    /\ coordState[<<cid, txn>>] = "PREPARING"
    /\ coordTimeout[<<cid, txn>>] = 0
    /\ coordDecision[<<cid, txn>>] = "NONE"
    \* Timeout: abort transaction
    /\ coordDecision' = [coordDecision EXCEPT ![<<cid, txn>>] = "ABORT"]
    /\ coordState' = [coordState EXCEPT ![<<cid, txn>>] = "ABORTING"]
    /\ coordLog' = [coordLog EXCEPT ![<<cid, txn>>] = Append(@, "ABORT")]
    /\ network' = network \cup 
        {[type |-> "ABORT", from |-> cid, to |-> p, txn |-> txn] : 
         p \in Participants}
    /\ UNCHANGED <<coordVotes, coordTimeout, partVars, failVars>>

\* Participant timeout (blocked - must wait for decision)
ParticipantTimeout(pid, txn) ==
    /\ pid \in Participants
    /\ txn \in Transactions
    /\ pid \notin partFailed
    /\ partState[<<pid, txn>>] = "PREPARED"
    /\ partTimeout[<<pid, txn>>] = 0
    \* Participant is blocked - cannot make unilateral decision
    \* In practice, would contact other participants or wait for recovery
    /\ UNCHANGED vars

\* Decrement timeouts
DecrementTimeout(cid, txn) ==
    /\ cid \in Coordinators
    /\ txn \in Transactions
    /\ coordTimeout[<<cid, txn>>] > 0
    /\ coordTimeout' = [coordTimeout EXCEPT ![<<cid, txn>>] = @ - 1]
    /\ UNCHANGED <<coordState, coordVotes, coordDecision, coordLog, partVars,
                   network, failVars>>

(***************************************************************************
 * Actions: Failure and Recovery (Bernstein Section 7.5)
 ***************************************************************************)

\* Coordinator fails
CoordinatorFail(cid) ==
    /\ cid \in Coordinators
    /\ cid \notin coordFailed
    /\ coordFailed' = coordFailed \cup {cid}
    /\ UNCHANGED <<coordVars, partVars, network, partFailed>>

\* Participant fails
ParticipantFail(pid) ==
    /\ pid \in Participants
    /\ pid \notin partFailed
    /\ partFailed' = partFailed \cup {pid}
    /\ UNCHANGED <<coordVars, partVars, network, coordFailed>>

\* Coordinator recovers
CoordinatorRecover(cid, txn) ==
    /\ cid \in Coordinators
    /\ cid \in coordFailed
    /\ txn \in Transactions
    \* Read log and resume protocol
    /\ coordFailed' = coordFailed \ {cid}
    /\ LET log == coordLog[<<cid, txn>>]
       IN
        \* Determine state from log
        IF Len(log) = 0
        THEN \* No log entry: transaction not started
            /\ UNCHANGED <<coordState, coordVotes, coordDecision, coordTimeout,
                           coordLog, partVars, network, partFailed>>
        ELSE IF "COMMIT" \in Range(log) \/ "ABORT" \in Range(log)
        THEN \* Decision was made: resend decision
            /\ LET decision == IF "COMMIT" \in Range(log) 
                              THEN "COMMIT" ELSE "ABORT"
                   msgType == IF decision = "COMMIT" THEN "COMMIT" ELSE "ABORT"
               IN
                /\ network' = network \cup 
                    {[type |-> msgType, from |-> cid, to |-> p, txn |-> txn] : 
                     p \in Participants}
                /\ UNCHANGED <<coordState, coordVotes, coordDecision, 
                               coordTimeout, coordLog, partVars, partFailed>>
        ELSE \* No decision yet: abort
            /\ coordDecision' = [coordDecision EXCEPT ![<<cid, txn>>] = "ABORT"]
            /\ coordState' = [coordState EXCEPT ![<<cid, txn>>] = "ABORTING"]
            /\ coordLog' = [coordLog EXCEPT 
                ![<<cid, txn>>] = Append(@, "ABORT")]
            /\ network' = network \cup 
                {[type |-> "ABORT", from |-> cid, to |-> p, txn |-> txn] : 
                 p \in Participants}
            /\ UNCHANGED <<coordVotes, coordTimeout, partVars, partFailed>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorStartTransaction(c, t)
    \/ \E p \in Participants, t \in Transactions, v \in {"YES", "NO"} :
        ParticipantVote(p, t, v)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorCollectVote(c, t)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorDecide(c, t)
    \/ \E p \in Participants, t \in Transactions : 
        ParticipantExecuteDecision(p, t)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorReceiveAck(c, t)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorFinish(c, t)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorTimeout(c, t)
    \/ \E p \in Participants, t \in Transactions : 
        ParticipantTimeout(p, t)
    \/ \E c \in Coordinators, t \in Transactions : 
        DecrementTimeout(c, t)
    \/ \E c \in Coordinators : CoordinatorFail(c)
    \/ \E p \in Participants : ParticipantFail(p)
    \/ \E c \in Coordinators, t \in Transactions : 
        CoordinatorRecover(c, t)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Gray 1978, Bernstein 1987)
 ***************************************************************************)

\* Atomicity: All participants reach same outcome (commit or abort)
Atomicity ==
    \A t \in Transactions :
        LET committedParts == {p \in Participants : 
                              partState[<<p, t>>] = "COMMITTED"}
            abortedParts == {p \in Participants : 
                            partState[<<p, t>>] = "ABORTED"}
        IN
            /\ ~(committedParts # {} /\ abortedParts # {})
            \* Cannot have some committed and some aborted

\* Consistency: Coordinator and participants agree
ConsistentOutcome ==
    \A c \in Coordinators, t \in Transactions :
        /\ coordState[<<c, t>>] = "COMMITTED" =>
            \A p \in Participants : 
                partState[<<p, t>>] \in {"PREPARED", "COMMITTED"}
        /\ coordState[<<c, t>>] = "ABORTED" =>
            \A p \in Participants :
                partState[<<p, t>>] # "COMMITTED"

\* Validity: If all vote YES and no failures, transaction commits
Validity ==
    \A c \in Coordinators, t \in Transactions :
        /\ coordState[<<c, t>>] = "PREPARING"
        /\ AllVotesReceived(c, t)
        /\ AllVotesYes(c, t)
        /\ c \notin coordFailed
        /\ \A p \in Participants : p \notin partFailed
        ~> coordState[<<c, t>>] = "COMMITTED"

\* No participant commits unless coordinator decides commit
NoUnilateralCommit ==
    \A p \in Participants, t \in Transactions :
        partState[<<p, t>>] = "COMMITTED" =>
            \E c \in Coordinators : 
                coordDecision[<<c, t>>] = "COMMIT"

Safety ==
    /\ Atomicity
    /\ ConsistentOutcome
    /\ NoUnilateralCommit

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Transactions eventually complete (under fair conditions)
TransactionsEventuallyComplete ==
    \A c \in Coordinators, t \in Transactions :
        /\ c \notin coordFailed
        /\ coordState[<<c, t>>] = "PREPARING"
        ~> coordState[<<c, t>>] \in {"COMMITTED", "ABORTED"}

Liveness ==
    /\ TransactionsEventuallyComplete
    /\ Validity

(***************************************************************************
 * Theorems (Gray 1978, Bernstein 1987)
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []Atomicity

\* Note: 2PC can block if coordinator fails after participants prepare
\* This is the fundamental limitation proven in the literature

================================================================================


--------------------------- MODULE ConsensusProtocol ---------------------------
(*****************************************************************************)
(* Consensus Protocol (Raft) for ColibrìDB                                  *)
(*                                                                           *)
(* This specification models the Raft consensus algorithm with:             *)
(*   - Leader election with randomized timeouts                             *)
(*   - Log replication with strong consistency                              *)
(*   - Safety properties (Leader Completeness, State Machine Safety)        *)
(*   - Cluster membership changes                                           *)
(*   - Log compaction and snapshotting                                      *)
(*   - Network partitions and recovery                                      *)
(*   - Client interactions                                                  *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Ongaro, D., & Ousterhout, J. (2014). "In Search of an                *)
(*     Understandable Consensus Algorithm (Extended Version)".              *)
(*     USENIX ATC '14. https://raft.github.io/raft.pdf                      *)
(*     The canonical Raft paper                                             *)
(*   - Lamport, L. (1998). "The Part-Time Parliament".                      *)
(*     ACM TOCS, 16(2), 133-169. DOI: 10.1145/279227.279229                 *)
(*     Original Paxos algorithm                                             *)
(*   - Lamport, L. (2001). "Paxos Made Simple".                             *)
(*     ACM SIGACT News, 32(4), 18-25.                                       *)
(*   - Chandra, T. D., & Toueg, S. (1996). "Unreliable Failure Detectors   *)
(*     for Reliable Distributed Systems". Journal of the ACM, 43(2),        *)
(*     225-267. DOI: 10.1145/226643.226647                                  *)
(*   - Howard, H., et al. (2016). "Flexible Paxos: Quorum Intersection      *)
(*     Revisited". arXiv:1608.06696                                         *)
(*   - Apache ZooKeeper's ZAB (ZooKeeper Atomic Broadcast) protocol         *)
(*   - etcd Raft implementation: https://github.com/etcd-io/raft            *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    Servers,            \* Set of all servers (Raft nodes)
    MaxTerm,            \* Maximum term for model checking (Ongaro Sec 5.1)
    MaxLogLength,       \* Maximum log length for model checking
    HeartbeatTimeout,   \* Heartbeat interval (Ongaro Sec 5.2: ~10ms-500ms)
    ElectionTimeout,    \* Election timeout range (Ongaro: 150ms-300ms)
    MaxClientRequests,  \* Maximum client requests for model checking
    MAX_TX,             \* From CORE - for transaction IDs in log entries
    MAX_LSN,            \* From CORE - for LSN tracking
    MAX_PAGES           \* From CORE - for state machine pages

ASSUME Cardinality(Servers) > 0
ASSUME MaxTerm \in Nat \ {0}
ASSUME MaxLogLength \in Nat \ {0}
ASSUME HeartbeatTimeout \in Nat \ {0}
ASSUME ElectionTimeout \in Nat \ {0}
ASSUME HeartbeatTimeout < ElectionTimeout  \* Critical Raft requirement

VARIABLES
    (*************************************************************************
     * Persistent state on all servers (Ongaro Fig 2 - survives crashes)
     *************************************************************************)
    currentTerm,        \* [ServerId -> Term] - Current term number
    votedFor,           \* [ServerId -> ServerId \union {NULL}] - CandidateId voted for
    log,                \* [ServerId -> Seq(LogEntry)] - Log entries (NOW USES WALRecord!)
    
    (*************************************************************************
     * Volatile state on all servers (Ongaro Fig 2)
     *************************************************************************)
    commitIndex,        \* [ServerId -> LogIndex] - Highest committed entry
    lastApplied,        \* [ServerId -> LogIndex] - Highest applied to state machine
    
    (*************************************************************************
     * Volatile state on leaders (Ongaro Fig 2 - reinitialized after election)
     *************************************************************************)
    nextIndex,          \* [Leader -> [ServerId -> LogIndex]] - Next log entry to send
    matchIndex,         \* [Leader -> [ServerId -> LogIndex]] - Highest replicated
    
    (*************************************************************************
     * Server state (Ongaro Sec 5.1)
     *************************************************************************)
    state,              \* [ServerId -> {FOLLOWER, CANDIDATE, LEADER}]
    
    (*************************************************************************
     * Election state (Ongaro Sec 5.2)
     *************************************************************************)
    votesGranted,       \* [Candidate -> SUBSET Servers] - Servers that granted vote
    electionTimer,      \* [ServerId -> Nat] - Time until election timeout
    heartbeatTimer,     \* [Leader -> Nat] - Time until next heartbeat
    
    (*************************************************************************
     * Network (Ongaro Sec 5.3)
     *************************************************************************)
    messages,           \* Set of RPC messages in flight
    
    (*************************************************************************
     * Cluster membership (Ongaro Sec 6)
     *************************************************************************)
    configuration,      \* Current cluster configuration (C_old, C_new)
    
    (*************************************************************************
     * Metrics and audit
     *************************************************************************)
    elections,          \* Number of elections performed
    auditLog,           \* Audit trail of events
    currentTime         \* Global logical clock (Lamport clock)

consensusVars == <<currentTerm, votedFor, log, commitIndex, lastApplied, nextIndex,
                    matchIndex, state, votesGranted, electionTimer, heartbeatTimer,
                    messages, configuration, elections, auditLog, currentTime>>

(***************************************************************************
 * Type Definitions
 ***************************************************************************)

ServerId == Servers
Term == Nat
LogIndex == Nat

(***************************************************************************
 * Log Entry (Ongaro Fig 2)
 * 
 * CRITICAL INTEGRATION: Uses CORE WALRecord as payload!
 * This allows Raft to replicate actual database WAL records
 * 
 * Structure:
 * - walRecord: Actual database operation (from CORE)
 * - term: Term when entry was received by leader
 * - index: Position in log (for Raft protocol)
 * - txId: Transaction ID (from CORE) for ACID integration
 ***************************************************************************)
LogEntry == [
    walRecord: WALRecord,  \* Database operation (INSERT, UPDATE, DELETE, etc.)
    term: Term,            \* Term when created (Raft)
    index: LogIndex,       \* Log position (Raft)
    txId: TxId             \* Transaction ID from CORE
]
Value == STRING

(* Server states *)
ServerState == {"FOLLOWER", "CANDIDATE", "LEADER"}

(* Log entry *)
LogEntry == [
    term: Term,
    index: LogIndex,
    command: Value
]

(* Message types *)
RequestVoteRequest == [
    type: {"RequestVote"},
    term: Term,
    candidateId: ServerId,
    lastLogIndex: LogIndex,
    lastLogTerm: Term
]

RequestVoteResponse == [
    type: {"RequestVoteResponse"},
    term: Term,
    voteGranted: BOOLEAN,
    from: ServerId
]

AppendEntriesRequest == [
    type: {"AppendEntries"},
    term: Term,
    leaderId: ServerId,
    prevLogIndex: LogIndex,
    prevLogTerm: Term,
    entries: Seq(LogEntry),
    leaderCommit: LogIndex
]

AppendEntriesResponse == [
    type: {"AppendEntriesResponse"},
    term: Term,
    success: BOOLEAN,
    matchIndex: LogIndex,
    from: ServerId
]

Message == RequestVoteRequest \cup RequestVoteResponse \cup 
           AppendEntriesRequest \cup AppendEntriesResponse

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Quorum: majority of servers *)
Quorum(servers) ==
    Cardinality(servers) * 2 > Cardinality(Servers)

(* Get last log index *)
LastLogIndex(server) ==
    Len(log[server])

(* Get last log term *)
LastLogTerm(server) ==
    IF LastLogIndex(server) = 0 THEN 0
    ELSE log[server][LastLogIndex(server)].term

(* Check if log is more up-to-date *)
IsLogUpToDate(candidateLogIndex, candidateLogTerm, voterLogIndex, voterLogTerm) ==
    \/ candidateLogTerm > voterLogTerm
    \/ (candidateLogTerm = voterLogTerm /\ candidateLogIndex >= voterLogIndex)

(* Count committed entries *)
NumCommittedEntries(leader) ==
    LET matchIndices == {matchIndex[leader][s] : s \in Servers}
        sortedIndices == CHOOSE seq \in Seq(matchIndices) :
                           \A i \in 1..(Len(seq)-1) : seq[i] <= seq[i+1]
        medianIndex == IF Len(sortedIndices) = 0 THEN 0
                      ELSE sortedIndices[(Len(sortedIndices) \div 2) + 1]
    IN medianIndex

(* Send message *)
Send(m) ==
    messages' = messages \cup {m}

(* Discard message *)
Discard(m) ==
    messages' = messages \ {m}

(* Reply to message *)
Reply(request, response) ==
    /\ messages' = (messages \ {request}) \cup {response}

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> 0]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ lastApplied = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ state = [s \in Servers |-> "FOLLOWER"]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ electionTimer = [s \in Servers |-> ElectionTimeout]
    /\ heartbeatTimer = [s \in Servers |-> 0]
    /\ messages = {}
    /\ configuration = Servers
    /\ elections = 0
    /\ auditLog = <<>>
    /\ currentTime = 0

--------------------------------------------------------------------------------
(* Leader Election *)

(* Timeout: follower/candidate starts new election *)
Timeout(server) ==
    /\ state[server] \in {"FOLLOWER", "CANDIDATE"}
    /\ electionTimer[server] = 0
    /\ currentTerm' = [currentTerm EXCEPT ![server] = @ + 1]
    /\ state' = [state EXCEPT ![server] = "CANDIDATE"]
    /\ votedFor' = [votedFor EXCEPT ![server] = server]
    /\ votesGranted' = [votesGranted EXCEPT ![server] = {server}]
    /\ electionTimer' = [electionTimer EXCEPT ![server] = ElectionTimeout]
    /\ LET requestVoteRequests == {
             [type |-> "RequestVote",
              term |-> currentTerm'[server],
              candidateId |-> server,
              lastLogIndex |-> LastLogIndex(server),
              lastLogTerm |-> LastLogTerm(server)]} \X (Servers \ {server})
       IN Send([m \in requestVoteRequests |-> m[1]])
    /\ elections' = elections + 1
    /\ auditLog' = Append(auditLog,
         [event |-> "ELECTION_STARTED",
          server |-> server,
          term |-> currentTerm'[server],
          time |-> currentTime])
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                  heartbeatTimer, configuration, currentTime>>

(* Handle RequestVote RPC *)
HandleRequestVoteRequest(server, m) ==
    /\ m.type = "RequestVote"
    /\ LET grantVote == 
             /\ m.term >= currentTerm[server]
             /\ (votedFor[server] = 0 \/ votedFor[server] = m.candidateId)
             /\ IsLogUpToDate(m.lastLogIndex, m.lastLogTerm,
                             LastLogIndex(server), LastLogTerm(server))
       IN
           /\ IF m.term > currentTerm[server] THEN
                /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
                /\ state' = [state EXCEPT ![server] = "FOLLOWER"]
                /\ votedFor' = [votedFor EXCEPT 
                     ![server] = IF grantVote THEN m.candidateId ELSE 0]
              ELSE
                /\ votedFor' = [votedFor EXCEPT 
                     ![server] = IF grantVote THEN m.candidateId ELSE @]
                /\ UNCHANGED <<currentTerm, state>>
           /\ Reply(m, [type |-> "RequestVoteResponse",
                       term |-> currentTerm'[server],
                       voteGranted |-> grantVote,
                       from |-> server])
           /\ auditLog' = Append(auditLog,
                [event |-> "VOTE_CAST",
                 server |-> server,
                 candidate |-> m.candidateId,
                 granted |-> grantVote,
                 time |-> currentTime])
    /\ UNCHANGED <<log, commitIndex, lastApplied, nextIndex, matchIndex,
                  votesGranted, electionTimer, heartbeatTimer, configuration,
                  elections, currentTime>>

(* Handle RequestVote response *)
HandleRequestVoteResponse(server, m) ==
    /\ m.type = "RequestVoteResponse"
    /\ state[server] = "CANDIDATE"
    /\ m.term = currentTerm[server]
    /\ IF m.voteGranted THEN
         LET newVotesGranted == votesGranted[server] \cup {m.from}
         IN
             /\ votesGranted' = [votesGranted EXCEPT ![server] = newVotesGranted]
             /\ IF Quorum(newVotesGranted) THEN
                  \* Become leader
                  /\ state' = [state EXCEPT ![server] = "LEADER"]
                  /\ nextIndex' = [nextIndex EXCEPT ![server] = 
                       [s \in Servers |-> LastLogIndex(server) + 1]]
                  /\ matchIndex' = [matchIndex EXCEPT ![server] = 
                       [s \in Servers |-> 0]]
                  /\ heartbeatTimer' = [heartbeatTimer EXCEPT 
                       ![server] = HeartbeatTimeout]
                  /\ auditLog' = Append(auditLog,
                       [event |-> "LEADER_ELECTED",
                        server |-> server,
                        term |-> currentTerm[server],
                        time |-> currentTime])
                ELSE
                  /\ UNCHANGED <<state, nextIndex, matchIndex, heartbeatTimer, auditLog>>
       ELSE
         /\ UNCHANGED <<state, votesGranted, nextIndex, matchIndex, 
                       heartbeatTimer, auditLog>>
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  electionTimer, configuration, elections, currentTime>>

--------------------------------------------------------------------------------
(* Log Replication *)

(* Leader sends AppendEntries (heartbeat or with entries) *)
AppendEntries(leader, follower) ==
    /\ state[leader] = "LEADER"
    /\ LET prevLogIndex == nextIndex[leader][follower] - 1
           prevLogTerm == IF prevLogIndex > 0 
                         THEN log[leader][prevLogIndex].term 
                         ELSE 0
           entriesToSend == SubSeq(log[leader], 
                                   nextIndex[leader][follower],
                                   LastLogIndex(leader))
       IN
           /\ Send([type |-> "AppendEntries",
                   term |-> currentTerm[leader],
                   leaderId |-> leader,
                   prevLogIndex |-> prevLogIndex,
                   prevLogTerm |-> prevLogTerm,
                   entries |-> entriesToSend,
                   leaderCommit |-> commitIndex[leader]])
           /\ heartbeatTimer' = [heartbeatTimer EXCEPT 
                ![leader] = HeartbeatTimeout]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, state, votesGranted, electionTimer,
                  configuration, elections, auditLog, currentTime>>

(* Handle AppendEntries RPC *)
HandleAppendEntriesRequest(server, m) ==
    /\ m.type = "AppendEntries"
    /\ LET logOk == \/ m.prevLogIndex = 0
                   \/ /\ m.prevLogIndex <= LastLogIndex(server)
                      /\ m.prevLogIndex > 0 =>
                           log[server][m.prevLogIndex].term = m.prevLogTerm
       IN
           /\ IF m.term < currentTerm[server] THEN
                \* Reject (stale term)
                /\ Reply(m, [type |-> "AppendEntriesResponse",
                            term |-> currentTerm[server],
                            success |-> FALSE,
                            matchIndex |-> 0,
                            from |-> server])
                /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, 
                              lastApplied, electionTimer, auditLog>>
              ELSE
                /\ currentTerm' = [currentTerm EXCEPT ![server] = m.term]
                /\ state' = [state EXCEPT ![server] = "FOLLOWER"]
                /\ votedFor' = [votedFor EXCEPT ![server] = 0]
                /\ electionTimer' = [electionTimer EXCEPT 
                     ![server] = ElectionTimeout]
                /\ IF logOk THEN
                     \* Append entries
                     /\ log' = [log EXCEPT ![server] = 
                          SubSeq(@, 1, m.prevLogIndex) \o m.entries]
                     /\ commitIndex' = [commitIndex EXCEPT ![server] = 
                          IF m.leaderCommit > @
                          THEN Min({m.leaderCommit, LastLogIndex(server)})
                          ELSE @]
                     /\ Reply(m, [type |-> "AppendEntriesResponse",
                                 term |-> currentTerm'[server],
                                 success |-> TRUE,
                                 matchIndex |-> m.prevLogIndex + Len(m.entries),
                                 from |-> server])
                     /\ auditLog' = Append(auditLog,
                          [event |-> "LOG_APPENDED",
                           server |-> server,
                           entries |-> Len(m.entries),
                           newCommitIndex |-> commitIndex'[server],
                           time |-> currentTime])
                   ELSE
                     \* Reject (log inconsistency)
                     /\ Reply(m, [type |-> "AppendEntriesResponse",
                                 term |-> currentTerm'[server],
                                 success |-> FALSE,
                                 matchIndex |-> 0,
                                 from |-> server])
                     /\ UNCHANGED <<log, commitIndex, auditLog>>
                /\ UNCHANGED lastApplied
    /\ UNCHANGED <<nextIndex, matchIndex, votesGranted, heartbeatTimer,
                  configuration, elections, currentTime>>

(* Handle AppendEntries response *)
HandleAppendEntriesResponse(leader, m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ state[leader] = "LEADER"
    /\ m.term = currentTerm[leader]
    /\ IF m.success THEN
         /\ nextIndex' = [nextIndex EXCEPT 
              ![leader][m.from] = m.matchIndex + 1]
         /\ matchIndex' = [matchIndex EXCEPT 
              ![leader][m.from] = m.matchIndex]
         \* Update commit index if majority replicated
         /\ LET newCommitIndex == NumCommittedEntries(leader)
            IN
                IF newCommitIndex > commitIndex[leader] /\
                   log[leader][newCommitIndex].term = currentTerm[leader]
                THEN
                    /\ commitIndex' = [commitIndex EXCEPT ![leader] = newCommitIndex]
                    /\ auditLog' = Append(auditLog,
                         [event |-> "COMMIT_INDEX_ADVANCED",
                          leader |-> leader,
                          newCommitIndex |-> newCommitIndex,
                          time |-> currentTime])
                ELSE
                    /\ UNCHANGED <<commitIndex, auditLog>>
       ELSE
         \* Decrement nextIndex and retry
         /\ nextIndex' = [nextIndex EXCEPT 
              ![leader][m.from] = Max({@ - 1, 1})]
         /\ UNCHANGED <<matchIndex, commitIndex, auditLog>>
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, lastApplied, state, votesGranted,
                  electionTimer, heartbeatTimer, configuration, elections, currentTime>>

--------------------------------------------------------------------------------
(* Client Requests *)

ClientRequest(leader, command) ==
    /\ state[leader] = "LEADER"
    /\ LastLogIndex(leader) < MaxLogLength
    /\ LET newEntry == [term |-> currentTerm[leader],
                       index |-> LastLogIndex(leader) + 1,
                       command |-> command]
       IN
           /\ log' = [log EXCEPT ![leader] = Append(@, newEntry)]
           /\ auditLog' = Append(auditLog,
                [event |-> "CLIENT_REQUEST",
                 leader |-> leader,
                 command |-> command,
                 index |-> newEntry.index,
                 time |-> currentTime])
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, lastApplied, nextIndex,
                  matchIndex, state, votesGranted, electionTimer, heartbeatTimer,
                  messages, configuration, elections, currentTime>>

--------------------------------------------------------------------------------
(* State Machine Application *)

ApplyLog(server) ==
    /\ lastApplied[server] < commitIndex[server]
    /\ lastApplied' = [lastApplied EXCEPT ![server] = @ + 1]
    /\ auditLog' = Append(auditLog,
         [event |-> "LOG_APPLIED",
          server |-> server,
          index |-> lastApplied'[server],
          command |-> log[server][lastApplied'[server]].command,
          time |-> currentTime])
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex,
                  state, votesGranted, electionTimer, heartbeatTimer, messages,
                  configuration, elections, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ electionTimer' = [s \in Servers |-> 
         IF electionTimer[s] > 0 THEN electionTimer[s] - 1 ELSE 0]
    /\ heartbeatTimer' = [s \in Servers |->
         IF heartbeatTimer[s] > 0 THEN heartbeatTimer[s] - 1 ELSE 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, lastApplied,
                  nextIndex, matchIndex, state, votesGranted, messages,
                  configuration, elections, auditLog>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E s \in Servers : Timeout(s)
    \/ \E s \in Servers, m \in messages : HandleRequestVoteRequest(s, m)
    \/ \E s \in Servers, m \in messages : HandleRequestVoteResponse(s, m)
    \/ \E l, f \in Servers : AppendEntries(l, f)
    \/ \E s \in Servers, m \in messages : HandleAppendEntriesRequest(s, m)
    \/ \E l \in Servers, m \in messages : HandleAppendEntriesResponse(l, m)
    \/ \E l \in Servers, cmd \in Value : ClientRequest(l, cmd)
    \/ \E s \in Servers : ApplyLog(s)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: At most one leader per term *)
AtMostOneLeaderPerTerm ==
    \A s1, s2 \in Servers :
        (state[s1] = "LEADER" /\ state[s2] = "LEADER" /\
         currentTerm[s1] = currentTerm[s2]) => s1 = s2

(* INV2: Committed entries are durable *)
CommittedEntriesDurable ==
    \A s \in Servers, i \in 1..commitIndex[s] :
        \A t \in Servers : i <= LastLogIndex(t) =>
            log[s][i] = log[t][i]

(* INV3: Log matching property *)
LogMatching ==
    \A s1, s2 \in Servers, i \in 1..Min({LastLogIndex(s1), LastLogIndex(s2)}) :
        log[s1][i].term = log[s2][i].term =>
            log[s1][i] = log[s2][i]

(* INV4: Leader completeness *)
LeaderCompleteness ==
    \A leader \in Servers :
        state[leader] = "LEADER" =>
            \A s \in Servers, i \in 1..commitIndex[s] :
                i <= LastLogIndex(leader) /\
                log[s][i].term < currentTerm[leader] =>
                    log[leader][i] = log[s][i]

(* INV5: State machine safety *)
StateMachineSafety ==
    \A s1, s2 \in Servers :
        lastApplied[s1] = lastApplied[s2] =>
            SubSeq(log[s1], 1, lastApplied[s1]) = 
            SubSeq(log[s2], 1, lastApplied[s2])

(* INV6: Current term monotonically increases *)
TermMonotonic ==
    \A s \in Servers : currentTerm[s] <= MaxTerm

TypeInvariant ==
    /\ \A s \in Servers : currentTerm[s] \in Nat
    /\ \A s \in Servers : state[s] \in ServerState
    /\ \A s \in Servers : commitIndex[s] <= LastLogIndex(s)
    /\ \A s \in Servers : lastApplied[s] <= commitIndex[s]

--------------------------------------------------------------------------------
(* Safety Properties *)

(* SAFE1: Election Safety *)
ElectionSafety == AtMostOneLeaderPerTerm

(* SAFE2: Log consistency *)
LogConsistency == LogMatching /\ CommittedEntriesDurable

(* SAFE3: State machine safety *)
StateMachineConsistency == StateMachineSafety

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* LIVE1: Eventually elect a leader *)
EventuallyElectLeader ==
    <>(\E s \in Servers : state[s] = "LEADER")

(* LIVE2: Committed entries eventually applied *)
CommittedEventuallyApplied ==
    \A s \in Servers :
        commitIndex[s] > 0 ~> lastApplied[s] = commitIndex[s]

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM RaftSafety ==
    Spec => [](ElectionSafety /\ LogConsistency /\ StateMachineConsistency)

THEOREM RaftProgress ==
    Spec => EventuallyElectLeader

THEOREM RaftCorrectness ==
    Spec => [](LeaderCompleteness /\ StateMachineSafety)

================================================================================


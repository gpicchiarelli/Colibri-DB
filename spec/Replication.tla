------------------------------ MODULE Replication ------------------------------
(*****************************************************************************)
(* Database Replication for ColibrìDB                                       *)
(*                                                                           *)
(* This specification models database replication with:                     *)
(*   - Asynchronous replication (eventual consistency)                      *)
(*   - Synchronous replication (strong consistency)                         *)
(*   - Semi-synchronous replication                                         *)
(*   - Master-slave (primary-replica) architecture                          *)
(*   - Multi-master (active-active) replication                             *)
(*   - Cascading replication (slave->slave)                                 *)
(*   - Conflict detection and resolution                                    *)
(*   - Replication lag monitoring                                           *)
(*   - Failover and promotion                                               *)
(*   - Split-brain prevention                                               *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Bernstein, P. A., & Goodman, N. (1984). "An Algorithm for            *)
(*     Concurrency Control and Recovery in Replicated Distributed           *)
(*     Databases". ACM TODS, 9(4), 596-615. DOI: 10.1145/1994.2207          *)
(*   - Gray, J., Helland, P., O'Neil, P., & Shasha, D. (1996).              *)
(*     "The Dangers of Replication and a Solution". SIGMOD'96, pp. 173-182. *)
(*     DOI: 10.1145/233269.233330                                           *)
(*   - Saito, Y., & Shapiro, M. (2005). "Optimistic Replication".           *)
(*     ACM Computing Surveys, 37(1), 42-81. DOI: 10.1145/1057977.1057980    *)
(*   - Vogels, W. (2009). "Eventually Consistent". CACM, 52(1), 40-44.      *)
(*     DOI: 10.1145/1435417.1435432                                         *)
(*   - Brewer, E. (2012). "CAP Twelve Years Later: How the Rules Have       *)
(*     Changed". IEEE Computer, 45(2), 23-29. DOI: 10.1109/MC.2012.37      *)
(*   - Corbett, J. C., et al. (2013). "Spanner: Google's Globally-          *)
(*     Distributed Database". ACM TOCS, 31(3), Article 8.                   *)
(*     DOI: 10.1145/2491245                                                 *)
(*   - PostgreSQL Streaming Replication Documentation                        *)
(*   - MySQL Group Replication and InnoDB Cluster Documentation             *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    Nodes,              \* Set of all database nodes
    MaxReplicas,        \* Maximum number of replicas
    MaxReplicationLag,  \* Maximum acceptable replication lag (in LSN units)
    QuorumSize,         \* Quorum size for synchronous replication
    ConflictResolution, \* Conflict resolution strategy
    MAX_TX,             \* From CORE - for transaction IDs
    MAX_LSN,            \* From CORE - for LSN bounds
    MAX_PAGES           \* From CORE - for page replication

ASSUME Cardinality(Nodes) > 0
ASSUME MaxReplicas \in Nat \ {0}
ASSUME MaxReplicationLag \in Nat
ASSUME QuorumSize \in Nat \ {0}
ASSUME QuorumSize <= Cardinality(Nodes)

VARIABLES
    nodeState,          \* [NodeId -> [role, status, data, lsn: LSN, connected]]
    replicationStreams, \* Set of active replication streams
    replicationLog,     \* Seq(WALRecord) - Uses CORE WALRecord type!
    acknowledgments,    \* [NodeId -> LSN] - Last ack'd LSN from each node
    conflicts,          \* Set of detected conflicts
    topology,           \* Replication topology graph
    failoverState,      \* Failover/promotion state machine
    splitBrainToken,    \* Token for split-brain prevention (Paxos-based)
    metrics,            \* [NodeId -> [lag: LSN, throughput: Nat]]
    auditLog,           \* Seq of replication events
    currentTime         \* Global logical clock (Nat)

replicationVars == <<nodeState, replicationStreams, replicationLog, acknowledgments,
                      conflicts, topology, failoverState, splitBrainToken, metrics,
                      auditLog, currentTime>>

(***************************************************************************
 * Type Definitions
 ***************************************************************************)

NodeId == Nodes
\* LSN imported from CORE, not redefined
ChangeId == Nat

(* Node roles *)
NodeRole == {"PRIMARY", "REPLICA", "STANDBY", "WITNESS"}

(* Node status *)
NodeStatus == {"ONLINE", "OFFLINE", "SYNCING", "LAGGING", "FAILED"}

(* Replication modes *)
ReplicationMode == {"ASYNC", "SYNC", "SEMI_SYNC"}

(* Replication stream *)
ReplicationStream == [
    id: Nat,
    source: NodeId,
    target: NodeId,
    mode: ReplicationMode,
    status: {"ACTIVE", "PAUSED", "BROKEN"},
    lastAckLSN: LSN,
    lag: Nat
]

(***************************************************************************
 * Change Record - Uses CORE WALRecord as base
 * Extended with replication-specific metadata
 ***************************************************************************)
ChangeRecord == [
    walRecord: WALRecord,       \* Base WAL record from CORE
    id: ChangeId,               \* Unique change identifier
    originNode: NodeId,         \* Node where change originated
    timestamp: Timestamp,       \* From CORE
    causality: SUBSET ChangeId  \* Causal dependencies (Saito & Shapiro 2005)
]

(* Conflict types *)
ConflictType == {
    "UPDATE_UPDATE",    \* Concurrent updates to same object
    "UPDATE_DELETE",    \* Update vs delete conflict
    "DELETE_DELETE",    \* Redundant deletes
    "UNIQUE_VIOLATION"  \* Uniqueness constraint violation
}

(* Conflict resolution strategies *)
ResolutionStrategy == {
    "LAST_WRITE_WINS",          \* Timestamp-based
    "FIRST_WRITE_WINS",         \* First commit wins
    "PRIMARY_WINS",             \* Primary always wins
    "REPLICA_WINS",             \* Replica always wins
    "MANUAL",                   \* Require manual intervention
    "MERGE",                    \* Automatic merge
    "CUSTOM"                    \* Application-defined
}

(* Failover state *)
FailoverState == [
    inProgress: BOOLEAN,
    oldPrimary: NodeId \cup {0},
    newPrimary: NodeId \cup {0},
    initiatedAt: Nat,
    votes: [NodeId -> BOOLEAN]
]

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ nodeState = [n \in Nodes |-> 
         [role |-> IF n = CHOOSE node \in Nodes : TRUE 
                   THEN "PRIMARY" ELSE "REPLICA",
          status |-> "ONLINE",
          data |-> <<>>,
          lsn |-> 0,
          connected |-> Nodes \ {n}]]
    /\ replicationStreams = {}
    /\ replicationLog = <<>>
    /\ acknowledgments = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ conflicts = {}
    /\ topology = [source \in Nodes |-> 
         IF nodeState[source].role = "PRIMARY" 
         THEN {n \in Nodes : n # source} 
         ELSE {}]
    /\ failoverState = [inProgress |-> FALSE, oldPrimary |-> 0, 
                       newPrimary |-> 0, initiatedAt |-> 0,
                       votes |-> [n \in Nodes |-> FALSE]]
    /\ splitBrainToken = CHOOSE n \in Nodes : nodeState[n].role = "PRIMARY"
    /\ metrics = [totalChanges |-> 0, conflictsDetected |-> 0,
                 avgLag |-> 0, failovers |-> 0]
    /\ auditLog = <<>>
    /\ currentTime = 0

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Get primary node *)
GetPrimary ==
    CHOOSE n \in Nodes : nodeState[n].role = "PRIMARY"

(* Get all replicas *)
GetReplicas ==
    {n \in Nodes : nodeState[n].role = "REPLICA"}

(* Check if node is up-to-date *)
IsUpToDate(node, lsn) ==
    nodeState[node].lsn >= lsn

(* Calculate replication lag *)
ReplicationLag(source, target) ==
    nodeState[source].lsn - nodeState[target].lsn

(* Check quorum *)
HasQuorum(nodes) ==
    Cardinality(nodes) >= QuorumSize

(* Detect conflicts between two changes *)
HasConflict(change1, change2) ==
    /\ change1.id # change2.id
    /\ change1.data = change2.data  \* Same object
    /\ change1.id \notin change2.causality
    /\ change2.id \notin change1.causality

(* Resolve conflict based on strategy *)
ResolveConflict(change1, change2, strategy) ==
    CASE strategy = "LAST_WRITE_WINS" ->
           IF change1.timestamp > change2.timestamp 
           THEN change1 ELSE change2
      [] strategy = "FIRST_WRITE_WINS" ->
           IF change1.timestamp < change2.timestamp 
           THEN change1 ELSE change2
      [] strategy = "PRIMARY_WINS" ->
           IF change1.node = GetPrimary 
           THEN change1 ELSE change2
      [] OTHER -> change1

(* Check for split-brain *)
HasSplitBrain ==
    Cardinality({n \in Nodes : nodeState[n].role = "PRIMARY"}) > 1

--------------------------------------------------------------------------------
(* Primary Operations *)

(* Write on primary *)
PrimaryWrite(operation, data) ==
    /\ LET primary == GetPrimary
       IN
           /\ nodeState[primary].status = "ONLINE"
           /\ LET changeId == Len(replicationLog) + 1
                  lsn == nodeState[primary].lsn + 1
                  change == [
                      id |-> changeId,
                      lsn |-> lsn,
                      node |-> primary,
                      operation |-> operation,
                      data |-> data,
                      timestamp |-> currentTime,
                      causality |-> {}
                  ]
              IN
                  /\ replicationLog' = Append(replicationLog, change)
                  /\ nodeState' = [nodeState EXCEPT
                       ![primary].lsn = lsn,
                       ![primary].data = Append(@, data)]
                  /\ metrics' = [metrics EXCEPT !.totalChanges = @ + 1]
                  /\ auditLog' = Append(auditLog,
                       [event |-> "PRIMARY_WRITE",
                        node |-> primary,
                        changeId |-> changeId,
                        time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, acknowledgments, conflicts, topology,
                  failoverState, splitBrainToken, currentTime>>

--------------------------------------------------------------------------------
(* Asynchronous Replication *)

ReplicateAsync(source, target) ==
    /\ nodeState[source].role \in {"PRIMARY", "REPLICA"}
    /\ nodeState[target].role \in {"REPLICA", "STANDBY"}
    /\ nodeState[source].status = "ONLINE"
    /\ nodeState[target].status = "ONLINE"
    /\ target \in topology[source]
    /\ nodeState[source].lsn > nodeState[target].lsn
    /\ LET targetLSN == nodeState[target].lsn
           changes == {replicationLog[i] : i \in DOMAIN replicationLog /\
                      replicationLog[i].lsn > targetLSN /\
                      replicationLog[i].lsn <= nodeState[source].lsn}
       IN
           /\ changes # {}
           /\ LET change == CHOOSE c \in changes : 
                    \A other \in changes : other.lsn >= c.lsn
              IN
                  /\ nodeState' = [nodeState EXCEPT
                       ![target].lsn = change.lsn,
                       ![target].data = Append(@, change.data)]
                  /\ acknowledgments' = [acknowledgments EXCEPT
                       ![target][source] = change.lsn]
                  /\ auditLog' = Append(auditLog,
                       [event |-> "ASYNC_REPLICATE",
                        source |-> source,
                        target |-> target,
                        lsn |-> change.lsn,
                        time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, conflicts, topology,
                  failoverState, splitBrainToken, metrics, currentTime>>

--------------------------------------------------------------------------------
(* Synchronous Replication *)

ReplicateSync(source, replicas) ==
    /\ nodeState[source].role = "PRIMARY"
    /\ nodeState[source].status = "ONLINE"
    /\ replicas \subseteq GetReplicas
    /\ HasQuorum(replicas)
    /\ \A r \in replicas : nodeState[r].status = "ONLINE"
    /\ LET sourceLSN == nodeState[source].lsn
       IN
           \* Wait for all replicas in quorum to acknowledge
           /\ \A r \in replicas : acknowledgments[r][source] >= sourceLSN - 1
           /\ nodeState' = [n \in Nodes |->
                IF n \in replicas
                THEN [nodeState[n] EXCEPT !.lsn = sourceLSN]
                ELSE nodeState[n]]
           /\ auditLog' = Append(auditLog,
                [event |-> "SYNC_REPLICATE",
                 source |-> source,
                 replicas |-> replicas,
                 lsn |-> sourceLSN,
                 time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, acknowledgments, conflicts,
                  topology, failoverState, splitBrainToken, metrics, currentTime>>

--------------------------------------------------------------------------------
(* Semi-Synchronous Replication *)

ReplicateSemiSync(source, target) ==
    /\ nodeState[source].role = "PRIMARY"
    /\ nodeState[target].role = "REPLICA"
    /\ target \in topology[source]
    /\ nodeState[source].lsn > nodeState[target].lsn
    /\ LET sourceLSN == nodeState[source].lsn
       IN
           \* At least one replica must acknowledge before returning
           /\ acknowledgments[target][source] >= sourceLSN - 1
           /\ nodeState' = [nodeState EXCEPT
                ![target].lsn = sourceLSN]
           /\ auditLog' = Append(auditLog,
                [event |-> "SEMI_SYNC_REPLICATE",
                 source |-> source,
                 target |-> target,
                 lsn |-> sourceLSN,
                 time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, acknowledgments, conflicts,
                  topology, failoverState, splitBrainToken, metrics, currentTime>>

--------------------------------------------------------------------------------
(* Multi-Master Replication *)

ReplicaWrite(replica, operation, data) ==
    /\ nodeState[replica].role = "REPLICA"
    /\ nodeState[replica].status = "ONLINE"
    /\ LET changeId == Len(replicationLog) + 1
           lsn == nodeState[replica].lsn + 1
           change == [
               id |-> changeId,
               lsn |-> lsn,
               node |-> replica,
               operation |-> operation,
               data |-> data,
               timestamp |-> currentTime,
               causality |-> {}
           ]
       IN
           /\ replicationLog' = Append(replicationLog, change)
           /\ nodeState' = [nodeState EXCEPT
                ![replica].lsn = lsn,
                ![replica].data = Append(@, data)]
           \* Detect conflicts
           /\ conflicts' = conflicts \cup
                {[type |-> "UPDATE_UPDATE",
                  change1 |-> change,
                  change2 |-> other,
                  detected |-> currentTime] :
                 other \in {replicationLog[i] : i \in DOMAIN replicationLog /\
                           HasConflict(change, replicationLog[i])}}
           /\ IF conflicts' # conflicts
              THEN metrics' = [metrics EXCEPT !.conflictsDetected = @ + 1]
              ELSE metrics' = metrics
           /\ auditLog' = Append(auditLog,
                [event |-> "REPLICA_WRITE",
                 node |-> replica,
                 changeId |-> changeId,
                 conflicts |-> Cardinality(conflicts') - Cardinality(conflicts),
                 time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, acknowledgments, topology, failoverState,
                  splitBrainToken, currentTime>>

--------------------------------------------------------------------------------
(* Conflict Resolution *)

ResolveConflict(conflictId) ==
    /\ \E conflict \in conflicts :
         /\ LET resolved == ResolveConflict(conflict.change1, conflict.change2,
                                           ConflictResolution)
            IN
                /\ conflicts' = conflicts \ {conflict}
                /\ auditLog' = Append(auditLog,
                     [event |-> "CONFLICT_RESOLVED",
                      conflictId |-> conflictId,
                      strategy |-> ConflictResolution,
                      winner |-> resolved,
                      time |-> currentTime])
    /\ UNCHANGED <<nodeState, replicationStreams, replicationLog, acknowledgments,
                  topology, failoverState, splitBrainToken, metrics, currentTime>>

--------------------------------------------------------------------------------
(* Failover *)

InitiateFailover(failedNode, newPrimary) ==
    /\ nodeState[failedNode].role = "PRIMARY"
    /\ nodeState[failedNode].status = "FAILED"
    /\ nodeState[newPrimary].role = "REPLICA"
    /\ nodeState[newPrimary].status = "ONLINE"
    /\ ~failoverState.inProgress
    /\ IsUpToDate(newPrimary, nodeState[failedNode].lsn)
    /\ failoverState' = [
         inProgress |-> TRUE,
         oldPrimary |-> failedNode,
         newPrimary |-> newPrimary,
         initiatedAt |-> currentTime,
         votes |-> [n \in Nodes |-> FALSE]]
    /\ auditLog' = Append(auditLog,
         [event |-> "FAILOVER_INITIATED",
          failedNode |-> failedNode,
          newPrimary |-> newPrimary,
          time |-> currentTime])
    /\ UNCHANGED <<nodeState, replicationStreams, replicationLog, acknowledgments,
                  conflicts, topology, splitBrainToken, metrics, currentTime>>

VoteForFailover(voter, candidate) ==
    /\ failoverState.inProgress
    /\ failoverState.newPrimary = candidate
    /\ ~failoverState.votes[voter]
    /\ nodeState[voter].status = "ONLINE"
    /\ failoverState' = [failoverState EXCEPT !.votes[voter] = TRUE]
    /\ auditLog' = Append(auditLog,
         [event |-> "FAILOVER_VOTE",
          voter |-> voter,
          candidate |-> candidate,
          time |-> currentTime])
    /\ UNCHANGED <<nodeState, replicationStreams, replicationLog, acknowledgments,
                  conflicts, topology, splitBrainToken, metrics, currentTime>>

CompleteFailover ==
    /\ failoverState.inProgress
    /\ LET votes == {n \in Nodes : failoverState.votes[n]}
       IN HasQuorum(votes)
    /\ LET oldPrimary == failoverState.oldPrimary
           newPrimary == failoverState.newPrimary
       IN
           /\ nodeState' = [n \in Nodes |->
                IF n = newPrimary
                THEN [nodeState[n] EXCEPT !.role = "PRIMARY"]
                ELSE IF n = oldPrimary
                THEN [nodeState[n] EXCEPT !.role = "STANDBY"]
                ELSE nodeState[n]]
           /\ topology' = [source \in Nodes |->
                IF source = newPrimary
                THEN Nodes \ {newPrimary}
                ELSE IF source = oldPrimary
                THEN {}
                ELSE topology[source]]
           /\ splitBrainToken' = newPrimary
           /\ failoverState' = [failoverState EXCEPT !.inProgress = FALSE]
           /\ metrics' = [metrics EXCEPT !.failovers = @ + 1]
           /\ auditLog' = Append(auditLog,
                [event |-> "FAILOVER_COMPLETED",
                 oldPrimary |-> oldPrimary,
                 newPrimary |-> newPrimary,
                 time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, acknowledgments, conflicts,
                  currentTime>>

--------------------------------------------------------------------------------
(* Node Failure and Recovery *)

NodeFail(node) ==
    /\ nodeState[node].status = "ONLINE"
    /\ nodeState' = [nodeState EXCEPT ![node].status = "FAILED"]
    /\ auditLog' = Append(auditLog,
         [event |-> "NODE_FAILED",
          node |-> node,
          time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, acknowledgments, conflicts,
                  topology, failoverState, splitBrainToken, metrics, currentTime>>

NodeRecover(node) ==
    /\ nodeState[node].status = "FAILED"
    /\ nodeState' = [nodeState EXCEPT ![node].status = "SYNCING"]
    /\ auditLog' = Append(auditLog,
         [event |-> "NODE_RECOVERING",
          node |-> node,
          time |-> currentTime])
    /\ UNCHANGED <<replicationStreams, replicationLog, acknowledgments, conflicts,
                  topology, failoverState, splitBrainToken, metrics, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<nodeState, replicationStreams, replicationLog, acknowledgments,
                  conflicts, topology, failoverState, splitBrainToken, metrics,
                  auditLog>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E op, data \in STRING : PrimaryWrite(op, data)
    \/ \E source, target \in Nodes : ReplicateAsync(source, target)
    \/ \E source \in Nodes, reps \in SUBSET Nodes : ReplicateSync(source, reps)
    \/ \E source, target \in Nodes : ReplicateSemiSync(source, target)
    \/ \E replica \in Nodes, op, data \in STRING : ReplicaWrite(replica, op, data)
    \/ \E cid \in Nat : ResolveConflict(cid)
    \/ \E failed, new \in Nodes : InitiateFailover(failed, new)
    \/ \E voter, candidate \in Nodes : VoteForFailover(voter, candidate)
    \/ CompleteFailover
    \/ \E node \in Nodes : NodeFail(node)
    \/ \E node \in Nodes : NodeRecover(node)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: At most one primary at a time (no split-brain) *)
SinglePrimary ==
    Cardinality({n \in Nodes : nodeState[n].role = "PRIMARY"}) <= 1

(* INV2: All replicas lag behind or equal to primary *)
ReplicasBehindPrimary ==
    LET primary == GetPrimary
    IN \A replica \in GetReplicas :
         nodeState[replica].lsn <= nodeState[primary].lsn

(* INV3: Acknowledgments don't exceed node LSN *)
AcknowledgmentsValid ==
    \A source, target \in Nodes :
        acknowledgments[target][source] <= nodeState[target].lsn

(* INV4: Replication lag within bounds for online nodes *)
ReplicationLagBounded ==
    LET primary == GetPrimary
    IN \A replica \in GetReplicas :
         nodeState[replica].status = "ONLINE" =>
           ReplicationLag(primary, replica) <= MaxReplicationLag

(* INV5: Split-brain token belongs to current primary *)
SplitBrainTokenValid ==
    splitBrainToken = GetPrimary

TypeInvariant ==
    /\ DOMAIN nodeState = Nodes
    /\ currentTime \in Nat
    /\ \A n \in Nodes : nodeState[n].role \in NodeRole

--------------------------------------------------------------------------------
(* Safety Properties *)

(* SAFE1: No split-brain scenarios *)
NoSplitBrain ==
    ~HasSplitBrain

(* SAFE2: Data consistency across replicas (eventual) *)
EventualConsistency ==
    \A n1, n2 \in Nodes :
        (nodeState[n1].status = "ONLINE" /\ nodeState[n2].status = "ONLINE") =>
          (nodeState[n1].lsn = nodeState[n2].lsn => 
            nodeState[n1].data = nodeState[n2].data)

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* LIVE1: Replicas eventually catch up *)
ReplicasEventuallyCatchUp ==
    \A replica \in GetReplicas :
        nodeState[replica].status = "ONLINE" ~>
          (nodeState[replica].lsn = nodeState[GetPrimary].lsn)

(* LIVE2: Failover eventually completes *)
FailoverEventuallyCompletes ==
    failoverState.inProgress ~> ~failoverState.inProgress

(* LIVE3: Conflicts eventually get resolved *)
ConflictsEventuallyResolved ==
    Cardinality(conflicts) > 0 ~> Cardinality(conflicts) = 0

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM ReplicationSafety ==
    Spec => [](SinglePrimary /\ NoSplitBrain)

THEOREM ReplicationConsistency ==
    Spec => [](ReplicasBehindPrimary /\ AcknowledgmentsValid)

THEOREM ReplicationProgress ==
    Spec => (ReplicasEventuallyCatchUp /\ FailoverEventuallyCompletes)

================================================================================


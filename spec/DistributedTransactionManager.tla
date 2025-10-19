----------------------------- MODULE DistributedTransactionManager -----------------------------
(*
  Distributed Transaction Manager Bridge Module
  
  This bridge module integrates distributed transaction components:
  - TransactionManager: Local ACID transaction management
  - TwoPhaseCommit: Distributed commit protocol
  - Replication: Data replication across nodes
  - ConsensusProtocol: Raft consensus for consistency
  - Clock: Distributed timestamp oracle
  
  Purpose:
  Provides formally verified distributed ACID transactions with:
  - Atomic commit across multiple nodes
  - Strong consistency via Raft
  - Fault tolerance via replication
  - Snapshot isolation with distributed timestamps
  
  Cross-Module Invariants:
  1. Distributed Atomicity: All nodes commit or all abort
  2. Replication Consistency: All replicas converge to same state
  3. Consensus Safety: Only one leader per term
  4. Timestamp Monotonicity: Timestamps increase across commits
  
  Based on:
  - Gray, J. (1978). "Notes on Data Base Operating Systems"
  - Ongaro, D., & Ousterhout, J. (2014). "In Search of an Understandable
    Consensus Algorithm" (Raft - USENIX ATC)
  - Corbett, J. C., et al. (2013). "Spanner: Google's Globally Distributed
    Database" (ACM TOCS)
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS CORE, TransactionManager, TwoPhaseCommit, Replication, ConsensusProtocol, Clock

CONSTANTS
  Nodes,              \* Set of database nodes
  CoordinatorNode,    \* Current transaction coordinator
  ReplicationFactor   \* Number of replicas per data item

(* --------------------------------------------------------------------------
   BRIDGE VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Distributed transaction state
  distributedTx,         \* [TxId -> [coord, participants, status, ts]]
  preparedNodes,         \* [TxId -> SUBSET Nodes] - Nodes that voted YES
  commitDecisions,       \* [TxId -> [decision, term]] - Commit decisions via Raft
  
  \* Replication state per node
  nodeReplicas,          \* [Node -> [TxId -> Data]] - Replicated data per node
  replicationLag,        \* [Node -> LSN] - Replication lag per node
  
  \* Fault tolerance
  aliveNodes,            \* SUBSET Nodes - Currently alive nodes
  partitionedNodes       \* SUBSET Nodes - Nodes in network partition

dtmVars == <<distributedTx, preparedNodes, commitDecisions, nodeReplicas,
             replicationLag, aliveNodes, partitionedNodes>>

allVars == <<tmVars, tpcVars, replicationVars, raftVars, clockVars, dtmVars>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_DTM ==
  /\ TypeOK_TM              \* TransactionManager types
  /\ TypeOK_TPC             \* TwoPhaseCommit types
  /\ TypeOK_Replication     \* Replication types
  /\ TypeOK_Raft            \* ConsensusProtocol types
  /\ TypeOK_Clock           \* Clock types
  /\ distributedTx \in [TxIds -> [
       coordinator: Nodes,
       participants: SUBSET Nodes,
       status: {"preparing", "prepared", "committed", "aborted"},
       commitTS: Nat
     ]]
  /\ preparedNodes \in [TxIds -> SUBSET Nodes]
  /\ commitDecisions \in [TxIds -> [decision: {"commit", "abort"}, term: Nat]]
  /\ nodeReplicas \in [Nodes -> [TxIds -> STRING]]
  /\ replicationLag \in [Nodes -> Nat]
  /\ aliveNodes \in SUBSET Nodes
  /\ partitionedNodes \in SUBSET Nodes

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_DTM ==
  /\ Init_TM
  /\ Init_TPC
  /\ Init_Replication
  /\ Init_Raft
  /\ Init_Clock
  /\ distributedTx = [tid \in TxIds |-> 
       [coordinator |-> CoordinatorNode,
        participants |-> {},
        status |-> "preparing",
        commitTS |-> 0]]
  /\ preparedNodes = [tid \in TxIds |-> {}]
  /\ commitDecisions = [tid \in TxIds |-> [decision |-> "abort", term |-> 0]]
  /\ nodeReplicas = [n \in Nodes |-> [tid \in TxIds |-> ""]]
  /\ replicationLag = [n \in Nodes |-> 0]
  /\ aliveNodes = Nodes
  /\ partitionedNodes = {}

(* --------------------------------------------------------------------------
   DISTRIBUTED TRANSACTION OPERATIONS
   -------------------------------------------------------------------------- *)

\* Begin a distributed transaction
BeginDistributedTx(tid, participantNodes) ==
  /\ CoordinatorNode \in aliveNodes
  /\ participantNodes \subseteq aliveNodes
  /\ BeginTransaction(tid, "serializable", TRUE)  \* distributed = TRUE
  /\ distributedTx' = [distributedTx EXCEPT 
       ![tid].participants = participantNodes,
       ![tid].status = "preparing"]
  /\ RequestTimestamp(tid)  \* Get global timestamp from Clock
  /\ UNCHANGED <<preparedNodes, commitDecisions, nodeReplicas, 
                replicationLag, aliveNodes, partitionedNodes>>

\* Phase 1: Prepare - Ask all participants to prepare
PrepareDistributedTx(tid) ==
  /\ distributedTx[tid].status = "preparing"
  /\ distributedTx[tid].coordinator \in aliveNodes
  /\ \A node \in distributedTx[tid].participants: node \in aliveNodes
  /\ TPC_Prepare(tid)  \* Send PREPARE to all participants
  /\ preparedNodes' = [preparedNodes EXCEPT ![tid] = 
       {n \in distributedTx[tid].participants: TPC_VoteYes(n, tid)}]
  /\ IF Cardinality(preparedNodes'[tid]) = Cardinality(distributedTx[tid].participants)
     THEN distributedTx' = [distributedTx EXCEPT ![tid].status = "prepared"]
     ELSE distributedTx' = [distributedTx EXCEPT ![tid].status = "aborted"]
  /\ UNCHANGED <<commitDecisions, nodeReplicas, replicationLag, 
                aliveNodes, partitionedNodes>>

\* Phase 2: Commit Decision via Raft Consensus
CommitDecisionViaRaft(tid) ==
  /\ distributedTx[tid].status = "prepared"
  /\ LET decision == IF Cardinality(preparedNodes[tid]) = 
                         Cardinality(distributedTx[tid].participants)
                     THEN "commit"
                     ELSE "abort"
         leaderNode == GetRaftLeader()
     IN /\ leaderNode \in aliveNodes
        /\ Raft_AppendEntry([
             index |-> nextLogIndex,
             term |-> currentTerm,
             command |-> [type |-> "COMMIT_DECISION", txId |-> tid, decision |-> decision]
           ])
        /\ commitDecisions' = [commitDecisions EXCEPT ![tid] = 
             [decision |-> decision, term |-> currentTerm]]
        /\ UNCHANGED <<distributedTx, preparedNodes, nodeReplicas,
                      replicationLag, aliveNodes, partitionedNodes>>

\* Phase 3: Execute Commit/Abort based on Raft decision
ExecuteDistributedCommit(tid) ==
  /\ commitDecisions[tid].decision = "commit"
  /\ distributedTx[tid].status = "prepared"
  /\ LET commitTS == GetCommitTimestamp(tid)
     IN /\ CommitTransaction(tid)  \* Local commit on coordinator
        /\ distributedTx' = [distributedTx EXCEPT 
             ![tid].status = "committed",
             ![tid].commitTS = commitTS]
        /\ \* Replicate to all participants
           \A node \in distributedTx[tid].participants:
             Replicate_Data(node, tid, commitTS)
        /\ nodeReplicas' = [n \in Nodes |-> 
             IF n \in distributedTx[tid].participants
             THEN [nodeReplicas[n] EXCEPT ![tid] = "committed_data"]
             ELSE nodeReplicas[n]]
        /\ UNCHANGED <<preparedNodes, commitDecisions, replicationLag,
                      aliveNodes, partitionedNodes>>

ExecuteDistributedAbort(tid) ==
  /\ commitDecisions[tid].decision = "abort" \/ distributedTx[tid].status = "aborted"
  /\ AbortTransaction(tid)
  /\ distributedTx' = [distributedTx EXCEPT ![tid].status = "aborted"]
  /\ UNCHANGED <<preparedNodes, commitDecisions, nodeReplicas,
                replicationLag, aliveNodes, partitionedNodes>>

\* Replication lag monitoring
UpdateReplicationLag(node) ==
  /\ node \in aliveNodes
  /\ LET currentLSN == GetNodeLSN(node)
         leaderLSN == GetLeaderLSN()
     IN replicationLag' = [replicationLag EXCEPT ![node] = leaderLSN - currentLSN]
  /\ UNCHANGED <<distributedTx, preparedNodes, commitDecisions, nodeReplicas,
                aliveNodes, partitionedNodes>>

(* --------------------------------------------------------------------------
   FAULT HANDLING
   -------------------------------------------------------------------------- *)

\* Node failure
NodeFailure(node) ==
  /\ node \in aliveNodes
  /\ aliveNodes' = aliveNodes \ {node}
  /\ \* Abort all transactions where this node is coordinator
     distributedTx' = [tid \in TxIds |->
       IF distributedTx[tid].coordinator = node /\ distributedTx[tid].status # "committed"
       THEN [distributedTx[tid] EXCEPT !.status = "aborted"]
       ELSE distributedTx[tid]]
  /\ UNCHANGED <<preparedNodes, commitDecisions, nodeReplicas,
                replicationLag, partitionedNodes>>

\* Node recovery
NodeRecovery(node) ==
  /\ node \notin aliveNodes
  /\ aliveNodes' = aliveNodes \union {node}
  /\ \* Catch up replication
     Replicate_CatchUp(node)
  /\ UNCHANGED <<distributedTx, preparedNodes, commitDecisions,
                replicationLag, partitionedNodes>>

\* Network partition
NetworkPartition(partition) ==
  /\ partition \subseteq Nodes
  /\ partitionedNodes' = partition
  /\ UNCHANGED <<distributedTx, preparedNodes, commitDecisions, nodeReplicas,
                replicationLag, aliveNodes>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_DTM ==
  \/ \E tid \in TxIds, nodes \in SUBSET Nodes: BeginDistributedTx(tid, nodes)
  \/ \E tid \in TxIds: PrepareDistributedTx(tid)
  \/ \E tid \in TxIds: CommitDecisionViaRaft(tid)
  \/ \E tid \in TxIds: ExecuteDistributedCommit(tid)
  \/ \E tid \in TxIds: ExecuteDistributedAbort(tid)
  \/ \E node \in Nodes: UpdateReplicationLag(node)
  \/ \E node \in Nodes: NodeFailure(node)
  \/ \E node \in Nodes: NodeRecovery(node)
  \/ \E partition \in SUBSET Nodes: NetworkPartition(partition)
  \/ Next_TM \/ Next_TPC \/ Next_Replication \/ Next_Raft \/ Next_Clock

Spec_DTM == Init_DTM /\ [][Next_DTM]_allVars

(* --------------------------------------------------------------------------
   CROSS-MODULE INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Distributed Atomicity (All or Nothing)
Inv_DTM_DistributedAtomicity ==
  \A tid \in TxIds:
    distributedTx[tid].status = "committed" =>
      \A node \in distributedTx[tid].participants:
        /\ node \in aliveNodes
        /\ nodeReplicas[node][tid] # ""

\* Invariant 2: Replication Consistency
Inv_DTM_ReplicationConsistency ==
  \A tid \in TxIds:
    distributedTx[tid].status = "committed" =>
      \A n1, n2 \in distributedTx[tid].participants:
        nodeReplicas[n1][tid] = nodeReplicas[n2][tid]

\* Invariant 3: Raft Safety - Only one leader per term
Inv_DTM_RaftSafety ==
  Raft_LeaderSafety  \* From ConsensusProtocol

\* Invariant 4: Timestamp Monotonicity
Inv_DTM_TimestampMonotonic ==
  \A t1, t2 \in TxIds:
    /\ distributedTx[t1].status = "committed"
    /\ distributedTx[t2].status = "committed"
    /\ t1 < t2
    => distributedTx[t1].commitTS < distributedTx[t2].commitTS

\* Invariant 5: Replication Lag Bounded
Inv_DTM_ReplicationLagBounded ==
  \A node \in aliveNodes:
    replicationLag[node] <= MAX_REPLICATION_LAG

\* Invariant 6: No Split-Brain
Inv_DTM_NoSplitBrain ==
  \* At most one partition can have a leader
  Cardinality(partitionedNodes) > 0 =>
    ~(GetRaftLeader() \in partitionedNodes)

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Distributed transactions eventually complete
Prop_DTM_TxCompletion ==
  \A tid \in TxIds:
    [](distributedTx[tid].status = "preparing" =>
       <>(distributedTx[tid].status \in {"committed", "aborted"}))

\* Property 2: Replication eventually catches up
Prop_DTM_ReplicationCatchup ==
  \A node \in Nodes:
    [](node \in aliveNodes => <>(replicationLag[node] = 0))

\* Property 3: Partitioned nodes eventually recover
Prop_DTM_PartitionRecovery ==
  [](Cardinality(partitionedNodes) > 0 => <>(partitionedNodes = {}))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM DTM_DistributedACID ==
  \* Distributed transactions satisfy ACID properties
  Spec_DTM => []Inv_DTM_DistributedAtomicity

THEOREM DTM_Consistency ==
  \* All replicas remain consistent
  Spec_DTM => []Inv_DTM_ReplicationConsistency

THEOREM DTM_Progress ==
  \* Transactions eventually complete
  Spec_DTM => Prop_DTM_TxCompletion

=============================================================================

(*
  INTEGRATION NOTES:
  
  This bridge module coordinates five critical components:
  
  1. TransactionManager: Provides local ACID transactions
  2. TwoPhaseCommit: Implements distributed commit protocol
  3. Replication: Ensures data availability across nodes
  4. ConsensusProtocol: Provides Raft consensus for consistency
  5. Clock: Provides distributed timestamp oracle
  
  The key insight is that distributed ACID requires:
  - 2PC for atomic commit
  - Raft for consistent commit decisions
  - Logical clocks for global ordering
  - Replication for fault tolerance
  
  This is similar to:
  - Google Spanner (TrueTime + Paxos)
  - CockroachDB (HLC + Raft)
  - TiDB (TSO + Raft)
  
  VERIFICATION NOTES:
  
  The most critical invariants to verify are:
  1. Distributed Atomicity: No partial commits
  2. Replication Consistency: All replicas converge
  3. Raft Safety: At most one leader per term
  
  These guarantee that the system maintains ACID properties even in:
  - Node failures
  - Network partitions
  - Concurrent distributed transactions
*)


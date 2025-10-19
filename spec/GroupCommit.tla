----------------------------- MODULE GroupCommit -----------------------------
(*
  ColibrìDB Group Commit Optimization Specification
  
  Batches multiple transaction commits into single fsync for performance.
  
  Key Properties:
  - Durability Preserved: Group commit doesn't compromise durability
  - Order Preserved: Commit order matches LSN order
  - Fairness: No transaction starved indefinitely
  
  Author: ColibrìDB Team
  Date: 2025-10-18
*)

EXTENDS CORE, WAL, Naturals

CONSTANTS
  MAX_BATCH_SIZE,      \* Maximum commits per batch
  MAX_WAIT_TIME_MS     \* Maximum wait time before forced flush

VARIABLES
  commitQueue,     \* Sequence of pending commit requests
  batchTimer,      \* Timer for forced flush
  lastFlushTime    \* Timestamp of last flush

gcVars == <<commitQueue, batchTimer, lastFlushTime>>

CommitRequest == [
  tid: TxId,
  targetLSN: LSN,
  timestamp: Timestamp
]

TypeOK_GC ==
  /\ commitQueue \in Seq(CommitRequest)
  /\ batchTimer \in Nat
  /\ lastFlushTime \in Timestamp

Init_GC ==
  /\ commitQueue = <<>>
  /\ batchTimer = 0
  /\ lastFlushTime = 0

RequestCommit(tid, targetLSN, timestamp) ==
  /\ Len(commitQueue) < MAX_BATCH_SIZE
  /\ LET request == [tid |-> tid, targetLSN |-> targetLSN, timestamp |-> timestamp]
     IN commitQueue' = Append(commitQueue, request)
  /\ UNCHANGED <<batchTimer, lastFlushTime>>

FlushBatch ==
  /\ commitQueue # <<>>
  /\ \/ Len(commitQueue) >= MAX_BATCH_SIZE  \* Size threshold
     \/ batchTimer >= MAX_WAIT_TIME_MS       \* Time threshold
  /\ LET maxLSN == Max({req.targetLSN : req \in Range(commitQueue)})
     IN
       /\ flushedLSN' = maxLSN  \* From WAL module
       /\ commitQueue' = <<>>
       /\ batchTimer' = 0
       /\ lastFlushTime' = lastFlushTime + 1
       /\ UNCHANGED <<>>  \* Other WAL vars updated

TickTimer ==
  /\ commitQueue # <<>>
  /\ batchTimer < MAX_WAIT_TIME_MS
  /\ batchTimer' = batchTimer + 1
  /\ UNCHANGED <<commitQueue, lastFlushTime>>

\* Invariants
Inv_GC_DurabilityPreserved ==
  \A req \in Range(commitQueue):
    req.targetLSN > flushedLSN  \* Unflushed commits in queue

Inv_GC_OrderPreserved ==
  \A i, j \in DOMAIN commitQueue:
    i < j => commitQueue[i].targetLSN <= commitQueue[j].targetLSN

Inv_GC_BoundedWait ==
  \A req \in Range(commitQueue):
    lastFlushTime - req.timestamp <= MAX_WAIT_TIME_MS

\* Liveness
Liveness_EventualCommit ==
  []<>(commitQueue = <<>>)

Next_GC ==
  \/ \E tid \in TxId, lsn \in LSN, ts \in Timestamp: RequestCommit(tid, lsn, ts)
  \/ FlushBatch
  \/ TickTimer

Spec_GC == Init_GC /\ [][Next_GC]_gcVars /\ WF_gcVars(FlushBatch)
=============================================================================


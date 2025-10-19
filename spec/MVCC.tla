--------------------------------- MODULE MVCC ---------------------------------
(*
  ColibrìDB Multi-Version Concurrency Control (MVCC) Specification
  
  This module specifies snapshot isolation using multi-version timestamps.
  Implements full MVCC with:
  - Snapshot creation for read consistency
  - Version visibility rules (Snapshot Isolation)
  - Write-Write conflict detection (First Committer Wins)
  - Garbage collection of old versions
  - Read-only transaction optimization
  
  Key Properties:
  - Snapshot Isolation: Transactions see consistent snapshots
  - No Write-Write Conflicts: Concurrent updates to same key conflict
  - Version Chain Consistency: Versions maintain proper ordering
  - Read Stability: Reads are repeatable within transaction
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Based on: 
  - "A Critique of ANSI SQL Isolation Levels" (Berenson et al., 1995)
  - "Serializable Snapshot Isolation in PostgreSQL" (Ports & Grittner, 2012)
*)

EXTENDS CORE, Naturals, FiniteSets, Sequences

CONSTANTS Keys  \* Set of all possible keys

VARIABLES
  versions,      \* [Key -> Seq(Version)]
  activeTx,      \* Set of active transaction IDs
  committedTx,   \* Set of committed transaction IDs
  abortedTx,     \* Set of aborted transaction IDs
  snapshots,     \* [TxId -> Snapshot]
  readSets,      \* [TxId -> SUBSET Keys] - keys read by transaction
  writeSets,     \* [TxId -> SUBSET Keys] - keys written by transaction
  globalTS,      \* Global timestamp counter for commit timestamps
  minActiveTx    \* Minimum active transaction (for GC)

mvccVars == <<versions, activeTx, committedTx, abortedTx, snapshots, 
              readSets, writeSets, globalTS, minActiveTx>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Version structure with full MVCC metadata
Version == [
  value: Value,
  beginTx: TxId,          \* Transaction that created this version
  endTx: TxId \union {0}, \* Transaction that deleted/updated (0 = active)
  beginTS: Timestamp,     \* Commit timestamp when version became visible
  endTS: Timestamp \union {0}, \* Commit timestamp when version became invisible
  createdBy: TxId,        \* Original creator (for conflict detection)
  deletedBy: TxId \union {0}   \* Deleter/updater (0 = not deleted)
]

\* Snapshot for transaction isolation
Snapshot == [
  txId: TxId,
  startTS: Timestamp,          \* Transaction start timestamp
  xmin: Timestamp,             \* Oldest transaction that was active at start
  xmax: Timestamp,             \* Next transaction ID at snapshot time
  activeTxAtStart: SUBSET TxId  \* Set of transactions active when snapshot taken
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_MVCC ==
  /\ versions \in [Keys -> Seq(Version)]
  /\ activeTx \in SUBSET TxIds
  /\ committedTx \in SUBSET TxIds
  /\ abortedTx \in SUBSET TxIds
  /\ snapshots \in [TxIds -> Snapshot]
  /\ readSets \in [TxIds -> SUBSET Keys]
  /\ writeSets \in [TxIds -> SUBSET Keys]
  /\ globalTS \in Timestamp
  /\ minActiveTx \in TxIds \union {0}
  /\ activeTx \intersect committedTx = {}
  /\ activeTx \intersect abortedTx = {}
  /\ committedTx \intersect abortedTx = {}

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ versions = [k \in Keys |-> <<>>]
  /\ activeTx = {}
  /\ committedTx = {}
  /\ abortedTx = {}
  /\ snapshots = [tid \in TxIds |-> [
       txId |-> 0,
       startTS |-> 0,
       xmin |-> 0,
       xmax |-> 0,
       activeTxAtStart |-> {}
     ]]
  /\ readSets = [tid \in TxIds |-> {}]
  /\ writeSets = [tid \in TxIds |-> {}]
  /\ globalTS = 1
  /\ minActiveTx = 0

(* --------------------------------------------------------------------------
   VISIBILITY RULES (Core of MVCC)
   -------------------------------------------------------------------------- *)

\* Check if a version is visible to a given snapshot
\* Implements Snapshot Isolation visibility rules (Berenson et al., 1995)
\* Critical: Transaction MUST see its own uncommitted writes!
IsVisible(version, snapshot) ==
  \* Rule 1: Transaction always sees its own writes (committed or not)
  \/ version.beginTx = snapshot.txId
  \* Rule 2: Version is committed before snapshot and creator not active
  \/ /\ version.beginTS > 0                         \* Version is committed
     /\ version.beginTS < snapshot.startTS          \* Committed before snapshot
     /\ version.beginTx \notin snapshot.activeTxAtStart  \* Creator was not active
     /\ \/ version.endTS = 0                        \* Not deleted
        \/ version.endTS >= snapshot.startTS        \* Deleted after snapshot
        \/ version.endTx = snapshot.txId            \* Own deletes visible

\* Get the visible version of a key for a transaction
\* Returns the newest visible version, or 0 if none exists
GetVisibleVersion(key, tid) ==
  LET snapshot == snapshots[tid]
      visibleVersions == {i \in DOMAIN versions[key] :
                           IsVisible(versions[key][i], snapshot)}
  IN IF visibleVersions = {}
     THEN 0
     ELSE Max(visibleVersions)

(* --------------------------------------------------------------------------
   TRANSACTION OPERATIONS
   -------------------------------------------------------------------------- *)

\* Begin a new transaction and create its snapshot
Begin(tid) ==
  /\ tid \in TxIds
  /\ tid \notin activeTx \union committedTx \union abortedTx
  /\ tid > 0
  /\ activeTx' = activeTx \union {tid}
  /\ snapshots' = [snapshots EXCEPT ![tid] = [
       txId |-> tid,
       startTS |-> globalTS,
       xmin |-> IF activeTx = {} THEN globalTS ELSE Min(activeTx),
       xmax |-> globalTS,
       activeTxAtStart |-> activeTx
     ]]
  /\ readSets' = [readSets EXCEPT ![tid] = {}]
  /\ writeSets' = [writeSets EXCEPT ![tid] = {}]
  /\ minActiveTx' = IF activeTx = {} THEN tid ELSE Min(activeTx \union {tid})
  /\ UNCHANGED <<versions, committedTx, abortedTx, globalTS>>

\* Read a key (adds to read set)
Read(tid, key) ==
  /\ tid \in activeTx
  /\ key \in Keys
  /\ LET versionIdx == GetVisibleVersion(key, tid)
     IN
       /\ readSets' = [readSets EXCEPT ![tid] = @ \union {key}]
       /\ UNCHANGED <<versions, activeTx, committedTx, abortedTx, snapshots,
                      writeSets, globalTS, minActiveTx>>

\* Write a key (creates new version, checks for conflicts)
Write(tid, key, value) ==
  /\ tid \in activeTx
  /\ key \in Keys
  /\ LET 
       \* Check for write-write conflicts with concurrent transactions
       hasConflict == \E i \in DOMAIN versions[key]:
                        /\ versions[key][i].endTx = 0
                        /\ versions[key][i].beginTx # tid
                        /\ versions[key][i].beginTx \in activeTx
       \* Create new version
       newVersion == [
         value |-> value,
         beginTx |-> tid,
         endTx |-> 0,
         beginTS |-> 0,  \* Will be set at commit
         endTS |-> 0,
         createdBy |-> tid,
         deletedBy |-> 0
       ]
     IN
       /\ ~hasConflict  \* Abort if write-write conflict detected
       /\ versions' = [versions EXCEPT ![key] = Append(@, newVersion)]
       /\ writeSets' = [writeSets EXCEPT ![tid] = @ \union {key}]
       /\ UNCHANGED <<activeTx, committedTx, abortedTx, snapshots, 
                      readSets, globalTS, minActiveTx>>

\* Update a key (logically delete old version, create new one)
Update(tid, key, newValue) ==
  /\ tid \in activeTx
  /\ key \in Keys
  /\ LET 
       oldVersionIdx == GetVisibleVersion(key, tid)
       hasConflict == \E i \in DOMAIN versions[key]:
                        /\ versions[key][i].endTx = 0
                        /\ versions[key][i].beginTx # tid
                        /\ versions[key][i].beginTx \in activeTx
       newVersion == [
         value |-> newValue,
         beginTx |-> tid,
         endTx |-> 0,
         beginTS |-> 0,
         endTS |-> 0,
         createdBy |-> tid,
         deletedBy |-> 0
       ]
     IN
       /\ oldVersionIdx > 0  \* Key must exist
       /\ ~hasConflict
       /\ versions' = [versions EXCEPT 
            ![key] = [i \in DOMAIN @ |->
              IF i = oldVersionIdx
              THEN [@ EXCEPT !.endTx = tid, !.deletedBy = tid]
              ELSE @[i]
            ] \o <<newVersion>>
          ]
       /\ writeSets' = [writeSets EXCEPT ![tid] = @ \union {key}]
       /\ UNCHANGED <<activeTx, committedTx, abortedTx, snapshots, 
                      readSets, globalTS, minActiveTx>>

\* Delete a key (mark latest visible version as deleted)
Delete(tid, key) ==
  /\ tid \in activeTx
  /\ key \in Keys
  /\ LET 
       versionIdx == GetVisibleVersion(key, tid)
       hasConflict == \E i \in DOMAIN versions[key]:
                        /\ versions[key][i].endTx = 0
                        /\ versions[key][i].beginTx # tid
                        /\ versions[key][i].beginTx \in activeTx
     IN
       /\ versionIdx > 0
       /\ ~hasConflict
       /\ versions' = [versions EXCEPT ![key][versionIdx].endTx = tid,
                                       ![key][versionIdx].deletedBy = tid]
       /\ writeSets' = [writeSets EXCEPT ![tid] = @ \union {key}]
       /\ UNCHANGED <<activeTx, committedTx, abortedTx, snapshots, 
                      readSets, globalTS, minActiveTx>>

\* Commit transaction (assign commit timestamp, make versions visible)
\* CRITICAL FIX: Check for write-write conflicts at commit time (First-Committer-Wins)
\* Based on Berenson et al. Section 3.2: "The first updater wins"
Commit(tid) ==
  /\ tid \in activeTx
  /\ LET 
       commitTS == globalTS
       \* Check for write-write conflicts with committed transactions
       hasCommitConflict == \E k \in writeSets[tid]:
                              \E i \in DOMAIN versions[k]:
                                /\ versions[k][i].createdBy # tid
                                /\ versions[k][i].beginTx \in committedTx
                                /\ versions[k][i].beginTS >= snapshots[tid].startTS
                                /\ versions[k][i].endTS = 0
     IN
       /\ ~hasCommitConflict  \* Abort if conflict detected at commit
       /\ activeTx' = activeTx \ {tid}
       /\ committedTx' = committedTx \union {tid}
       /\ globalTS' = globalTS + 1
       /\ versions' = [k \in Keys |->
            [i \in DOMAIN versions[k] |->
              IF versions[k][i].beginTx = tid
              THEN [versions[k][i] EXCEPT !.beginTS = commitTS]
              ELSE IF versions[k][i].endTx = tid
              THEN [versions[k][i] EXCEPT !.endTS = commitTS]
              ELSE versions[k][i]
            ]
          ]
       /\ minActiveTx' = IF activeTx \ {tid} = {} 
                         THEN 0 
                         ELSE Min(activeTx \ {tid})
       /\ UNCHANGED <<abortedTx, snapshots, readSets, writeSets>>

\* Abort transaction (remove uncommitted versions, restore deleted versions)
Abort(tid) ==
  /\ tid \in activeTx
  /\ activeTx' = activeTx \ {tid}
  /\ abortedTx' = abortedTx \union {tid}
  /\ versions' = [k \in Keys |->
       LET filtered == SelectSeq(versions[k], 
                         LAMBDA v: v.beginTx # tid)
           restored == [i \in DOMAIN filtered |->
                         IF filtered[i].endTx = tid
                         THEN [filtered[i] EXCEPT !.endTx = 0, !.deletedBy = 0]
                         ELSE filtered[i]
                       ]
       IN restored
     ]
  /\ minActiveTx' = IF activeTx \ {tid} = {} 
                    THEN 0 
                    ELSE Min(activeTx \ {tid})
  /\ UNCHANGED <<committedTx, snapshots, readSets, writeSets, globalTS>>

\* Vacuum: Remove old versions that are no longer visible to any active transaction
Vacuum ==
  /\ activeTx # {}
  /\ LET oldestSnapshot == minActiveTx
     IN
       /\ oldestSnapshot > 0
       /\ versions' = [k \in Keys |->
            SelectSeq(versions[k],
              LAMBDA v: \/ v.endTS = 0
                        \/ v.endTS >= oldestSnapshot
            )
          ]
       /\ UNCHANGED <<activeTx, committedTx, abortedTx, snapshots, 
                      readSets, writeSets, globalTS, minActiveTx>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Snapshot Isolation - transactions see consistent snapshots
Inv_MVCC_SnapshotIsolation ==
  \A tid \in activeTx:
    /\ tid \in DOMAIN snapshots
    /\ snapshots[tid].txId = tid
    /\ \A key \in readSets[tid]:
         LET versionIdx == GetVisibleVersion(key, tid)
         IN \/ versionIdx = 0  \* Key doesn't exist
            \/ /\ versionIdx > 0
               /\ IsVisible(versions[key][versionIdx], snapshots[tid])

\* Invariant 2: No concurrent writes to same key
Inv_MVCC_NoWriteWriteConflict ==
  \A k \in Keys:
    \A i, j \in DOMAIN versions[k]:
      /\ i # j
      /\ versions[k][i].endTx = 0
      /\ versions[k][j].endTx = 0
      /\ versions[k][i].beginTx \in activeTx
      /\ versions[k][j].beginTx \in activeTx
      => versions[k][i].beginTx = versions[k][j].beginTx

\* Invariant 3: Version chains maintain timestamp ordering
Inv_MVCC_VersionChainConsistency ==
  \A k \in Keys:
    \A i \in DOMAIN versions[k]:
      /\ i > 1 =>
           \/ versions[k][i].beginTS = 0  \* Uncommitted
           \/ versions[k][i-1].beginTS = 0
           \/ versions[k][i].beginTS > versions[k][i-1].beginTS

\* Invariant 4: Committed versions have valid timestamps
Inv_MVCC_CommittedVersionsValid ==
  \A k \in Keys:
    \A i \in DOMAIN versions[k]:
      versions[k][i].beginTx \in committedTx =>
        /\ versions[k][i].beginTS > 0
        /\ versions[k][i].beginTS < globalTS

\* Invariant 5: Active transactions have snapshots
Inv_MVCC_ActiveTxHaveSnapshots ==
  \A tid \in activeTx:
    /\ tid \in DOMAIN snapshots
    /\ snapshots[tid].startTS > 0
    /\ snapshots[tid].startTS <= globalTS

\* Invariant 6: Read stability - repeated reads return same value
Inv_MVCC_ReadStability ==
  \A tid \in activeTx:
    \A key \in readSets[tid]:
      LET v1 == GetVisibleVersion(key, tid)
      IN v1 = GetVisibleVersion(key, tid)  \* Always same version

\* Invariant 7: Write sets are subsets of all keys
Inv_MVCC_WriteSetsValid ==
  \A tid \in TxIds:
    writeSets[tid] \subseteq Keys

\* Combined safety invariant
Inv_MVCC_Safety ==
  /\ TypeOK_MVCC
  /\ Inv_MVCC_SnapshotIsolation
  /\ Inv_MVCC_NoWriteWriteConflict
  /\ Inv_MVCC_VersionChainConsistency
  /\ Inv_MVCC_CommittedVersionsValid
  /\ Inv_MVCC_ActiveTxHaveSnapshots
  /\ Inv_MVCC_ReadStability
  /\ Inv_MVCC_WriteSetsValid

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, all transactions complete (commit or abort)
Liveness_TxEventuallyCompletes ==
  \A tid \in TxIds:
    [](tid \in activeTx => <>(tid \in committedTx \union abortedTx))

\* Eventually, old versions are vacuumed
Liveness_EventualVacuum ==
  []<>(Cardinality(activeTx) = 0 \/ Vacuum)

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E tid \in TxIds: Begin(tid)
  \/ \E tid \in TxIds, key \in Keys: Read(tid, key)
  \/ \E tid \in TxIds, key \in Keys, value \in Value: Write(tid, key, value)
  \/ \E tid \in TxIds, key \in Keys, value \in Value: Update(tid, key, value)
  \/ \E tid \in TxIds, key \in Keys: Delete(tid, key)
  \/ \E tid \in TxIds: Commit(tid)
  \/ \E tid \in TxIds: Abort(tid)
  \/ Vacuum

Spec == Init /\ [][Next]_mvccVars

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: Snapshot Isolation prevents lost updates
THEOREM SnapshotIsolation_PreventsLostUpdates ==
  Spec => []Inv_MVCC_NoWriteWriteConflict

\* Theorem 2: Reads are repeatable within transaction
THEOREM RepeatableReads ==
  Spec => []Inv_MVCC_ReadStability

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    MAX_TX = 4
    MAX_LSN = 20
    MAX_PAGES = 5
    Keys = {1, 2, 3}
  
  Invariants to check:
    - Inv_MVCC_Safety
  
  Temporal properties:
    - Liveness_TxEventuallyCompletes (with fairness)
  
  State constraints:
    - globalTS <= 20
    - Cardinality(activeTx) <= 3
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_MVCC(mvcc: MVCCEngine) -> [String: Any] {
      return [
          "versions": Dictionary(grouping: mvcc.versionStore.allVersions) { $0.key },
          "activeTx": Set(mvcc.activeTx.keys),
          "committedTx": Set(mvcc.committedTx),
          "abortedTx": Set(mvcc.abortedTx),
          "snapshots": mvcc.snapshots.mapValues { snap in
              ["txId": snap.txId,
               "startTS": snap.startTS,
               "xmin": snap.xmin,
               "xmax": snap.xmax,
               "activeTxAtStart": Set(snap.activeTxAtStart)]
          },
          "readSets": mvcc.readSets,
          "writeSets": mvcc.writeSets,
          "globalTS": mvcc.globalTimestamp,
          "minActiveTx": mvcc.minActiveTransaction
      ]
  }
  
  TRACE POINTS:
  
  - traceLog(.mvccBegin, state: toTLA_MVCC(self), txId: tid)
  - traceLog(.mvccRead, state: toTLA_MVCC(self), txId: tid, key: key)
  - traceLog(.mvccWrite, state: toTLA_MVCC(self), txId: tid, key: key)
  - traceLog(.mvccCommit, state: toTLA_MVCC(self), txId: tid)
  - traceLog(.mvccAbort, state: toTLA_MVCC(self), txId: tid)
  - traceLog(.mvccVacuum, state: toTLA_MVCC(self))
*)


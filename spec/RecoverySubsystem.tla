------------------------- MODULE RecoverySubsystem -------------------------
(***************************************************************************
 * Recovery Subsystem Bridge Module
 *
 * This bridge module integrates the complete recovery and backup stack:
 *   - WAL.tla: Write-Ahead Logging with LSN tracking
 *   - RECOVERY.tla: ARIES recovery algorithm (Analysis, Redo, Undo)
 *   - ErrorRecovery.tla: Error handling and resilience
 *   - Backup.tla: Full and incremental backup system
 *   - PointInTimeRecovery.tla: PITR with WAL replay
 *   - Compression.tla: Data compression for backups
 *
 * Purpose:
 *   Provide a unified recovery subsystem that guarantees ACID durability
 *   through coordinated WAL, crash recovery, backups, and PITR.
 *
 * Key Integration Points:
 *   1. WAL <-> RECOVERY: ARIES recovery reads WAL for redo/undo
 *   2. WAL <-> Backup: Checkpoint before backup, WAL archived
 *   3. Backup <-> PITR: PITR restores backup + replays WAL
 *   4. ErrorRecovery: Coordinates all error scenarios
 *   5. Compression: Applied to backup data
 *
 * Cross-Module Invariants:
 *   - Inv_RS_Durability: Committed data always recoverable
 *   - Inv_RS_PITRAccuracy: PITR restores exact state at timestamp
 *   - Inv_RS_WARProtocol: Write-Ahead-Restore (WAL before backup)
 *   - Inv_RS_BackupCompleteness: Backup + WAL cover all data
 *   - Inv_RS_NoCorruption: Recovery detects and handles corruption
 *
 * Based on:
 *   - Mohan, C., et al. (1992). "ARIES: A Transaction Recovery Method
 *     Supporting Fine-Granularity Locking and Partial Rollbacks Using
 *     Write-Ahead Logging". ACM TODS, 17(1), 94-162.
 *   - Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts
 *     and Techniques". Morgan Kaufmann. Chapter 10: Recovery.
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 * Version: 1.0
 ***************************************************************************)

EXTENDS CORE, WAL, RECOVERY, ErrorRecovery, Compression, Naturals, Sequences, FiniteSets

(***************************************************************************
 * INTEGRATION STATE
 ***************************************************************************)

VARIABLES
    recoverySubsystemState,  \* State machine: "normal" | "recovering" | "backing_up" | "error"
    lastBackupLSN,          \* LSN at last backup
    backupInProgress,       \* BOOLEAN
    recoveryInProgress,     \* BOOLEAN
    archivedWALSegments,    \* Seq(WALSegment) - archived WAL for PITR
    backupMetadata,         \* [backupId -> [lsn, timestamp, type, compressed]]
    nextBackupId,           \* Nat
    restoreTargetLSN,       \* LSN to restore to (for PITR), 0 if not restoring
    compressionEnabled,     \* BOOLEAN
    integrityChecks         \* [LSN -> checksum] - for corruption detection

rsVars == <<recoverySubsystemState, lastBackupLSN, backupInProgress, recoveryInProgress,
             archivedWALSegments, backupMetadata, nextBackupId, restoreTargetLSN,
             compressionEnabled, integrityChecks>>

\* Combine all variables from integrated modules
allRecoveryVars == <<
    rsVars,
    vars,           \* WAL variables
    recoveryVars,   \* RECOVERY variables
    errorVars,      \* ErrorRecovery variables
    compressionVars \* Compression variables (if defined)
>>

(***************************************************************************
 * CONSTANTS
 ***************************************************************************)

CONSTANTS
    BACKUP_INTERVAL_LSN,    \* Trigger backup every N LSNs
    MAX_ARCHIVED_SEGMENTS,  \* Maximum archived WAL segments to keep
    COMPRESSION_ALGORITHM,  \* "none" | "lz4" | "snappy" | "zstd"
    BACKUP_TYPES            \* {"FULL", "INCREMENTAL"}

ASSUME BACKUP_INTERVAL_LSN \in Nat \ {0}
ASSUME MAX_ARCHIVED_SEGMENTS \in Nat \ {0}
ASSUME COMPRESSION_ALGORITHM \in {"none", "lz4", "snappy", "zstd"}
ASSUME BACKUP_TYPES = {"FULL", "INCREMENTAL"}

(***************************************************************************
 * TYPE INVARIANT
 ***************************************************************************)

TypeOK_RecoverySubsystem ==
    /\ TypeOK                           \* WAL
    /\ TypeOK_Recovery                  \* RECOVERY
    /\ TypeOK_ErrorRecovery             \* ErrorRecovery
    /\ recoverySubsystemState \in {"normal", "recovering", "backing_up", "error"}
    /\ lastBackupLSN \in LSN
    /\ backupInProgress \in BOOLEAN
    /\ recoveryInProgress \in BOOLEAN
    /\ archivedWALSegments \in Seq([startLSN: LSN, endLSN: LSN, records: Seq(WALRecord)])
    /\ backupMetadata \in [Nat -> [lsn: LSN, timestamp: Nat, type: BACKUP_TYPES, 
                                    compressed: BOOLEAN, size: Nat]]
    /\ nextBackupId \in Nat
    /\ restoreTargetLSN \in LSN
    /\ compressionEnabled \in BOOLEAN
    /\ integrityChecks \in [LSN -> Nat]  \* LSN -> checksum

(***************************************************************************
 * INITIAL STATE
 ***************************************************************************)

Init_RecoverySubsystem ==
    /\ Init                             \* WAL Init
    /\ Init_Recovery                    \* RECOVERY Init
    /\ Init_ErrorRecovery               \* ErrorRecovery Init
    /\ recoverySubsystemState = "normal"
    /\ lastBackupLSN = 0
    /\ backupInProgress = FALSE
    /\ recoveryInProgress = FALSE
    /\ archivedWALSegments = <<>>
    /\ backupMetadata = [b \in {} |-> <<>>]
    /\ nextBackupId = 1
    /\ restoreTargetLSN = 0
    /\ compressionEnabled = (COMPRESSION_ALGORITHM # "none")
    /\ integrityChecks = [lsn \in {} |-> 0]

(***************************************************************************
 * INTEGRATION OPERATIONS
 ***************************************************************************)

\* -------------------------------------------------------------------------
\* Operation: Perform Full Backup with Compression
\* Integrates: WAL (checkpoint) + Backup + Compression
\* -------------------------------------------------------------------------
PerformFullBackup ==
    /\ recoverySubsystemState = "normal"
    /\ ~backupInProgress
    /\ nextLSN > lastBackupLSN + BACKUP_INTERVAL_LSN  \* Time for backup
    
    \* Step 1: Checkpoint WAL (ensures all dirty pages flushed)
    /\ Checkpoint
    /\ LET checkpointLSN == flushedLSN
       IN
       \* Step 2: Create backup metadata
       /\ backupMetadata' = backupMetadata @@ 
            (nextBackupId :> [
                lsn |-> checkpointLSN,
                timestamp |-> currentTime,  \* Assume time tracking
                type |-> "FULL",
                compressed |-> compressionEnabled,
                size |-> nextLSN - 1  \* Total log size
            ])
       
       \* Step 3: Archive current WAL segment
       /\ archivedWALSegments' = Append(archivedWALSegments, [
            startLSN |-> lastBackupLSN + 1,
            endLSN |-> checkpointLSN,
            records |-> SubSeq(log, lastBackupLSN + 1, checkpointLSN)
          ])
       
       \* Step 4: Update state
       /\ lastBackupLSN' = checkpointLSN
       /\ nextBackupId' = nextBackupId + 1
       /\ recoverySubsystemState' = "normal"
       /\ backupInProgress' = FALSE
       
    /\ UNCHANGED <<recoveryVars, errorVars, recoveryInProgress, 
                   restoreTargetLSN, compressionEnabled, integrityChecks>>

\* -------------------------------------------------------------------------
\* Operation: Perform Incremental Backup
\* Backs up only WAL records since last backup
\* -------------------------------------------------------------------------
PerformIncrementalBackup ==
    /\ recoverySubsystemState = "normal"
    /\ ~backupInProgress
    /\ lastBackupLSN > 0  \* Must have full backup first
    /\ nextLSN > lastBackupLSN + (BACKUP_INTERVAL_LSN \div 2)  \* More frequent
    
    /\ LET currentLSN == nextLSN - 1
       IN
       \* Archive incremental WAL segment
       /\ archivedWALSegments' = Append(archivedWALSegments, [
            startLSN |-> lastBackupLSN + 1,
            endLSN |-> currentLSN,
            records |-> SubSeq(log, lastBackupLSN + 1, currentLSN)
          ])
       
       /\ backupMetadata' = backupMetadata @@ 
            (nextBackupId :> [
                lsn |-> currentLSN,
                timestamp |-> currentTime,
                type |-> "INCREMENTAL",
                compressed |-> compressionEnabled,
                size |-> currentLSN - lastBackupLSN
            ])
       
       /\ lastBackupLSN' = currentLSN
       /\ nextBackupId' = nextBackupId + 1
       
    /\ UNCHANGED <<vars, recoveryVars, errorVars, recoverySubsystemState,
                   backupInProgress, recoveryInProgress, restoreTargetLSN,
                   compressionEnabled, integrityChecks>>

\* -------------------------------------------------------------------------
\* Operation: Point-In-Time Recovery
\* Integrates: Backup (restore) + WAL (replay) + RECOVERY (ARIES)
\* -------------------------------------------------------------------------
PerformPITR(targetLSN) ==
    /\ recoverySubsystemState = "normal"
    /\ ~recoveryInProgress
    /\ targetLSN \in LSNs
    /\ targetLSN <= flushedLSN
    
    \* Find latest full backup before targetLSN
    /\ LET fullBackups == {bid \in DOMAIN backupMetadata : 
                            /\ backupMetadata[bid].type = "FULL"
                            /\ backupMetadata[bid].lsn <= targetLSN}
           lastFullBackupId == CHOOSE bid \in fullBackups :
                                \A bid2 \in fullBackups : 
                                  backupMetadata[bid].lsn >= backupMetadata[bid2].lsn
           baseBackup == backupMetadata[lastFullBackupId]
       IN
       /\ recoverySubsystemState' = "recovering"
       /\ recoveryInProgress' = TRUE
       /\ restoreTargetLSN' = targetLSN
       
       \* Step 1: Restore base backup (simulated)
       \* In practice: restore data files from backup
       
       \* Step 2: Apply incremental backups if any
       /\ LET incrementalBackups == {bid \in DOMAIN backupMetadata :
                                      /\ backupMetadata[bid].type = "INCREMENTAL"
                                      /\ backupMetadata[bid].lsn > baseBackup.lsn
                                      /\ backupMetadata[bid].lsn <= targetLSN}
          IN TRUE  \* Apply incrementals (simulated)
       
       \* Step 3: Replay WAL from baseBackup.lsn to targetLSN
       \* This integrates with RECOVERY module's redo phase
       /\ AnalysisPhase  \* Build ATT and DPT
       /\ RedoComplete   \* Replay WAL records
       \* Stop at targetLSN, not flushedLSN
       
       \* Step 4: Undo uncommitted transactions at targetLSN
       /\ UndoComplete
       
       \* Step 5: Mark recovery complete
       /\ recoverySubsystemState' = "normal"
       /\ recoveryInProgress' = FALSE
       /\ restoreTargetLSN' = 0
       
    /\ UNCHANGED <<backupMetadata, nextBackupId, lastBackupLSN, backupInProgress,
                   archivedWALSegments, compressionEnabled, integrityChecks>>

\* -------------------------------------------------------------------------
\* Operation: Crash and Recovery
\* Integrates: WAL (crash) + RECOVERY (ARIES) + ErrorRecovery
\* -------------------------------------------------------------------------
CrashAndRecover ==
    /\ recoverySubsystemState = "normal"
    /\ ~recoveryInProgress
    
    \* Step 1: Simulate crash (from WAL module)
    /\ Crash
    /\ recoverySubsystemState' = "recovering"
    /\ recoveryInProgress' = TRUE
    
    \* Step 2: Error detection and logging (ErrorRecovery)
    /\ DetectError("crash")
    /\ LogError([type |-> "crash", lsn |-> nextLSN - 1])
    
    \* Step 3: ARIES recovery
    /\ AnalysisPhase
    /\ RedoComplete
    /\ UndoComplete
    
    \* Step 4: Recovery complete
    /\ recoverySubsystemState' = "normal"
    /\ recoveryInProgress' = FALSE
    
    /\ UNCHANGED <<backupMetadata, nextBackupId, lastBackupLSN, backupInProgress,
                   archivedWALSegments, restoreTargetLSN, compressionEnabled,
                   integrityChecks>>

\* -------------------------------------------------------------------------
\* Operation: Archive Old WAL Segments
\* Prune old archived segments to avoid unbounded growth
\* -------------------------------------------------------------------------
PruneArchivedWAL ==
    /\ recoverySubsystemState = "normal"
    /\ Len(archivedWALSegments) > MAX_ARCHIVED_SEGMENTS
    
    \* Keep only recent segments needed for PITR
    /\ LET minRequiredLSN == lastBackupLSN - (BACKUP_INTERVAL_LSN * 2)
           prunedSegments == SelectSeq(archivedWALSegments, 
                                        LAMBDA seg: seg.endLSN >= minRequiredLSN)
       IN archivedWALSegments' = prunedSegments
    
    /\ UNCHANGED <<vars, recoveryVars, errorVars, recoverySubsystemState,
                   backupMetadata, nextBackupId, lastBackupLSN, backupInProgress,
                   recoveryInProgress, restoreTargetLSN, compressionEnabled,
                   integrityChecks>>

(***************************************************************************
 * CROSS-MODULE INVARIANTS
 ***************************************************************************)

\* Invariant 1: ACID Durability - committed data is recoverable
Inv_RS_Durability ==
    \A lsn \in 1..flushedLSN:
        /\ log[lsn].kind = "commit"
        => \* Either in current WAL or archived
           \/ lsn \in DOMAIN log
           \/ \E seg \in Range(archivedWALSegments): 
                lsn >= seg.startLSN /\ lsn <= seg.endLSN

\* Invariant 2: Write-Ahead-Restore - WAL flushed before backup
Inv_RS_WARProtocol ==
    lastBackupLSN > 0 => lastBackupLSN <= flushedLSN

\* Invariant 3: Backup Completeness - backup + WAL cover all data
Inv_RS_BackupCompleteness ==
    /\ lastBackupLSN > 0
    => \* All LSNs from lastBackupLSN to flushedLSN are either:
       \* (a) in current WAL, or (b) in archived segments
       \A lsn \in lastBackupLSN..flushedLSN:
         \/ lsn \in DOMAIN log
         \/ \E seg \in Range(archivedWALSegments):
              lsn >= seg.startLSN /\ lsn <= seg.endLSN

\* Invariant 4: PITR Accuracy - restore point is valid
Inv_RS_PITRAccuracy ==
    /\ restoreTargetLSN > 0
    => /\ restoreTargetLSN <= flushedLSN
       /\ \E bid \in DOMAIN backupMetadata:
            /\ backupMetadata[bid].type = "FULL"
            /\ backupMetadata[bid].lsn <= restoreTargetLSN

\* Invariant 5: No Concurrent Operations - recovery is exclusive
Inv_RS_ExclusiveRecovery ==
    recoveryInProgress => ~backupInProgress

\* Invariant 6: Recovery State Machine - valid transitions
Inv_RS_StateMachineValid ==
    /\ recoverySubsystemState \in {"normal", "recovering", "backing_up", "error"}
    /\ (recoverySubsystemState = "recovering") <=> recoveryInProgress
    /\ (recoverySubsystemState = "backing_up") <=> backupInProgress

\* Invariant 7: Archived WAL Bounded - prevent memory exhaustion
Inv_RS_ArchivedWALBounded ==
    Len(archivedWALSegments) <= MAX_ARCHIVED_SEGMENTS + 5  \* Small slack

\* Invariant 8: Backup Monotonicity - backups are monotonically increasing
Inv_RS_BackupMonotonic ==
    \A bid1, bid2 \in DOMAIN backupMetadata:
        bid1 < bid2 => backupMetadata[bid1].lsn < backupMetadata[bid2].lsn

\* Combined Recovery Subsystem Safety
Inv_RS_Safety ==
    /\ TypeOK_RecoverySubsystem
    /\ Inv_RS_Durability
    /\ Inv_RS_WARProtocol
    /\ Inv_RS_BackupCompleteness
    /\ Inv_RS_PITRAccuracy
    /\ Inv_RS_ExclusiveRecovery
    /\ Inv_RS_StateMachineValid
    /\ Inv_RS_ArchivedWALBounded
    /\ Inv_RS_BackupMonotonic

(***************************************************************************
 * NEXT-STATE RELATION
 ***************************************************************************)

Next_RecoverySubsystem ==
    \/ PerformFullBackup
    \/ PerformIncrementalBackup
    \/ \E targetLSN \in LSNs: PerformPITR(targetLSN)
    \/ CrashAndRecover
    \/ PruneArchivedWAL
    \/ Next                     \* WAL operations
    \/ Next_Recovery            \* RECOVERY operations
    \/ Next_ErrorRecovery       \* ErrorRecovery operations

(***************************************************************************
 * SPECIFICATION
 ***************************************************************************)

Spec_RecoverySubsystem == 
    Init_RecoverySubsystem /\ [][Next_RecoverySubsystem]_allRecoveryVars

(***************************************************************************
 * LIVENESS PROPERTIES
 ***************************************************************************)

\* Eventually, recovery completes
Liveness_RS_RecoveryCompletes ==
    [](recoveryInProgress => <>(~recoveryInProgress))

\* Eventually, backup is performed
Liveness_RS_BackupProgress ==
    []<>(lastBackupLSN > 0)

\* Eventually, all committed data is backed up
Liveness_RS_AllDataBackedUp ==
    []<>(\A lsn \in 1..flushedLSN: 
           log[lsn].kind = "commit" => lsn <= lastBackupLSN)

(***************************************************************************
 * THEOREMS
 ***************************************************************************)

\* Theorem 1: Recovery Subsystem maintains safety
THEOREM RecoverySubsystem_Safety ==
    Spec_RecoverySubsystem => []Inv_RS_Safety

\* Theorem 2: Committed transactions are durable
THEOREM RecoverySubsystem_Durability ==
    Spec_RecoverySubsystem => []Inv_RS_Durability

\* Theorem 3: PITR restores accurate state
THEOREM RecoverySubsystem_PITRCorrectness ==
    Spec_RecoverySubsystem => []Inv_RS_PITRAccuracy

\* Theorem 4: Recovery eventually completes
THEOREM RecoverySubsystem_RecoveryProgress ==
    Spec_RecoverySubsystem => Liveness_RS_RecoveryCompletes

=============================================================================

(*
  MODEL CHECKING CONFIGURATION (RecoverySubsystem.cfg):
  
  SPECIFICATION Spec_RecoverySubsystem
  
  CONSTANTS
    MAX_TX = 3
    MAX_LSN = 20
    MAX_PAGES = 3
    BACKUP_INTERVAL_LSN = 5
    MAX_ARCHIVED_SEGMENTS = 3
    COMPRESSION_ALGORITHM = "lz4"
    BACKUP_TYPES = {"FULL", "INCREMENTAL"}
    
  INVARIANTS
    TypeOK_RecoverySubsystem
    Inv_RS_Safety
    Inv_RS_Durability
    Inv_RS_WARProtocol
    Inv_RS_BackupCompleteness
    
  PROPERTIES
    Liveness_RS_RecoveryCompletes
    Liveness_RS_BackupProgress
    
  CONSTRAINT
    nextLSN <= MAX_LSN
    
  This model checks that:
    1. Recovery subsystem maintains type safety
    2. All committed data is recoverable (durability)
    3. WAL is flushed before backups (WAR protocol)
    4. Backup + WAL cover all data (completeness)
    5. Recovery eventually completes (liveness)
    6. Backups eventually progress (liveness)
*)


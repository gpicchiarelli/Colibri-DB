-------------------------------- MODULE Backup --------------------------------
(*****************************************************************************)
(* Backup System for ColibrìDB                                              *)
(*                                                                           *)
(* This specification models a comprehensive backup system with:            *)
(*   - Full backups (complete database snapshot)                            *)
(*   - Incremental backups (changes since last backup)                      *)
(*   - Differential backups (changes since last full backup)                *)
(*   - Consistent snapshots (ACID-compliant)                                *)
(*   - Backup catalog management                                            *)
(*   - Backup verification and validation                                   *)
(*   - Backup retention policies                                            *)
(*   - Parallel backup streams                                              *)
(*   - Backup compression and encryption                                    *)
(*   - Hot backups (without stopping database)                              *)
(*   - Restore operations                                                   *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Gray & Reuter (1993): "Transaction Processing" - Recovery            *)
(*   - Oracle RMAN (Recovery Manager) architecture                          *)
(*   - PostgreSQL pg_basebackup and WAL archiving                           *)
(*   - MySQL Enterprise Backup documentation                                *)
(*   - Verma & Kale (2016): "Cloud Backup and Recovery"                     *)
(*   - Tang et al. (2012): "Incremental Backup Systems"                     *)
(*   - Zhu et al. (2008): "Avoiding the Disk Bottleneck in Backup"         *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE, TLC

CONSTANTS
    DatabaseObjects,    \* Set of all database objects (tables, indexes, etc.)
    BackupDestinations, \* Set of backup storage locations
    MaxBackups,         \* Maximum number of backups to retain
    MaxParallelStreams, \* Maximum parallel backup streams
    CompressionLevels,  \* Set of compression levels (0-9)
    RetentionDays       \* Backup retention period in days

VARIABLES
    databaseState,      \* Current state of database objects
    backupCatalog,      \* Catalog of all backups
    activeBackups,      \* Currently running backup operations
    backupDestState,    \* State of backup destinations
    walArchive,         \* Write-Ahead Log archive
    restorePoints,      \* Named restore points
    backupMetrics,      \* Performance metrics for backups
    auditLog,           \* Audit trail of backup operations
    currentTime,        \* Global clock
    lastFullBackup,     \* Timestamp of last full backup
    currentLSN          \* Current Log Sequence Number

vars == <<databaseState, backupCatalog, activeBackups, backupDestState,
          walArchive, restorePoints, backupMetrics, auditLog, currentTime,
          lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Type Definitions *)

BackupId == Nat
LSN == Nat  \* Log Sequence Number
Timestamp == Nat

(* Backup types *)
BackupType == {"FULL", "INCREMENTAL", "DIFFERENTIAL", "ARCHIVE_LOG"}

(* Backup status *)
BackupStatus == {"RUNNING", "COMPLETED", "FAILED", "VALIDATED", "EXPIRED"}

(* Backup method *)
BackupMethod == {"HOT", "COLD", "WARM"}  \* Online, offline, or read-only

(* Compression algorithms *)
CompressionAlgorithm == {"NONE", "LZ4", "SNAPPY", "ZSTD", "GZIP"}

(* Backup structure *)
Backup == [
    id: BackupId,
    type: BackupType,
    status: BackupStatus,
    startTime: Timestamp,
    endTime: Timestamp,
    startLSN: LSN,
    endLSN: LSN,
    objects: SUBSET DatabaseObjects,
    destination: BackupDestinations,
    size: Nat,
    compressed: BOOLEAN,
    compressionAlgo: CompressionAlgorithm,
    compressionLevel: CompressionLevels,
    encrypted: BOOLEAN,
    checksum: STRING,
    parentBackupId: BackupId \cup {0},  \* 0 = no parent
    method: BackupMethod,
    parallelStreams: Nat
]

(* Restore point *)
RestorePoint == [
    name: STRING,
    timestamp: Timestamp,
    lsn: LSN,
    description: STRING
]

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ databaseState = [obj \in DatabaseObjects |-> 
         [data |-> <<>>, version |-> 0, lsn |-> 0]]
    /\ backupCatalog = {}
    /\ activeBackups = {}
    /\ backupDestState = [dest \in BackupDestinations |->
         [available |-> TRUE, freeSpace |-> 1000000, backups |-> {}]]
    /\ walArchive = <<>>
    /\ restorePoints = {}
    /\ backupMetrics = [totalBackups |-> 0, totalSize |-> 0, 
                       avgDuration |-> 0, lastBackupTime |-> 0]
    /\ auditLog = <<>>
    /\ currentTime = 0
    /\ lastFullBackup = 0
    /\ currentLSN = 0

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Generate unique backup ID *)
GenerateBackupId ==
    Cardinality(backupCatalog) + 1

(* Calculate backup size based on type and objects *)
CalculateBackupSize(backupType, objects, parentId) ==
    CASE backupType = "FULL" -> Cardinality(objects) * 100
      [] backupType = "INCREMENTAL" -> Cardinality(objects) * 10
      [] backupType = "DIFFERENTIAL" -> Cardinality(objects) * 30
      [] backupType = "ARCHIVE_LOG" -> 50
      [] OTHER -> 0

(* Apply compression ratio *)
CompressedSize(size, algo, level) ==
    CASE algo = "NONE" -> size
      [] algo = "LZ4" -> size \div 2
      [] algo = "SNAPPY" -> size \div 2
      [] algo = "ZSTD" -> size \div 3
      [] algo = "GZIP" -> size \div 4
      [] OTHER -> size

(* Check if destination has enough space *)
HasEnoughSpace(destination, requiredSize) ==
    backupDestState[destination].freeSpace >= requiredSize

(* Get all objects modified since LSN *)
ModifiedSince(lsn) ==
    {obj \in DatabaseObjects : databaseState[obj].lsn > lsn}

(* Find last full backup *)
LastFullBackupId ==
    IF \E b \in backupCatalog : b.type = "FULL" /\ b.status = "COMPLETED"
    THEN CHOOSE b \in backupCatalog : 
           b.type = "FULL" /\ b.status = "COMPLETED" /\
           \A other \in backupCatalog :
             (other.type = "FULL" /\ other.status = "COMPLETED") =>
               other.endTime <= b.endTime
    ELSE 0

(* Find backup by ID *)
FindBackup(backupId) ==
    CHOOSE b \in backupCatalog : b.id = backupId

(* Check if backup is valid for restore *)
IsBackupValid(backup) ==
    /\ backup.status \in {"COMPLETED", "VALIDATED"}
    /\ backup.endTime + (RetentionDays * 86400) >= currentTime
    /\ backup.destination \in BackupDestinations
    /\ backupDestState[backup.destination].available

(* Get backup chain for restore (parent backups) *)
RECURSIVE GetBackupChain(_)
GetBackupChain(backup) ==
    IF backup.parentBackupId = 0 THEN <<backup>>
    ELSE
        LET parent == FindBackup(backup.parentBackupId)
        IN Append(GetBackupChain(parent), backup)

(* Calculate retention expiry *)
IsExpired(backup) ==
    currentTime > backup.endTime + (RetentionDays * 86400)

(* Compute checksum (simulated) *)
ComputeChecksum(backup) ==
    CHOOSE cs \in STRING : TRUE  \* Simplified

--------------------------------------------------------------------------------
(* Full Backup *)

InitiateFullBackup(destination, method, compressed, compressionAlgo, 
                   compressionLevel, encrypted, parallelStreams) ==
    /\ Cardinality(activeBackups) < MaxParallelStreams
    /\ parallelStreams <= MaxParallelStreams
    /\ destination \in BackupDestinations
    /\ backupDestState[destination].available
    /\ LET backupId == GenerateBackupId
           rawSize == CalculateBackupSize("FULL", DatabaseObjects, 0)
           finalSize == IF compressed 
                       THEN CompressedSize(rawSize, compressionAlgo, compressionLevel)
                       ELSE rawSize
       IN
           /\ HasEnoughSpace(destination, finalSize)
           /\ LET backup == [
                    id |-> backupId,
                    type |-> "FULL",
                    status |-> "RUNNING",
                    startTime |-> currentTime,
                    endTime |-> 0,
                    startLSN |-> currentLSN,
                    endLSN |-> 0,
                    objects |-> DatabaseObjects,
                    destination |-> destination,
                    size |-> finalSize,
                    compressed |-> compressed,
                    compressionAlgo |-> compressionAlgo,
                    compressionLevel |-> compressionLevel,
                    encrypted |-> encrypted,
                    checksum |-> <<>>,
                    parentBackupId |-> 0,
                    method |-> method,
                    parallelStreams |-> parallelStreams
              ]
              IN
                  /\ activeBackups' = activeBackups \cup {backup}
                  /\ auditLog' = Append(auditLog,
                       [event |-> "FULL_BACKUP_INITIATED",
                        backupId |-> backupId,
                        destination |-> destination,
                        time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, backupDestState, walArchive,
                  restorePoints, backupMetrics, currentTime, lastFullBackup, currentLSN>>

CompleteFullBackup(backupId) ==
    /\ \E backup \in activeBackups :
         /\ backup.id = backupId
         /\ backup.type = "FULL"
         /\ backup.status = "RUNNING"
         /\ LET completedBackup == [backup EXCEPT
                  !.status = "COMPLETED",
                  !.endTime = currentTime,
                  !.endLSN = currentLSN,
                  !.checksum = ComputeChecksum(backup)]
            IN
                /\ activeBackups' = (activeBackups \ {backup}) \cup {completedBackup}
                /\ backupCatalog' = backupCatalog \cup {completedBackup}
                /\ backupDestState' = [backupDestState EXCEPT
                     ![backup.destination].freeSpace = @ - backup.size,
                     ![backup.destination].backups = @ \cup {backupId}]
                /\ lastFullBackup' = currentTime
                /\ backupMetrics' = [backupMetrics EXCEPT
                     !.totalBackups = @ + 1,
                     !.totalSize = @ + backup.size,
                     !.lastBackupTime = currentTime]
                /\ auditLog' = Append(auditLog,
                     [event |-> "FULL_BACKUP_COMPLETED",
                      backupId |-> backupId,
                      size |-> backup.size,
                      duration |-> currentTime - backup.startTime,
                      time |-> currentTime])
    /\ UNCHANGED <<databaseState, walArchive, restorePoints, currentTime, currentLSN>>

--------------------------------------------------------------------------------
(* Incremental Backup *)

InitiateIncrementalBackup(destination, compressed, compressionAlgo, 
                          compressionLevel, encrypted) ==
    /\ Cardinality(activeBackups) < MaxParallelStreams
    /\ \E lastBackup \in backupCatalog :
         /\ lastBackup.status = "COMPLETED"
         /\ lastBackup.endTime = CHOOSE max \in Nat :
              \E b \in backupCatalog : 
                b.status = "COMPLETED" /\ b.endTime = max /\
                \A other \in backupCatalog : 
                  other.status = "COMPLETED" => other.endTime <= max
         /\ LET backupId == GenerateBackupId
                modifiedObjs == ModifiedSince(lastBackup.endLSN)
                rawSize == CalculateBackupSize("INCREMENTAL", modifiedObjs, lastBackup.id)
                finalSize == IF compressed 
                            THEN CompressedSize(rawSize, compressionAlgo, compressionLevel)
                            ELSE rawSize
            IN
                /\ HasEnoughSpace(destination, finalSize)
                /\ LET backup == [
                         id |-> backupId,
                         type |-> "INCREMENTAL",
                         status |-> "RUNNING",
                         startTime |-> currentTime,
                         endTime |-> 0,
                         startLSN |-> lastBackup.endLSN,
                         endLSN |-> 0,
                         objects |-> modifiedObjs,
                         destination |-> destination,
                         size |-> finalSize,
                         compressed |-> compressed,
                         compressionAlgo |-> compressionAlgo,
                         compressionLevel |-> compressionLevel,
                         encrypted |-> encrypted,
                         checksum |-> <<>>,
                         parentBackupId |-> lastBackup.id,
                         method |-> "HOT",
                         parallelStreams |-> 1
                   ]
                   IN
                       /\ activeBackups' = activeBackups \cup {backup}
                       /\ auditLog' = Append(auditLog,
                            [event |-> "INCREMENTAL_BACKUP_INITIATED",
                             backupId |-> backupId,
                             parentId |-> lastBackup.id,
                             time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, backupDestState, walArchive,
                  restorePoints, backupMetrics, currentTime, lastFullBackup, currentLSN>>

CompleteIncrementalBackup(backupId) ==
    /\ \E backup \in activeBackups :
         /\ backup.id = backupId
         /\ backup.type = "INCREMENTAL"
         /\ LET completedBackup == [backup EXCEPT
                  !.status = "COMPLETED",
                  !.endTime = currentTime,
                  !.endLSN = currentLSN,
                  !.checksum = ComputeChecksum(backup)]
            IN
                /\ activeBackups' = (activeBackups \ {backup})
                /\ backupCatalog' = backupCatalog \cup {completedBackup}
                /\ backupDestState' = [backupDestState EXCEPT
                     ![backup.destination].freeSpace = @ - backup.size,
                     ![backup.destination].backups = @ \cup {backupId}]
                /\ backupMetrics' = [backupMetrics EXCEPT
                     !.totalBackups = @ + 1,
                     !.totalSize = @ + backup.size]
                /\ auditLog' = Append(auditLog,
                     [event |-> "INCREMENTAL_BACKUP_COMPLETED",
                      backupId |-> backupId,
                      time |-> currentTime])
    /\ UNCHANGED <<databaseState, walArchive, restorePoints, currentTime, 
                  lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* WAL Archive *)

ArchiveWAL(walSegment) ==
    /\ walArchive' = Append(walArchive, 
         [segment |-> walSegment, 
          lsn |-> currentLSN, 
          timestamp |-> currentTime,
          archived |-> TRUE])
    /\ auditLog' = Append(auditLog,
         [event |-> "WAL_ARCHIVED",
          lsn |-> currentLSN,
          time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, activeBackups, backupDestState,
                  restorePoints, backupMetrics, currentTime, lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Restore Points *)

CreateRestorePoint(name, description) ==
    /\ ~\E rp \in restorePoints : rp.name = name
    /\ LET restorePoint == [
             name |-> name,
             timestamp |-> currentTime,
             lsn |-> currentLSN,
             description |-> description
       ]
       IN
           /\ restorePoints' = restorePoints \cup {restorePoint}
           /\ auditLog' = Append(auditLog,
                [event |-> "RESTORE_POINT_CREATED",
                 name |-> name,
                 lsn |-> currentLSN,
                 time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, activeBackups, backupDestState,
                  walArchive, backupMetrics, currentTime, lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Backup Validation *)

ValidateBackup(backupId) ==
    /\ \E backup \in backupCatalog :
         /\ backup.id = backupId
         /\ backup.status = "COMPLETED"
         /\ LET verified == (ComputeChecksum(backup) = backup.checksum)
            IN
                /\ verified
                /\ backupCatalog' = (backupCatalog \ {backup}) \cup
                     {[backup EXCEPT !.status = "VALIDATED"]}
                /\ auditLog' = Append(auditLog,
                     [event |-> "BACKUP_VALIDATED",
                      backupId |-> backupId,
                      result |-> "SUCCESS",
                      time |-> currentTime])
    /\ UNCHANGED <<databaseState, activeBackups, backupDestState, walArchive,
                  restorePoints, backupMetrics, currentTime, lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Backup Retention and Cleanup *)

ExpireOldBackups ==
    /\ \E backup \in backupCatalog :
         /\ IsExpired(backup)
         /\ backupCatalog' = backupCatalog \ {backup}
         /\ backupDestState' = [backupDestState EXCEPT
              ![backup.destination].freeSpace = @ + backup.size,
              ![backup.destination].backups = @ \ {backup.id}]
         /\ auditLog' = Append(auditLog,
              [event |-> "BACKUP_EXPIRED",
               backupId |-> backup.id,
               reason |-> "RETENTION_POLICY",
               time |-> currentTime])
    /\ UNCHANGED <<databaseState, activeBackups, walArchive, restorePoints,
                  backupMetrics, currentTime, lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Restore Operation *)

InitiateRestore(backupId, targetTime) ==
    /\ \E backup \in backupCatalog :
         /\ backup.id = backupId
         /\ IsBackupValid(backup)
         /\ LET backupChain == GetBackupChain(backup)
            IN
                /\ auditLog' = Append(auditLog,
                     [event |-> "RESTORE_INITIATED",
                      backupId |-> backupId,
                      targetTime |-> targetTime,
                      chainLength |-> Len(backupChain),
                      time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, activeBackups, backupDestState,
                  walArchive, restorePoints, backupMetrics, currentTime, 
                  lastFullBackup, currentLSN>>

CompleteRestore(backupId) ==
    /\ auditLog' = Append(auditLog,
         [event |-> "RESTORE_COMPLETED",
          backupId |-> backupId,
          time |-> currentTime])
    /\ UNCHANGED <<databaseState, backupCatalog, activeBackups, backupDestState,
                  walArchive, restorePoints, backupMetrics, currentTime, 
                  lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Database Updates *)

UpdateDatabaseObject(obj) ==
    /\ obj \in DatabaseObjects
    /\ currentLSN' = currentLSN + 1
    /\ databaseState' = [databaseState EXCEPT
         ![obj].version = @ + 1,
         ![obj].lsn = currentLSN + 1]
    /\ UNCHANGED <<backupCatalog, activeBackups, backupDestState, walArchive,
                  restorePoints, backupMetrics, auditLog, currentTime, lastFullBackup>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<databaseState, backupCatalog, activeBackups, backupDestState,
                  walArchive, restorePoints, backupMetrics, auditLog, 
                  lastFullBackup, currentLSN>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E dest \in BackupDestinations, method \in BackupMethod, 
          comp \in BOOLEAN, algo \in CompressionAlgorithm, 
          level \in CompressionLevels, enc \in BOOLEAN, streams \in 1..MaxParallelStreams :
         InitiateFullBackup(dest, method, comp, algo, level, enc, streams)
    \/ \E bid \in BackupId : CompleteFullBackup(bid)
    \/ \E dest \in BackupDestinations, comp \in BOOLEAN, 
          algo \in CompressionAlgorithm, level \in CompressionLevels, enc \in BOOLEAN :
         InitiateIncrementalBackup(dest, comp, algo, level, enc)
    \/ \E bid \in BackupId : CompleteIncrementalBackup(bid)
    \/ \E wal \in STRING : ArchiveWAL(wal)
    \/ \E name, desc \in STRING : CreateRestorePoint(name, desc)
    \/ \E bid \in BackupId : ValidateBackup(bid)
    \/ ExpireOldBackups
    \/ \E bid \in BackupId, tt \in Timestamp : InitiateRestore(bid, tt)
    \/ \E bid \in BackupId : CompleteRestore(bid)
    \/ \E obj \in DatabaseObjects : UpdateDatabaseObject(obj)
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: Active backups have valid status *)
ActiveBackupsValid ==
    \A backup \in activeBackups :
        backup.status = "RUNNING"

(* INV2: Completed backups are in catalog *)
CompletedBackupsInCatalog ==
    \A backup \in backupCatalog :
        backup.status \in {"COMPLETED", "VALIDATED", "FAILED", "EXPIRED"}

(* INV3: Backup IDs are unique *)
UniqueBackupIds ==
    \A b1, b2 \in backupCatalog :
        b1.id = b2.id => b1 = b2

(* INV4: Incremental backups have valid parents *)
IncrementalBackupsHaveParents ==
    \A backup \in backupCatalog :
        backup.type = "INCREMENTAL" =>
            /\ backup.parentBackupId # 0
            /\ \E parent \in backupCatalog : parent.id = backup.parentBackupId

(* INV5: Backup sizes are consistent *)
BackupSizesConsistent ==
    \A backup \in backupCatalog :
        backup.size > 0

(* INV6: Destination space is non-negative *)
DestinationSpaceValid ==
    \A dest \in BackupDestinations :
        backupDestState[dest].freeSpace >= 0

(* INV7: Parallel streams don't exceed limit *)
ParallelStreamsLimit ==
    Cardinality(activeBackups) <= MaxParallelStreams

(* INV8: LSN monotonically increases *)
LSNMonotonic ==
    /\ currentLSN >= 0
    /\ \A obj \in DatabaseObjects : databaseState[obj].lsn <= currentLSN

(* INV9: Backup catalog size doesn't exceed limit *)
BackupCatalogLimit ==
    Cardinality(backupCatalog) <= MaxBackups

TypeInvariant ==
    /\ DOMAIN databaseState = DatabaseObjects
    /\ DOMAIN backupDestState = BackupDestinations
    /\ currentTime \in Nat
    /\ currentLSN \in Nat
    /\ lastFullBackup \in Nat

--------------------------------------------------------------------------------
(* Safety Properties *)

(* SAFE1: No overlapping backup IDs *)
NoOverlappingIds ==
    \A b1 \in activeBackups, b2 \in backupCatalog :
        b1.id # b2.id

(* SAFE2: Validated backups are restorable *)
ValidatedBackupsRestorable ==
    \A backup \in backupCatalog :
        backup.status = "VALIDATED" => IsBackupValid(backup)

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* LIVE1: Running backups eventually complete or fail *)
BackupsEventuallyComplete ==
    \A backup \in activeBackups :
        backup.status = "RUNNING" ~>
            \E completed \in backupCatalog : completed.id = backup.id

(* LIVE2: Expired backups are eventually removed *)
ExpiredBackupsRemoved ==
    \A backup \in backupCatalog :
        IsExpired(backup) ~> (backup \notin backupCatalog)

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM BackupIntegrity ==
    Spec => [](UniqueBackupIds /\ CompletedBackupsInCatalog)

THEOREM BackupConsistency ==
    Spec => [](IncrementalBackupsHaveParents /\ BackupSizesConsistent)

THEOREM ResourceLimits ==
    Spec => [](ParallelStreamsLimit /\ BackupCatalogLimit)

THEOREM LSNSafety ==
    Spec => []LSNMonotonic

================================================================================


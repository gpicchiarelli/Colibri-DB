------------------------------- MODULE Backup -------------------------------
(*
  ColibrìDB Backup Specification
  
  Manages database backup including:
  - Full and incremental backups
  - Backup scheduling and retention
  - Backup verification and integrity
  - Compression and encryption
  - Restore operations
  - Backup monitoring and alerts
  
  Based on:
  - PostgreSQL Backup and Recovery (2019)
  - MySQL Backup and Recovery (2018)
  - Oracle Backup and Recovery (2020)
  - MongoDB Backup and Recovery (2021)
  - AWS RDS Backup Best Practices
  
  Key Properties:
  - Reliability: Backup data integrity
  - Efficiency: Minimal performance impact
  - Completeness: All data backed up
  - Security: Encrypted backups
  - Recoverability: Successful restore operations
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxBackupRetention,    \* Maximum backup retention days
  BackupCompressionLevel, \* Compression level for backups
  BackupEncryptionKey,   \* Encryption key for backups
  MaxBackupSize,         \* Maximum backup size
  BackupTimeout,         \* Timeout for backup operations
  MaxConcurrentBackups   \* Maximum concurrent backup operations

VARIABLES
  backups,               \* [BackupId -> Backup]
  backupJobs,            \* [JobId -> BackupJob]
  backupSchedules,       \* [ScheduleId -> BackupSchedule]
  restoreJobs,           \* [JobId -> RestoreJob]
  backupPolicies,        \* [PolicyId -> BackupPolicy]
  backupStorage,         \* [StorageId -> BackupStorage]
  backupVerification,    \* [BackupId -> BackupVerification]
  backupMonitoring       \* BackupMonitoring

backupVars == <<backups, backupJobs, backupSchedules, restoreJobs, backupPolicies, 
               backupStorage, backupVerification, backupMonitoring>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Backup record
Backup == [
  backupId: Nat,
  backupType: {"full", "incremental", "differential"},
  databaseName: STRING,
    startTime: Timestamp,
    endTime: Timestamp,
    size: Nat,
  compressedSize: Nat,
  isEncrypted: BOOLEAN,
  isCompressed: BOOLEAN,
  status: {"pending", "running", "completed", "failed", "cancelled"},
  storageLocation: STRING,
  checksum: Nat,
  isVerified: BOOLEAN,
  retentionDate: Timestamp
]

\* Backup job
BackupJob == [
  jobId: Nat,
  backupId: Nat,
  scheduleId: Nat,
  priority: Nat,  \* 1-10
  status: {"pending", "running", "completed", "failed", "cancelled"},
  startTime: Timestamp,
  endTime: Timestamp,
  progress: Nat,  \* 0-100
  errorMessage: STRING,
  isScheduled: BOOLEAN
]

\* Backup schedule
BackupSchedule == [
  scheduleId: Nat,
  scheduleName: STRING,
  databaseName: STRING,
  backupType: {"full", "incremental", "differential"},
  frequency: {"hourly", "daily", "weekly", "monthly"},
  startTime: Nat,  \* Hour of day
  isEnabled: BOOLEAN,
  retentionDays: Nat,
  compressionEnabled: BOOLEAN,
  encryptionEnabled: BOOLEAN,
  lastRun: Timestamp,
  nextRun: Timestamp
]

\* Restore job
RestoreJob == [
  jobId: Nat,
  backupId: Nat,
  targetDatabase: STRING,
  restoreType: {"full", "partial", "point_in_time"},
  startTime: Timestamp,
  endTime: Timestamp,
  status: {"pending", "running", "completed", "failed", "cancelled"},
  progress: Nat,  \* 0-100
  errorMessage: STRING,
  isVerified: BOOLEAN
]

\* Backup policy
BackupPolicy == [
  policyId: Nat,
  policyName: STRING,
  databaseName: STRING,
  fullBackupFrequency: {"daily", "weekly", "monthly"},
  incrementalBackupFrequency: {"hourly", "daily"},
  retentionDays: Nat,
  compressionLevel: Nat,
  encryptionEnabled: BOOLEAN,
  verificationEnabled: BOOLEAN,
  isActive: BOOLEAN
]

\* Backup storage
BackupStorage == [
  storageId: Nat,
  storageName: STRING,
  storageType: {"local", "network", "cloud"},
  path: STRING,
  maxCapacity: Nat,
  usedCapacity: Nat,
  availableCapacity: Nat,
  isEncrypted: BOOLEAN,
  isCompressed: BOOLEAN,
  isActive: BOOLEAN
]

\* Backup verification
BackupVerification == [
  backupId: Nat,
  verificationType: {"checksum", "restore_test", "integrity_check"},
  status: {"pending", "running", "passed", "failed"},
  startTime: Timestamp,
  endTime: Timestamp,
  errorMessage: STRING,
  isVerified: BOOLEAN
]

\* Backup monitoring
BackupMonitoring == [
  totalBackups: Nat,
  successfulBackups: Nat,
  failedBackups: Nat,
  totalSize: Nat,
  averageBackupTime: Nat,
  lastBackupTime: Timestamp,
  nextScheduledBackup: Timestamp,
  storageUtilization: Nat,  \* 0-100
  isHealthy: BOOLEAN
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Backup ==
  /\ backups \in [Nat -> Backup]
  /\ backupJobs \in [Nat -> BackupJob]
  /\ backupSchedules \in [Nat -> BackupSchedule]
  /\ restoreJobs \in [Nat -> RestoreJob]
  /\ backupPolicies \in [Nat -> BackupPolicy]
  /\ backupStorage \in [Nat -> BackupStorage]
  /\ backupVerification \in [Nat -> BackupVerification]
  /\ backupMonitoring \in BackupMonitoring

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ backups = [b \in {} |-> [
       backupId |-> 0,
       backupType |-> "full",
       databaseName |-> "",
       startTime |-> 0,
       endTime |-> 0,
       size |-> 0,
       compressedSize |-> 0,
       isEncrypted |-> FALSE,
       isCompressed |-> FALSE,
       status |-> "pending",
       storageLocation |-> "",
       checksum |-> 0,
       isVerified |-> FALSE,
       retentionDate |-> 0
     ]]
  /\ backupJobs = [j \in {} |-> [
       jobId |-> 0,
       backupId |-> 0,
       scheduleId |-> 0,
       priority |-> 5,
       status |-> "pending",
       startTime |-> 0,
       endTime |-> 0,
       progress |-> 0,
       errorMessage |-> "",
       isScheduled |-> FALSE
     ]]
  /\ backupSchedules = [s \in {} |-> [
       scheduleId |-> 0,
       scheduleName |-> "",
       databaseName |-> "",
       backupType |-> "full",
       frequency |-> "daily",
       startTime |-> 0,
       isEnabled |-> FALSE,
       retentionDays |-> 7,
       compressionEnabled |-> TRUE,
       encryptionEnabled |-> FALSE,
       lastRun |-> 0,
       nextRun |-> 0
     ]]
  /\ restoreJobs = [j \in {} |-> [
       jobId |-> 0,
       backupId |-> 0,
       targetDatabase |-> "",
       restoreType |-> "full",
       startTime |-> 0,
       endTime |-> 0,
       status |-> "pending",
       progress |-> 0,
       errorMessage |-> "",
       isVerified |-> FALSE
     ]]
  /\ backupPolicies = [p \in {} |-> [
       policyId |-> 0,
       policyName |-> "",
       databaseName |-> "",
       fullBackupFrequency |-> "daily",
       incrementalBackupFrequency |-> "hourly",
       retentionDays |-> 7,
       compressionLevel |-> 6,
       encryptionEnabled |-> FALSE,
       verificationEnabled |-> TRUE,
       isActive |-> FALSE
     ]]
  /\ backupStorage = [s \in {} |-> [
       storageId |-> 0,
       storageName |-> "",
       storageType |-> "local",
       path |-> "",
       maxCapacity |-> 0,
       usedCapacity |-> 0,
       availableCapacity |-> 0,
       isEncrypted |-> FALSE,
       isCompressed |-> FALSE,
       isActive |-> FALSE
     ]]
  /\ backupVerification = [v \in {} |-> [
       backupId |-> 0,
       verificationType |-> "checksum",
       status |-> "pending",
       startTime |-> 0,
       endTime |-> 0,
       errorMessage |-> "",
       isVerified |-> FALSE
     ]]
  /\ backupMonitoring = [
       totalBackups |-> 0,
       successfulBackups |-> 0,
       failedBackups |-> 0,
       totalSize |-> 0,
       averageBackupTime |-> 0,
       lastBackupTime |-> 0,
       nextScheduledBackup |-> 0,
       storageUtilization |-> 0,
       isHealthy |-> TRUE
     ]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Start backup
StartBackup(backupId, backupType, databaseName, isEncrypted, isCompressed) ==
  /\ ~(backupId \in DOMAIN backups)
           /\ LET backup == [
       backupId |-> backupId,
       backupType |-> backupType,
       databaseName |-> databaseName,
       startTime |-> globalTimestamp,
                    endTime |-> 0,
       size |-> 0,
       compressedSize |-> 0,
       isEncrypted |-> isEncrypted,
       isCompressed |-> isCompressed,
       status |-> "running",
       storageLocation |-> "",
       checksum |-> 0,
       isVerified |-> FALSE,
       retentionDate |-> globalTimestamp + (MaxBackupRetention * 24 * 3600)
     ]
  IN /\ backups' = [backups EXCEPT ![backupId] = backup]
     /\ UNCHANGED <<backupJobs, backupSchedules, restoreJobs, backupPolicies, 
                   backupStorage, backupVerification, backupMonitoring>>

\* Complete backup
CompleteBackup(backupId, size, compressedSize, storageLocation, checksum, success, errorMessage) ==
  /\ backupId \in DOMAIN backups
  /\ LET backup == backups[backupId]
       updatedBackup == [backup EXCEPT 
                        !.endTime = globalTimestamp,
                        !.size = size,
                        !.compressedSize = compressedSize,
                        !.storageLocation = storageLocation,
                        !.checksum = checksum,
                        !.status = IF success THEN "completed" ELSE "failed"]
  IN /\ backups' = [backups EXCEPT ![backupId] = updatedBackup]
     /\ backupMonitoring' = [backupMonitoring EXCEPT 
                            !.totalBackups = backupMonitoring.totalBackups + 1,
                            !.successfulBackups = IF success THEN backupMonitoring.successfulBackups + 1 
                                                 ELSE backupMonitoring.successfulBackups,
                            !.failedBackups = IF success THEN backupMonitoring.failedBackups 
                                             ELSE backupMonitoring.failedBackups + 1,
                            !.totalSize = backupMonitoring.totalSize + size,
                            !.lastBackupTime = globalTimestamp]
     /\ UNCHANGED <<backupJobs, backupSchedules, restoreJobs, backupPolicies, 
                   backupStorage, backupVerification>>

\* Start restore
StartRestore(jobId, backupId, targetDatabase, restoreType) ==
  /\ ~(jobId \in DOMAIN restoreJobs)
  /\ backupId \in DOMAIN backups
  /\ LET restoreJob == [
       jobId |-> jobId,
                      backupId |-> backupId,
       targetDatabase |-> targetDatabase,
       restoreType |-> restoreType,
       startTime |-> globalTimestamp,
                         endTime |-> 0,
       status |-> "running",
       progress |-> 0,
       errorMessage |-> "",
       isVerified |-> FALSE
     ]
  IN /\ restoreJobs' = [restoreJobs EXCEPT ![jobId] = restoreJob]
     /\ UNCHANGED <<backups, backupJobs, backupSchedules, backupPolicies, 
                   backupStorage, backupVerification, backupMonitoring>>

\* Complete restore
CompleteRestore(jobId, success, errorMessage) ==
  /\ jobId \in DOMAIN restoreJobs
  /\ LET restoreJob == restoreJobs[jobId]
       updatedRestoreJob == [restoreJob EXCEPT 
                            !.endTime = globalTimestamp,
                            !.status = IF success THEN "completed" ELSE "failed",
                            !.errorMessage = errorMessage,
                            !.isVerified = success]
  IN /\ restoreJobs' = [restoreJobs EXCEPT ![jobId] = updatedRestoreJob]
     /\ UNCHANGED <<backups, backupJobs, backupSchedules, backupPolicies, 
                   backupStorage, backupVerification, backupMonitoring>>

\* Verify backup
VerifyBackup(backupId, verificationType, success, errorMessage) ==
  /\ backupId \in DOMAIN backups
  /\ LET verification == [
                      backupId |-> backupId,
       verificationType |-> verificationType,
       status |-> IF success THEN "passed" ELSE "failed",
       startTime |-> globalTimestamp,
       endTime |-> globalTimestamp,
       errorMessage |-> errorMessage,
       isVerified |-> success
     ]
  IN /\ backupVerification' = [backupVerification EXCEPT ![backupId] = verification]
     /\ backups' = [backups EXCEPT ![backupId] = [backups[backupId] EXCEPT 
                   !.isVerified = success]]
     /\ UNCHANGED <<backupJobs, backupSchedules, restoreJobs, backupPolicies, 
                   backupStorage, backupMonitoring>>

\* Schedule backup
ScheduleBackup(scheduleId, scheduleName, databaseName, backupType, frequency, 
               startTime, retentionDays, compressionEnabled, encryptionEnabled) ==
  /\ ~(scheduleId \in DOMAIN backupSchedules)
  /\ LET schedule == [
       scheduleId |-> scheduleId,
       scheduleName |-> scheduleName,
       databaseName |-> databaseName,
       backupType |-> backupType,
       frequency |-> frequency,
       startTime |-> startTime,
       isEnabled |-> TRUE,
       retentionDays |-> retentionDays,
       compressionEnabled |-> compressionEnabled,
       encryptionEnabled |-> encryptionEnabled,
       lastRun |-> 0,
       nextRun |-> CalculateNextRunTime(frequency, startTime)
     ]
  IN /\ backupSchedules' = [backupSchedules EXCEPT ![scheduleId] = schedule]
     /\ UNCHANGED <<backups, backupJobs, restoreJobs, backupPolicies, 
                   backupStorage, backupVerification, backupMonitoring>>

\* Create backup policy
CreateBackupPolicy(policyId, policyName, databaseName, fullBackupFrequency, 
                  incrementalBackupFrequency, retentionDays, compressionLevel, 
                  encryptionEnabled, verificationEnabled) ==
  /\ ~(policyId \in DOMAIN backupPolicies)
  /\ LET policy == [
       policyId |-> policyId,
       policyName |-> policyName,
       databaseName |-> databaseName,
       fullBackupFrequency |-> fullBackupFrequency,
       incrementalBackupFrequency |-> incrementalBackupFrequency,
       retentionDays |-> retentionDays,
       compressionLevel |-> compressionLevel,
       encryptionEnabled |-> encryptionEnabled,
       verificationEnabled |-> verificationEnabled,
       isActive |-> TRUE
     ]
  IN /\ backupPolicies' = [backupPolicies EXCEPT ![policyId] = policy]
     /\ UNCHANGED <<backups, backupJobs, backupSchedules, restoreJobs, 
                   backupStorage, backupVerification, backupMonitoring>>

\* Add backup storage
AddBackupStorage(storageId, storageName, storageType, path, maxCapacity, 
                isEncrypted, isCompressed) ==
  /\ ~(storageId \in DOMAIN backupStorage)
  /\ LET storage == [
       storageId |-> storageId,
       storageName |-> storageName,
       storageType |-> storageType,
       path |-> path,
       maxCapacity |-> maxCapacity,
       usedCapacity |-> 0,
       availableCapacity |-> maxCapacity,
       isEncrypted |-> isEncrypted,
       isCompressed |-> isCompressed,
       isActive |-> TRUE
     ]
  IN /\ backupStorage' = [backupStorage EXCEPT ![storageId] = storage]
     /\ UNCHANGED <<backups, backupJobs, backupSchedules, restoreJobs, 
                   backupPolicies, backupVerification, backupMonitoring>>

\* Update backup monitoring
UpdateBackupMonitoring() ==
  /\ LET totalBackups == Len(DOMAIN backups)
       successfulBackups == Len({backupId \in DOMAIN backups : backups[backupId].status = "completed"})
       failedBackups == Len({backupId \in DOMAIN backups : backups[backupId].status = "failed"})
       totalSize == SumBackupSizes()
       averageBackupTime == CalculateAverageBackupTime()
       lastBackupTime == GetLastBackupTime()
       nextScheduledBackup == GetNextScheduledBackup()
       storageUtilization == CalculateStorageUtilization()
       isHealthy == successfulBackups > 0 /\ failedBackups < totalBackups / 2
       monitoring == [
         totalBackups |-> totalBackups,
         successfulBackups |-> successfulBackups,
         failedBackups |-> failedBackups,
         totalSize |-> totalSize,
         averageBackupTime |-> averageBackupTime,
         lastBackupTime |-> lastBackupTime,
         nextScheduledBackup |-> nextScheduledBackup,
         storageUtilization |-> storageUtilization,
         isHealthy |-> isHealthy
       ]
  IN /\ backupMonitoring' = monitoring
     /\ UNCHANGED <<backups, backupJobs, backupSchedules, restoreJobs, 
                   backupPolicies, backupStorage, backupVerification>>

\* Cleanup expired backups
CleanupExpiredBackups() ==
  /\ LET currentTime == globalTimestamp
       expiredBackups == {backupId \in DOMAIN backups : 
                         backups[backupId].retentionDate < currentTime}
  IN /\ backups' = [b \in DOMAIN backups \ expiredBackups |-> backups[b]]
     /\ UNCHANGED <<backupJobs, backupSchedules, restoreJobs, backupPolicies, 
                   backupStorage, backupVerification, backupMonitoring>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Calculate next run time for schedule
CalculateNextRunTime(frequency, startTime) ==
  CASE frequency
    OF "hourly" -> globalTimestamp + 3600
    [] "daily" -> globalTimestamp + (24 * 3600)
    [] "weekly" -> globalTimestamp + (7 * 24 * 3600)
    [] "monthly" -> globalTimestamp + (30 * 24 * 3600)
  ENDCASE

\* Sum backup sizes
SumBackupSizes() ==
  IF DOMAIN backups = {} THEN 0
  ELSE LET backupId == CHOOSE b \in DOMAIN backups : TRUE
           backup == backups[backupId]
           restBackups == [b \in DOMAIN backups \ {backupId} |-> backups[b]]
       IN backup.size + SumBackupSizes()

\* Calculate average backup time
CalculateAverageBackupTime() ==
  IF DOMAIN backups = {} THEN 0
  ELSE LET totalTime == SumBackupTimes()
           backupCount == Len(DOMAIN backups)
       IN totalTime / backupCount

\* Sum backup times
SumBackupTimes() ==
  IF DOMAIN backups = {} THEN 0
  ELSE LET backupId == CHOOSE b \in DOMAIN backups : TRUE
           backup == backups[backupId]
           restBackups == [b \in DOMAIN backups \ {backupId} |-> backups[b]]
       IN (backup.endTime - backup.startTime) + SumBackupTimes()

\* Get last backup time
GetLastBackupTime() ==
  IF DOMAIN backups = {} THEN 0
  ELSE LET backupTimes == {backups[backupId].endTime : backupId \in DOMAIN backups}
       IN Max(backupTimes)

\* Get next scheduled backup
GetNextScheduledBackup() ==
  IF DOMAIN backupSchedules = {} THEN 0
  ELSE LET scheduleTimes == {backupSchedules[scheduleId].nextRun : scheduleId \in DOMAIN backupSchedules}
       IN Min(scheduleTimes)

\* Calculate storage utilization
CalculateStorageUtilization() ==
  IF DOMAIN backupStorage = {} THEN 0
  ELSE LET totalUsed == SumStorageUsed()
           totalCapacity == SumStorageCapacity()
       IN IF totalCapacity = 0 THEN 0
          ELSE (totalUsed * 100) / totalCapacity

\* Sum storage used capacity
SumStorageUsed() ==
  IF DOMAIN backupStorage = {} THEN 0
  ELSE LET storageId == CHOOSE s \in DOMAIN backupStorage : TRUE
           storage == backupStorage[storageId]
           restStorage == [s \in DOMAIN backupStorage \ {storageId} |-> backupStorage[s]]
       IN storage.usedCapacity + SumStorageUsed()

\* Sum storage total capacity
SumStorageCapacity() ==
  IF DOMAIN backupStorage = {} THEN 0
  ELSE LET storageId == CHOOSE s \in DOMAIN backupStorage : TRUE
           storage == backupStorage[storageId]
           restStorage == [s \in DOMAIN backupStorage \ {storageId} |-> backupStorage[s]]
       IN storage.maxCapacity + SumStorageCapacity()

\* Check if backup is valid
IsBackupValid(backupId) ==
  backupId \in DOMAIN backups /\ 
  backups[backupId].status = "completed" /\ 
  backups[backupId].isVerified

\* Check if restore is possible
IsRestorePossible(backupId) ==
  IsBackupValid(backupId) /\ 
  backups[backupId].retentionDate > globalTimestamp

\* Get backup by type
GetBackupsByType(backupType) ==
  {backupId \in DOMAIN backups : backups[backupId].backupType = backupType}

\* Check if storage has capacity
HasStorageCapacity(storageId, requiredSize) ==
  storageId \in DOMAIN backupStorage /\ 
  backupStorage[storageId].availableCapacity >= requiredSize

\* Calculate backup priority
CalculateBackupPriority(backupType, isScheduled) ==
  CASE backupType
    OF "full" -> IF isScheduled THEN 8 ELSE 10
    [] "incremental" -> IF isScheduled THEN 6 ELSE 8
    [] "differential" -> IF isScheduled THEN 7 ELSE 9
  ENDCASE

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E backupId \in Nat, backupType \in {"full", "incremental", "differential"},
       databaseName \in STRING, isEncrypted \in BOOLEAN, isCompressed \in BOOLEAN :
       StartBackup(backupId, backupType, databaseName, isEncrypted, isCompressed)
  \/ \E backupId \in Nat, size \in Nat, compressedSize \in Nat, storageLocation \in STRING,
       checksum \in Nat, success \in BOOLEAN, errorMessage \in STRING :
       CompleteBackup(backupId, size, compressedSize, storageLocation, checksum, success, errorMessage)
  \/ \E jobId \in Nat, backupId \in Nat, targetDatabase \in STRING, 
       restoreType \in {"full", "partial", "point_in_time"} :
       StartRestore(jobId, backupId, targetDatabase, restoreType)
  \/ \E jobId \in Nat, success \in BOOLEAN, errorMessage \in STRING :
       CompleteRestore(jobId, success, errorMessage)
  \/ \E backupId \in Nat, verificationType \in {"checksum", "restore_test", "integrity_check"},
       success \in BOOLEAN, errorMessage \in STRING :
       VerifyBackup(backupId, verificationType, success, errorMessage)
  \/ \E scheduleId \in Nat, scheduleName \in STRING, databaseName \in STRING,
       backupType \in {"full", "incremental", "differential"}, 
       frequency \in {"hourly", "daily", "weekly", "monthly"}, startTime \in Nat,
       retentionDays \in Nat, compressionEnabled \in BOOLEAN, encryptionEnabled \in BOOLEAN :
       ScheduleBackup(scheduleId, scheduleName, databaseName, backupType, frequency,
                     startTime, retentionDays, compressionEnabled, encryptionEnabled)
  \/ \E policyId \in Nat, policyName \in STRING, databaseName \in STRING,
       fullBackupFrequency \in {"daily", "weekly", "monthly"},
       incrementalBackupFrequency \in {"hourly", "daily"}, retentionDays \in Nat,
       compressionLevel \in Nat, encryptionEnabled \in BOOLEAN, verificationEnabled \in BOOLEAN :
       CreateBackupPolicy(policyId, policyName, databaseName, fullBackupFrequency,
                         incrementalBackupFrequency, retentionDays, compressionLevel,
                         encryptionEnabled, verificationEnabled)
  \/ \E storageId \in Nat, storageName \in STRING, storageType \in {"local", "network", "cloud"},
       path \in STRING, maxCapacity \in Nat, isEncrypted \in BOOLEAN, isCompressed \in BOOLEAN :
       AddBackupStorage(storageId, storageName, storageType, path, maxCapacity,
                       isEncrypted, isCompressed)
  \/ UpdateBackupMonitoring()
  \/ CleanupExpiredBackups()

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Backup constraints
Inv_Backup_BackupConstraints ==
  \A backupId \in DOMAIN backups :
    LET backup == backups[backupId]
    IN /\ backup.size >= 0
       /\ backup.compressedSize >= 0
       /\ backup.startTime >= 0
       /\ backup.endTime >= backup.startTime
       /\ backup.retentionDate >= backup.startTime
       /\ backup.status \in {"pending", "running", "completed", "failed", "cancelled"}

\* Backup job constraints
Inv_Backup_JobConstraints ==
  \A jobId \in DOMAIN backupJobs :
    LET job == backupJobs[jobId]
    IN /\ job.priority >= 1 /\ job.priority <= 10
       /\ job.startTime >= 0
       /\ job.endTime >= job.startTime
       /\ job.progress >= 0 /\ job.progress <= 100
       /\ job.status \in {"pending", "running", "completed", "failed", "cancelled"}

\* Restore job constraints
Inv_Backup_RestoreJobConstraints ==
  \A jobId \in DOMAIN restoreJobs :
    LET job == restoreJobs[jobId]
    IN /\ job.startTime >= 0
       /\ job.endTime >= job.startTime
       /\ job.progress >= 0 /\ job.progress <= 100
       /\ job.status \in {"pending", "running", "completed", "failed", "cancelled"}

\* Backup schedule constraints
Inv_Backup_ScheduleConstraints ==
  \A scheduleId \in DOMAIN backupSchedules :
    LET schedule == backupSchedules[scheduleId]
    IN /\ schedule.startTime >= 0 /\ schedule.startTime <= 23
       /\ schedule.retentionDays > 0
       /\ schedule.frequency \in {"hourly", "daily", "weekly", "monthly"}
       /\ schedule.lastRun >= 0
       /\ schedule.nextRun >= schedule.lastRun

\* Backup policy constraints
Inv_Backup_PolicyConstraints ==
  \A policyId \in DOMAIN backupPolicies :
    LET policy == backupPolicies[policyId]
    IN /\ policy.retentionDays > 0
       /\ policy.compressionLevel >= 1 /\ policy.compressionLevel <= 22
       /\ policy.fullBackupFrequency \in {"daily", "weekly", "monthly"}
       /\ policy.incrementalBackupFrequency \in {"hourly", "daily"}

\* Backup storage constraints
Inv_Backup_StorageConstraints ==
  \A storageId \in DOMAIN backupStorage :
    LET storage == backupStorage[storageId]
    IN /\ storage.maxCapacity > 0
       /\ storage.usedCapacity >= 0
       /\ storage.availableCapacity >= 0
       /\ storage.usedCapacity + storage.availableCapacity = storage.maxCapacity
       /\ storage.storageType \in {"local", "network", "cloud"}

\* Backup verification constraints
Inv_Backup_VerificationConstraints ==
  \A backupId \in DOMAIN backupVerification :
    LET verification == backupVerification[backupId]
    IN /\ verification.startTime >= 0
       /\ verification.endTime >= verification.startTime
       /\ verification.status \in {"pending", "running", "passed", "failed"}

\* Backup monitoring constraints
Inv_Backup_MonitoringConstraints ==
  /\ backupMonitoring.totalBackups >= 0
  /\ backupMonitoring.successfulBackups >= 0
  /\ backupMonitoring.failedBackups >= 0
  /\ backupMonitoring.totalSize >= 0
  /\ backupMonitoring.averageBackupTime >= 0
  /\ backupMonitoring.storageUtilization >= 0 /\ backupMonitoring.storageUtilization <= 100
  /\ backupMonitoring.successfulBackups + backupMonitoring.failedBackups <= backupMonitoring.totalBackups

\* Backup integrity
Inv_Backup_Integrity ==
  \A backupId \in DOMAIN backups :
    LET backup == backups[backupId]
    IN backup.status = "completed" => backup.isVerified

\* Backup retention
Inv_Backup_Retention ==
  \A backupId \in DOMAIN backups :
    LET backup == backups[backupId]
    IN backup.retentionDate > backup.startTime

\* Storage capacity
Inv_Backup_StorageCapacity ==
  \A storageId \in DOMAIN backupStorage :
    LET storage == backupStorage[storageId]
    IN storage.usedCapacity <= storage.maxCapacity

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Backup jobs eventually complete
Liveness_BackupJobsComplete ==
  \A jobId \in DOMAIN backupJobs :
    backupJobs[jobId].status = "running" => 
    <>backupJobs[jobId].status \in {"completed", "failed", "cancelled"}

\* Restore jobs eventually complete
Liveness_RestoreJobsComplete ==
  \A jobId \in DOMAIN restoreJobs :
    restoreJobs[jobId].status = "running" => 
    <>restoreJobs[jobId].status \in {"completed", "failed", "cancelled"}

\* Backup verification eventually completes
Liveness_BackupVerificationComplete ==
  \A backupId \in DOMAIN backupVerification :
    backupVerification[backupId].status = "running" => 
    <>backupVerification[backupId].status \in {"passed", "failed"}

\* Expired backups are eventually cleaned up
Liveness_ExpiredBackupsCleanedUp ==
  \A backupId \in DOMAIN backups :
    backups[backupId].retentionDate < globalTimestamp => 
    <>~(backupId \in DOMAIN backups)

\* Backup monitoring is eventually updated
Liveness_BackupMonitoringUpdated ==
  backupMonitoring.lastBackupTime < globalTimestamp - 3600 => 
  <>backupMonitoring.lastBackupTime >= globalTimestamp - 3600

\* Scheduled backups eventually run
Liveness_ScheduledBackupsRun ==
  \A scheduleId \in DOMAIN backupSchedules :
    LET schedule == backupSchedules[scheduleId]
    IN schedule.isEnabled /\ schedule.nextRun <= globalTimestamp => 
       <>schedule.lastRun >= schedule.nextRun

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Backup size is bounded
THEOREM Backup_SizeBounded ==
  \A backupId \in DOMAIN backups :
    backups[backupId].size <= MaxBackupSize

\* Backup retention is respected
THEOREM Backup_RetentionRespected ==
  \A backupId \in DOMAIN backups :
    backups[backupId].retentionDate >= backups[backupId].startTime

\* Storage utilization is bounded
THEOREM Backup_StorageUtilizationBounded ==
  backupMonitoring.storageUtilization <= 100

\* Backup verification is reliable
THEOREM Backup_VerificationReliable ==
  \A backupId \in DOMAIN backups :
    backups[backupId].isVerified => 
    backupId \in DOMAIN backupVerification

\* Restore is possible for valid backups
THEOREM Backup_RestorePossible ==
  \A backupId \in DOMAIN backups :
    IsBackupValid(backupId) => IsRestorePossible(backupId)

\* Backup monitoring is consistent
THEOREM Backup_MonitoringConsistent ==
  backupMonitoring.successfulBackups + backupMonitoring.failedBackups <= backupMonitoring.totalBackups

\* Storage capacity is respected
THEOREM Backup_StorageCapacityRespected ==
  \A storageId \in DOMAIN backupStorage :
    backupStorage[storageId].usedCapacity <= backupStorage[storageId].maxCapacity

\* Backup compression is beneficial
THEOREM Backup_CompressionBeneficial ==
  \A backupId \in DOMAIN backups :
    LET backup == backups[backupId]
    IN backup.isCompressed => backup.compressedSize < backup.size

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - BackupManager.backups (Dictionary<UInt64, Backup>) → backups
  - BackupManager.backupJobs (Dictionary<UInt64, BackupJob>) → backupJobs
  - BackupManager.backupSchedules (Dictionary<UInt64, BackupSchedule>) → backupSchedules
  - BackupManager.restoreJobs (Dictionary<UInt64, RestoreJob>) → restoreJobs
  - BackupManager.backupPolicies (Dictionary<UInt64, BackupPolicy>) → backupPolicies
  - BackupManager.backupStorage (Dictionary<UInt64, BackupStorage>) → backupStorage
  
  USAGE:
  
  This module should be used with Recovery and other ColibrìDB modules:
  
  ---- MODULE Recovery ----
  EXTENDS Backup
  ...
  ====================
*)
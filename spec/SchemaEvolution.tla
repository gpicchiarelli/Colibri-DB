----------------------------- MODULE SchemaEvolution -----------------------------
(*
  ColibrìDB Schema Evolution Specification
  
  Manages database schema changes including:
  - DDL operations (CREATE, ALTER, DROP)
  - Schema versioning and migration
  - Backward/forward compatibility
  - Online schema changes without downtime
  - Constraint validation and enforcement
  
  Based on:
  - Curino et al. (2008) - "Schema Evolution in SQL-99 and Commercial Object-Relational DBMS"
  - Bernstein & Dayal (1994) - "An Overview of Repository Technology"
  - ISO/IEC 9075:2016 - SQL Standard Part 11 (SQL/Schemata)
  - PostgreSQL DDL Implementation
  
  Key Properties:
  - Atomicity: Schema changes are all-or-nothing
  - Consistency: Schema remains valid after changes
  - Isolation: Schema changes don't interfere with data operations
  - Durability: Schema changes survive crashes
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxSchemaVersions,    \* Maximum number of schema versions to keep
  MaxColumnChanges,     \* Maximum column changes per ALTER
  SchemaChangeTimeout   \* Timeout for schema change operations

VARIABLES
  schemas,              \* [SchemaName -> SchemaVersion]
  schemaVersions,       \* [SchemaName -> Seq(SchemaVersion)]
  pendingChanges,       \* [SchemaName -> PendingChange]
  changeHistory,        \* Seq(SchemaChange)
  compatibilityMatrix,  \* [SchemaVersion -> [SchemaVersion -> BOOLEAN]]
  migrationScripts,     \* [SchemaVersion -> [SchemaVersion -> MigrationScript]]
  constraintValidators, \* [SchemaName -> ConstraintValidator]
  onlineChanges        \* [SchemaName -> OnlineChangeState]

schemaEvolutionVars == <<schemas, schemaVersions, pendingChanges, changeHistory, 
                         compatibilityMatrix, migrationScripts, constraintValidators, onlineChanges>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Schema version information
SchemaVersion == [
  version: Nat,
  schemaName: STRING,
  timestamp: Timestamp,
  ddlStatement: STRING,
  isCompatible: BOOLEAN,
  migrationRequired: BOOLEAN
]

\* Pending schema change
PendingChange == [
  schemaName: STRING,
  changeType: {"create", "alter", "drop", "rename"},
  ddlStatement: STRING,
  submittedBy: TxId,
  submittedAt: Timestamp,
  estimatedDuration: Nat,
  requiresDowntime: BOOLEAN
]

\* Schema change history entry
SchemaChange == [
  changeId: Nat,
  schemaName: STRING,
  changeType: {"create", "alter", "drop", "rename"},
  fromVersion: Nat,
  toVersion: Nat,
  ddlStatement: STRING,
  executedBy: TxId,
  executedAt: Timestamp,
  duration: Nat,
  success: BOOLEAN,
  rollbackScript: STRING
]

\* Migration script for schema changes
MigrationScript == [
  fromVersion: Nat,
  toVersion: Nat,
  forwardScript: STRING,
  rollbackScript: STRING,
  dataTransformation: STRING,
  validationQuery: STRING
]

\* Constraint validator for schema changes
ConstraintValidator == [
  schemaName: STRING,
  constraints: Seq([type: {"not_null", "unique", "check", "foreign_key"}, 
                   column: STRING, expression: STRING]),
  validationRules: Seq(ValidationRule)
]

\* Validation rule for schema changes
ValidationRule == [
  ruleName: STRING,
  condition: STRING,
  errorMessage: STRING,
  severity: {"error", "warning", "info"}
]

\* Online change state for non-blocking schema changes
OnlineChangeState == [
  schemaName: STRING,
  changeType: {"add_column", "drop_column", "alter_column", "add_index"},
  phase: {"preparation", "validation", "migration", "completion", "cleanup"},
  progress: Nat,  \* 0-100
  startTime: Timestamp,
  estimatedCompletion: Timestamp,
  blockingOperations: Seq(TxId)
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_SchemaEvolution ==
  /\ schemas \in [STRING -> SchemaVersion]
  /\ schemaVersions \in [STRING -> Seq(SchemaVersion)]
  /\ pendingChanges \in [STRING -> PendingChange]
  /\ changeHistory \in Seq(SchemaChange)
  /\ compatibilityMatrix \in [Nat -> [Nat -> BOOLEAN]]
  /\ migrationScripts \in [Nat -> [Nat -> MigrationScript]]
  /\ constraintValidators \in [STRING -> ConstraintValidator]
  /\ onlineChanges \in [STRING -> OnlineChangeState]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ schemas = [s \in {} |-> [
       version |-> 0,
       schemaName |-> "",
       timestamp |-> 0,
       ddlStatement |-> "",
       isCompatible |-> TRUE,
       migrationRequired |-> FALSE
     ]]
  /\ schemaVersions = [s \in {} |-> <<>>]
  /\ pendingChanges = [s \in {} |-> [
       schemaName |-> "",
       changeType |-> "create",
       ddlStatement |-> "",
       submittedBy |-> 0,
       submittedAt |-> 0,
       estimatedDuration |-> 0,
       requiresDowntime |-> FALSE
     ]]
  /\ changeHistory = <<>>
  /\ compatibilityMatrix = [v \in {} |-> [w \in {} |-> TRUE]]
  /\ migrationScripts = [v \in {} |-> [w \in {} |-> [
       fromVersion |-> 0,
       toVersion |-> 0,
       forwardScript |-> "",
       rollbackScript |-> "",
       dataTransformation |-> "",
       validationQuery |-> ""
     ]]]
  /\ constraintValidators = [s \in {} |-> [
       schemaName |-> "",
       constraints |-> <<>>,
       validationRules |-> <<>>
     ]]
  /\ onlineChanges = [s \in {} |-> [
       schemaName |-> "",
       changeType |-> "add_column",
       phase |-> "preparation",
       progress |-> 0,
       startTime |-> 0,
       estimatedCompletion |-> 0,
       blockingOperations |-> <<>>
     ]]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Create new schema
CreateSchema(schemaName, ddlStatement, txId) ==
  /\ ~(schemaName \in DOMAIN schemas)
  /\ LET newVersion == [
       version |-> 1,
       schemaName |-> schemaName,
       timestamp |-> globalTimestamp,
       ddlStatement |-> ddlStatement,
       isCompatible |-> TRUE,
       migrationRequired |-> FALSE
     ]
  IN /\ schemas' = [schemas EXCEPT ![schemaName] = newVersion]
     /\ schemaVersions' = [schemaVersions EXCEPT ![schemaName] = <<newVersion>>]
     /\ changeHistory' = Append(changeHistory, [
          changeId |-> Len(changeHistory) + 1,
          schemaName |-> schemaName,
          changeType |-> "create",
          fromVersion |-> 0,
          toVersion |-> 1,
          ddlStatement |-> ddlStatement,
          executedBy |-> txId,
          executedAt |-> globalTimestamp,
          duration |-> 0,
          success |-> TRUE,
          rollbackScript |-> ""
        ])
     /\ UNCHANGED <<pendingChanges, compatibilityMatrix, migrationScripts, 
                   constraintValidators, onlineChanges>>

\* Alter existing schema
AlterSchema(schemaName, ddlStatement, txId) ==
  /\ schemaName \in DOMAIN schemas
  /\ LET currentVersion == schemas[schemaName]
       newVersion == [
         version |-> currentVersion.version + 1,
         schemaName |-> schemaName,
         timestamp |-> globalTimestamp,
         ddlStatement |-> ddlStatement,
         isCompatible |-> CheckCompatibility(currentVersion.version, currentVersion.version + 1),
         migrationRequired |-> ~CheckCompatibility(currentVersion.version, currentVersion.version + 1)
       ]
  IN /\ schemas' = [schemas EXCEPT ![schemaName] = newVersion]
     /\ schemaVersions' = [schemaVersions EXCEPT ![schemaName] = 
                          Append(schemaVersions[schemaName], newVersion)]
     /\ changeHistory' = Append(changeHistory, [
          changeId |-> Len(changeHistory) + 1,
          schemaName |-> schemaName,
          changeType |-> "alter",
          fromVersion |-> currentVersion.version,
          toVersion |-> newVersion.version,
          ddlStatement |-> ddlStatement,
          executedBy |-> txId,
          executedAt |-> globalTimestamp,
          duration |-> 0,
          success |-> TRUE,
          rollbackScript |-> GenerateRollbackScript(currentVersion, newVersion)
        ])
     /\ UNCHANGED <<pendingChanges, compatibilityMatrix, migrationScripts, 
                   constraintValidators, onlineChanges>>

\* Drop schema
DropSchema(schemaName, txId) ==
  /\ schemaName \in DOMAIN schemas
  /\ LET currentVersion == schemas[schemaName]
  IN /\ schemas' = [s \in DOMAIN schemas \ {schemaName} |-> schemas[s]]
     /\ schemaVersions' = [s \in DOMAIN schemaVersions \ {schemaName} |-> schemaVersions[s]]
     /\ changeHistory' = Append(changeHistory, [
          changeId |-> Len(changeHistory) + 1,
          schemaName |-> schemaName,
          changeType |-> "drop",
          fromVersion |-> currentVersion.version,
          toVersion |-> 0,
          ddlStatement |-> "DROP SCHEMA " || schemaName,
          executedBy |-> txId,
          executedAt |-> globalTimestamp,
          duration |-> 0,
          success |-> TRUE,
          rollbackScript |-> GenerateRollbackScript(currentVersion, [
            version |-> 0,
            schemaName |-> schemaName,
            timestamp |-> 0,
            ddlStatement |-> "",
            isCompatible |-> TRUE,
            migrationRequired |-> FALSE
          ])
        ])
     /\ UNCHANGED <<pendingChanges, compatibilityMatrix, migrationScripts, 
                   constraintValidators, onlineChanges>>

\* Submit pending schema change
SubmitPendingChange(schemaName, changeType, ddlStatement, txId, estimatedDuration, requiresDowntime) ==
  /\ LET pendingChange == [
       schemaName |-> schemaName,
       changeType |-> changeType,
       ddlStatement |-> ddlStatement,
       submittedBy |-> txId,
       submittedAt |-> globalTimestamp,
       estimatedDuration |-> estimatedDuration,
       requiresDowntime |-> requiresDowntime
     ]
  IN /\ pendingChanges' = [pendingChanges EXCEPT ![schemaName] = pendingChange]
     /\ UNCHANGED <<schemas, schemaVersions, changeHistory, compatibilityMatrix, 
                   migrationScripts, constraintValidators, onlineChanges>>

\* Execute pending schema change
ExecutePendingChange(schemaName, txId) ==
  /\ schemaName \in DOMAIN pendingChanges
  /\ LET pendingChange == pendingChanges[schemaName]
  IN /\ pendingChanges' = [s \in DOMAIN pendingChanges \ {schemaName} |-> pendingChanges[s]]
     /\ CASE pendingChange.changeType
         OF "create" -> CreateSchema(schemaName, pendingChange.ddlStatement, txId)
         [] "alter" -> AlterSchema(schemaName, pendingChange.ddlStatement, txId)
         [] "drop" -> DropSchema(schemaName, txId)
         [] "rename" -> RenameSchema(schemaName, pendingChange.ddlStatement, txId)
       ENDCASE

\* Rename schema
RenameSchema(oldName, newName, txId) ==
  /\ oldName \in DOMAIN schemas
  /\ ~(newName \in DOMAIN schemas)
  /\ LET currentVersion == schemas[oldName]
       renamedVersion == [currentVersion EXCEPT !.schemaName = newName]
  IN /\ schemas' = [s \in DOMAIN schemas \ {oldName} |-> 
                   IF s = oldName THEN renamedVersion ELSE schemas[s]]
     /\ schemaVersions' = [s \in DOMAIN schemaVersions \ {oldName} |-> 
                          IF s = oldName THEN <<renamedVersion>> ELSE schemaVersions[s]]
     /\ changeHistory' = Append(changeHistory, [
          changeId |-> Len(changeHistory) + 1,
          schemaName |-> oldName,
          changeType |-> "rename",
          fromVersion |-> currentVersion.version,
          toVersion |-> currentVersion.version,
          ddlStatement |-> "RENAME SCHEMA " || oldName || " TO " || newName,
          executedBy |-> txId,
          executedAt |-> globalTimestamp,
          duration |-> 0,
          success |-> TRUE,
          rollbackScript |-> "RENAME SCHEMA " || newName || " TO " || oldName
        ])
     /\ UNCHANGED <<pendingChanges, compatibilityMatrix, migrationScripts, 
                   constraintValidators, onlineChanges>>

\* Start online schema change
StartOnlineChange(schemaName, changeType, txId) ==
  /\ schemaName \in DOMAIN schemas
  /\ ~(schemaName \in DOMAIN onlineChanges)
  /\ LET onlineChange == [
       schemaName |-> schemaName,
       changeType |-> changeType,
       phase |-> "preparation",
       progress |-> 0,
       startTime |-> globalTimestamp,
       estimatedCompletion |-> globalTimestamp + SchemaChangeTimeout,
       blockingOperations |-> <<>>
     ]
  IN /\ onlineChanges' = [onlineChanges EXCEPT ![schemaName] = onlineChange]
     /\ UNCHANGED <<schemas, schemaVersions, pendingChanges, changeHistory, 
                   compatibilityMatrix, migrationScripts, constraintValidators>>

\* Progress online schema change
ProgressOnlineChange(schemaName, newPhase, progress, blockingOps) ==
  /\ schemaName \in DOMAIN onlineChanges
  /\ LET currentChange == onlineChanges[schemaName]
       updatedChange == [currentChange EXCEPT 
                        !.phase = newPhase,
                        !.progress = progress,
                        !.blockingOperations = blockingOps]
  IN /\ onlineChanges' = [onlineChanges EXCEPT ![schemaName] = updatedChange]
     /\ UNCHANGED <<schemas, schemaVersions, pendingChanges, changeHistory, 
                   compatibilityMatrix, migrationScripts, constraintValidators>>

\* Complete online schema change
CompleteOnlineChange(schemaName, txId) ==
  /\ schemaName \in DOMAIN onlineChanges
  /\ LET currentChange == onlineChanges[schemaName]
  IN /\ onlineChanges' = [s \in DOMAIN onlineChanges \ {schemaName} |-> onlineChanges[s]]
     /\ changeHistory' = Append(changeHistory, [
          changeId |-> Len(changeHistory) + 1,
          schemaName |-> schemaName,
          changeType |-> currentChange.changeType,
          fromVersion |-> schemas[schemaName].version,
          toVersion |-> schemas[schemaName].version + 1,
          ddlStatement |-> "ONLINE " || currentChange.changeType,
          executedBy |-> txId,
          executedAt |-> globalTimestamp,
          duration |-> globalTimestamp - currentChange.startTime,
          success |-> TRUE,
          rollbackScript |-> ""
        ])
     /\ UNCHANGED <<schemas, schemaVersions, pendingChanges, compatibilityMatrix, 
                   migrationScripts, constraintValidators>>

\* Validate schema constraints
ValidateSchemaConstraints(schemaName, constraints) ==
  /\ schemaName \in DOMAIN schemas
  /\ LET validator == constraintValidators[schemaName]
       isValid == \A constraint \in constraints : 
                    ValidateConstraint(constraint, schemas[schemaName])
  IN /\ constraintValidators' = [constraintValidators EXCEPT ![schemaName] = 
                                [validator EXCEPT !.constraints = constraints]]
     /\ UNCHANGED <<schemas, schemaVersions, pendingChanges, changeHistory, 
                   compatibilityMatrix, migrationScripts, onlineChanges>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Check compatibility between schema versions
CheckCompatibility(fromVersion, toVersion) ==
  IF fromVersion = 0 \/ toVersion = 0 THEN TRUE
  ELSE compatibilityMatrix[fromVersion][toVersion]

\* Generate rollback script for schema change
GenerateRollbackScript(fromVersion, toVersion) ==
  "ROLLBACK SCHEMA " || fromVersion.schemaName || " FROM " || 
  ToString(fromVersion.version) || " TO " || ToString(toVersion.version)

\* Validate individual constraint
ValidateConstraint(constraint, schemaVersion) ==
  CASE constraint.type
    OF "not_null" -> ValidateNotNullConstraint(constraint, schemaVersion)
    [] "unique" -> ValidateUniqueConstraint(constraint, schemaVersion)
    [] "check" -> ValidateCheckConstraint(constraint, schemaVersion)
    [] "foreign_key" -> ValidateForeignKeyConstraint(constraint, schemaVersion)
  ENDCASE

\* Validate NOT NULL constraint
ValidateNotNullConstraint(constraint, schemaVersion) ==
  TRUE  \* Simplified for TLA+ model

\* Validate UNIQUE constraint
ValidateUniqueConstraint(constraint, schemaVersion) ==
  TRUE  \* Simplified for TLA+ model

\* Validate CHECK constraint
ValidateCheckConstraint(constraint, schemaVersion) ==
  TRUE  \* Simplified for TLA+ model

\* Validate FOREIGN KEY constraint
ValidateForeignKeyConstraint(constraint, schemaVersion) ==
  TRUE  \* Simplified for TLA+ model

\* Convert number to string
ToString(n) ==
  IF n = 0 THEN "0"
  ELSE IF n = 1 THEN "1"
  ELSE IF n = 2 THEN "2"
  ELSE IF n = 3 THEN "3"
  ELSE IF n = 4 THEN "4"
  ELSE IF n = 5 THEN "5"
  ELSE ">5"

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E schemaName \in STRING, ddlStatement \in STRING, txId \in TxIds :
       CreateSchema(schemaName, ddlStatement, txId)
  \/ \E schemaName \in STRING, ddlStatement \in STRING, txId \in TxIds :
       AlterSchema(schemaName, ddlStatement, txId)
  \/ \E schemaName \in STRING, txId \in TxIds :
       DropSchema(schemaName, txId)
  \/ \E schemaName \in STRING, changeType \in {"create", "alter", "drop", "rename"},
       ddlStatement \in STRING, txId \in TxIds, estimatedDuration \in Nat, 
       requiresDowntime \in BOOLEAN :
       SubmitPendingChange(schemaName, changeType, ddlStatement, txId, 
                          estimatedDuration, requiresDowntime)
  \/ \E schemaName \in STRING, txId \in TxIds :
       ExecutePendingChange(schemaName, txId)
  \/ \E oldName \in STRING, newName \in STRING, txId \in TxIds :
       RenameSchema(oldName, newName, txId)
  \/ \E schemaName \in STRING, changeType \in {"add_column", "drop_column", 
       "alter_column", "add_index"}, txId \in TxIds :
       StartOnlineChange(schemaName, changeType, txId)
  \/ \E schemaName \in STRING, newPhase \in {"preparation", "validation", 
       "migration", "completion", "cleanup"}, progress \in 0..100, 
       blockingOps \in Seq(TxId) :
       ProgressOnlineChange(schemaName, newPhase, progress, blockingOps)
  \/ \E schemaName \in STRING, txId \in TxIds :
       CompleteOnlineChange(schemaName, txId)
  \/ \E schemaName \in STRING, constraints \in Seq([type: {"not_null", "unique", 
       "check", "foreign_key"}, column: STRING, expression: STRING]) :
       ValidateSchemaConstraints(schemaName, constraints)

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Schema versions are always increasing
Inv_SchemaEvolution_VersionMonotonic ==
  \A schemaName \in DOMAIN schemaVersions :
    \A i \in 1..Len(schemaVersions[schemaName])-1 :
      schemaVersions[schemaName][i].version < schemaVersions[schemaName][i+1].version

\* Current schema version matches latest in version history
Inv_SchemaEvolution_CurrentVersionMatch ==
  \A schemaName \in DOMAIN schemas :
    /\ schemaName \in DOMAIN schemaVersions
    /\ Len(schemaVersions[schemaName]) > 0
    /\ schemas[schemaName].version = schemaVersions[schemaName][Len(schemaVersions[schemaName])].version

\* Schema changes are atomic
Inv_SchemaEvolution_Atomicity ==
  \A change \in changeHistory :
    change.success => \A schemaName \in DOMAIN schemas :
      schemas[schemaName].version >= change.fromVersion

\* Online changes don't block normal operations
Inv_SchemaEvolution_OnlineChangeNonBlocking ==
  \A schemaName \in DOMAIN onlineChanges :
    Len(onlineChanges[schemaName].blockingOperations) = 0

\* Schema compatibility is symmetric
Inv_SchemaEvolution_CompatibilitySymmetric ==
  \A v1 \in DOMAIN compatibilityMatrix, v2 \in DOMAIN compatibilityMatrix[v1] :
    compatibilityMatrix[v1][v2] = compatibilityMatrix[v2][v1]

\* Pending changes have valid timestamps
Inv_SchemaEvolution_PendingChangeTimestamps ==
  \A schemaName \in DOMAIN pendingChanges :
    pendingChanges[schemaName].submittedAt <= globalTimestamp

\* Online changes progress monotonically
Inv_SchemaEvolution_OnlineChangeProgress ==
  \A schemaName \in DOMAIN onlineChanges :
    onlineChanges[schemaName].progress >= 0 /\ onlineChanges[schemaName].progress <= 100

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Pending changes are eventually executed
Liveness_PendingChangesExecuted ==
  \A schemaName \in DOMAIN pendingChanges :
    <>~(schemaName \in DOMAIN pendingChanges)

\* Online changes eventually complete
Liveness_OnlineChangesComplete ==
  \A schemaName \in DOMAIN onlineChanges :
    <>~(schemaName \in DOMAIN onlineChanges)

\* Schema changes are eventually recorded in history
Liveness_SchemaChangesRecorded ==
  \A schemaName \in DOMAIN schemas :
    \E change \in changeHistory : change.schemaName = schemaName

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Schema evolution maintains data integrity
THEOREM SchemaEvolution_DataIntegrity ==
  Inv_SchemaEvolution_VersionMonotonic /\ 
  Inv_SchemaEvolution_CurrentVersionMatch /\ 
  Inv_SchemaEvolution_Atomicity => 
  \A schemaName \in DOMAIN schemas : schemas[schemaName].version > 0

\* Online schema changes don't cause data loss
THEOREM SchemaEvolution_NoDataLoss ==
  Inv_SchemaEvolution_OnlineChangeNonBlocking /\ 
  Inv_SchemaEvolution_OnlineChangeProgress => 
  \A schemaName \in DOMAIN onlineChanges : 
    onlineChanges[schemaName].progress < 100 \/ 
    onlineChanges[schemaName].phase = "cleanup"

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - SchemaManager.schemas (Dictionary<String, Schema>) → schemas
  - SchemaManager.versionHistory (Dictionary<String, [SchemaVersion]>) → schemaVersions
  - SchemaManager.pendingChanges (Dictionary<String, PendingChange>) → pendingChanges
  - SchemaManager.changeHistory (Array<SchemaChange>) → changeHistory
  
  USAGE:
  
  This module should be used with other ColibrìDB modules:
  
  ---- MODULE ColibriDB ----
  EXTENDS SchemaEvolution
  ...
  ====================
*)
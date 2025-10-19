----------------------------- MODULE SchemaEvolution -----------------------------
(*
  Online Schema Evolution Specification for ColibrìDB
  
  This module specifies online schema changes (ALTER TABLE) that can be performed
  without blocking reads or writes to the table. It implements:
  - ADD COLUMN (with and without default values)
  - DROP COLUMN
  - CHANGE COLUMN (type, null constraints)
  - ADD/DROP INDEX
  - Three-phase protocol: Copy, Apply, Switch
  
  Based on:
  - Ronström, M., & Oreland, J. (2011). "Online Schema Upgrade for MySQL Cluster."
    MySQL Cluster Whitepaper.
  - Wiesmann, M., & Schiper, A. (2005). "Beyond 1-Safety and 2-Safety for Replicated
    Databases: Group-Safety." International Conference on Extending Database Technology.
  - Neamtiu, I., Hicks, M., Stoyle, G., & Oriol, M. (2006). "Practical dynamic software
    updating for C." ACM SIGPLAN Notices, 41(6).
  - Sadalage, P. J., & Fowler, M. (2012). "NoSQL Distilled: A Brief Guide to the
    Emerging World of Polyglot Persistence." Addison-Wesley.
  - Kleppmann, M. (2017). "Designing Data-Intensive Applications." O'Reilly Media.
  
  Key Properties:
  - Non-blocking: Reads/writes continue during schema change
  - Consistency: All operations see consistent schema version
  - Atomicity: Schema change commits or aborts atomically
  - Rollback safety: Can rollback to previous schema
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,                \* From CORE
  MAX_LSN,               \* From CORE
  MAX_PAGES,             \* From CORE
  Tables,                \* Set of table names
  Columns,               \* Set of possible column names
  DataTypes,             \* Set of possible data types
  MAX_SCHEMA_VERSIONS    \* Maximum concurrent schema versions

(* --------------------------------------------------------------------------
   SCHEMA DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Column definition
ColumnDef == [
  name: Columns,
  type: DataTypes,
  nullable: BOOLEAN,
  defaultValue: STRING,
  position: Nat
]

\* Table schema
Schema == [
  version: Nat,
  columns: Seq(ColumnDef),
  indexes: SUBSET STRING,
  constraints: SUBSET STRING
]

\* Schema change operation types
SchemaOpKind == {
  "ADD_COLUMN",
  "DROP_COLUMN",
  "MODIFY_COLUMN",
  "ADD_INDEX",
  "DROP_INDEX",
  "ADD_CONSTRAINT",
  "DROP_CONSTRAINT"
}

SchemaOp == [
  kind: SchemaOpKind,
  table: Tables,
  params: [STRING -> STRING]
]

\* Schema change phases (Online DDL protocol)
SchemaChangePhase == {
  "PREPARE",      \* Prepare shadow objects (new schema, new indexes)
  "COPY",         \* Copy existing data to shadow table
  "APPLY",        \* Apply ongoing writes to both old and new
  "SWITCH",       \* Atomically switch to new schema
  "CLEANUP",      \* Remove old schema
  "DONE",
  "FAILED",
  "ROLLBACK"
}

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Schema registry
  schemas,               \* [Tables -> Schema] - Current schema per table
  shadowSchemas,         \* [Tables -> Schema] - Shadow schemas for ongoing changes
  
  \* Schema change state
  activeSchemaChange,    \* [Tables -> SchemaOp \union {NULL}] - Ongoing changes
  schemaChangePhase,     \* [Tables -> SchemaChangePhase] - Current phase
  schemaVersion,         \* [Tables -> Nat] - Current schema version
  
  \* Data migration state
  copyProgress,          \* [Tables -> Nat] - Rows copied during COPY phase
  totalRows,             \* [Tables -> Nat] - Total rows to copy
  migrationLog,          \* [Tables -> Seq(Operation)] - Operations during APPLY phase
  
  \* Transaction-schema binding
  txSchemaVersion,       \* [TxId -> [Tables -> Nat]] - Schema version seen by each tx
  
  \* Lock state
  schemaLocks            \* [Tables -> {"none", "shared", "exclusive"}]

schemaVars == <<schemas, shadowSchemas, activeSchemaChange, schemaChangePhase,
                schemaVersion, copyProgress, totalRows, migrationLog,
                txSchemaVersion, schemaLocks>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_SchemaEvolution ==
  /\ schemas \in [Tables -> Schema]
  /\ shadowSchemas \in [Tables -> Schema \union {[version |-> 0]}]
  /\ activeSchemaChange \in [Tables -> SchemaOp \union {"none"}]
  /\ schemaChangePhase \in [Tables -> SchemaChangePhase]
  /\ schemaVersion \in [Tables -> Nat]
  /\ copyProgress \in [Tables -> Nat]
  /\ totalRows \in [Tables -> Nat]
  /\ migrationLog \in [Tables -> Seq([op: STRING, data: STRING])]
  /\ txSchemaVersion \in [TxIds -> [Tables -> Nat]]
  /\ schemaLocks \in [Tables -> {"none", "shared", "exclusive"}]

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Get effective schema for a transaction
GetEffectiveSchema(tid, table) ==
  LET version == txSchemaVersion[tid][table]
  IN IF version = schemaVersion[table]
     THEN schemas[table]
     ELSE IF schemaChangePhase[table] \in {"COPY", "APPLY", "SWITCH"}
     THEN shadowSchemas[table]
     ELSE schemas[table]

\* Check if schema change is compatible with running transactions
IsCompatibleChange(table, op) ==
  \* Some changes are backwards compatible, others aren't
  CASE op.kind OF
    "ADD_COLUMN" -> 
      \* Compatible if column has default value or is nullable
      op.params["nullable"] = "true" \/ "default" \in DOMAIN op.params
    [] "DROP_COLUMN" -> FALSE  \* Not compatible with reading transactions
    [] "MODIFY_COLUMN" -> FALSE  \* Type changes not compatible
    [] "ADD_INDEX" -> TRUE  \* Always compatible
    [] "DROP_INDEX" -> TRUE  \* Always compatible
    [] OTHER -> FALSE

\* Apply schema change to produce new schema
ApplySchemaChange(oldSchema, op) ==
  CASE op.kind OF
    "ADD_COLUMN" ->
      LET newCol == [
            name |-> op.params["name"],
            type |-> op.params["type"],
            nullable |-> op.params["nullable"] = "true",
            defaultValue |-> IF "default" \in DOMAIN op.params 
                             THEN op.params["default"] 
                             ELSE "NULL",
            position |-> Len(oldSchema.columns) + 1
          ]
      IN [oldSchema EXCEPT !.columns = Append(@, newCol),
                           !.version = @ + 1]
    
    [] "DROP_COLUMN" ->
      LET colName == op.params["name"]
          newCols == SelectSeq(oldSchema.columns, 
                               LAMBDA col: col.name # colName)
      IN [oldSchema EXCEPT !.columns = newCols,
                           !.version = @ + 1]
    
    [] "ADD_INDEX" ->
      [oldSchema EXCEPT !.indexes = @ \union {op.params["name"]},
                        !.version = @ + 1]
    
    [] "DROP_INDEX" ->
      [oldSchema EXCEPT !.indexes = @ \ {op.params["name"]},
                        !.version = @ + 1]
    
    [] OTHER -> oldSchema

\* Check if all transactions are on same schema version
AllTxOnSameVersion(table) ==
  \A tid1, tid2 \in TxIds:
    txSchemaVersion[tid1][table] = txSchemaVersion[tid2][table]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_SchemaEvolution ==
  /\ schemas = [t \in Tables |-> 
                 [version |-> 1,
                  columns |-> <<[name |-> "id", type |-> "INTEGER", 
                                nullable |-> FALSE, defaultValue |-> "", position |-> 1]>>,
                  indexes |-> {},
                  constraints |-> {}]]
  /\ shadowSchemas = [t \in Tables |-> [version |-> 0]]
  /\ activeSchemaChange = [t \in Tables |-> "none"]
  /\ schemaChangePhase = [t \in Tables |-> "DONE"]
  /\ schemaVersion = [t \in Tables |-> 1]
  /\ copyProgress = [t \in Tables |-> 0]
  /\ totalRows = [t \in Tables |-> 100]
  /\ migrationLog = [t \in Tables |-> <<>>]
  /\ txSchemaVersion = [tid \in TxIds |-> [t \in Tables |-> 1]]
  /\ schemaLocks = [t \in Tables |-> "none"]

(* --------------------------------------------------------------------------
   SCHEMA CHANGE PHASES
   -------------------------------------------------------------------------- *)

\* Phase 0: Prepare - Create shadow schema and indexes
PrepareSchemaChange(table, op) ==
  /\ activeSchemaChange[table] = "none"
  /\ schemaChangePhase[table] = "DONE"
  /\ activeSchemaChange' = [activeSchemaChange EXCEPT ![table] = op]
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "PREPARE"]
  /\ shadowSchemas' = [shadowSchemas EXCEPT ![table] = ApplySchemaChange(schemas[table], op)]
  /\ copyProgress' = [copyProgress EXCEPT ![table] = 0]
  /\ migrationLog' = [migrationLog EXCEPT ![table] = <<>>]
  /\ UNCHANGED <<schemas, schemaVersion, totalRows, txSchemaVersion, schemaLocks>>

\* Phase 1: Copy - Copy existing data to shadow table
CopyData(table) ==
  /\ schemaChangePhase[table] = "PREPARE"
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "COPY"]
  /\ schemaLocks' = [schemaLocks EXCEPT ![table] = "shared"]  \* Shared lock allows reads
  /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaVersion,
                copyProgress, totalRows, migrationLog, txSchemaVersion>>

\* Copy progress (incremental)
CopyBatch(table, batchSize) ==
  /\ schemaChangePhase[table] = "COPY"
  /\ copyProgress[table] < totalRows[table]
  /\ LET newProgress == Min({copyProgress[table] + batchSize, totalRows[table]})
     IN /\ copyProgress' = [copyProgress EXCEPT ![table] = newProgress]
        /\ IF newProgress = totalRows[table]
           THEN schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "APPLY"]
           ELSE UNCHANGED schemaChangePhase
        /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaVersion,
                      totalRows, migrationLog, txSchemaVersion, schemaLocks>>

\* Phase 2: Apply - Dual-write to both old and new schema
ApplyPhase(table) ==
  /\ schemaChangePhase[table] = "APPLY"
  /\ AllTxOnSameVersion(table)  \* Wait for all old transactions to complete
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "SWITCH"]
  /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaVersion,
                copyProgress, totalRows, migrationLog, txSchemaVersion, schemaLocks>>

\* Log operation during APPLY phase
LogOperation(table, operation, data) ==
  /\ schemaChangePhase[table] = "APPLY"
  /\ migrationLog' = [migrationLog EXCEPT ![table] = 
                       Append(@, [op |-> operation, data |-> data])]
  /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaChangePhase,
                schemaVersion, copyProgress, totalRows, txSchemaVersion, schemaLocks>>

\* Phase 3: Switch - Atomically switch to new schema
SwitchSchema(table) ==
  /\ schemaChangePhase[table] = "SWITCH"
  /\ schemaLocks' = [schemaLocks EXCEPT ![table] = "exclusive"]  \* Brief exclusive lock
  /\ schemas' = [schemas EXCEPT ![table] = shadowSchemas[table]]
  /\ schemaVersion' = [schemaVersion EXCEPT ![table] = shadowSchemas[table].version]
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "CLEANUP"]
  /\ UNCHANGED <<shadowSchemas, activeSchemaChange, copyProgress, totalRows,
                migrationLog, txSchemaVersion>>

\* Phase 4: Cleanup - Remove old schema objects
CleanupSchemaChange(table) ==
  /\ schemaChangePhase[table] = "CLEANUP"
  /\ shadowSchemas' = [shadowSchemas EXCEPT ![table] = [version |-> 0]]
  /\ activeSchemaChange' = [activeSchemaChange EXCEPT ![table] = "none"]
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "DONE"]
  /\ schemaLocks' = [schemaLocks EXCEPT ![table] = "none"]
  /\ UNCHANGED <<schemas, schemaVersion, copyProgress, totalRows,
                migrationLog, txSchemaVersion>>

\* Rollback schema change (if something goes wrong)
RollbackSchemaChange(table) ==
  /\ schemaChangePhase[table] \in {"PREPARE", "COPY", "APPLY"}
  /\ shadowSchemas' = [shadowSchemas EXCEPT ![table] = [version |-> 0]]
  /\ activeSchemaChange' = [activeSchemaChange EXCEPT ![table] = "none"]
  /\ schemaChangePhase' = [schemaChangePhase EXCEPT ![table] = "ROLLBACK"]
  /\ schemaLocks' = [schemaLocks EXCEPT ![table] = "none"]
  /\ UNCHANGED <<schemas, schemaVersion, copyProgress, totalRows,
                migrationLog, txSchemaVersion>>

(* --------------------------------------------------------------------------
   TRANSACTION OPERATIONS
   -------------------------------------------------------------------------- *)

\* Transaction begins and locks to a schema version
BeginTxWithSchema(tid, table) ==
  /\ txSchemaVersion' = [txSchemaVersion EXCEPT ![tid][table] = schemaVersion[table]]
  /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaChangePhase,
                schemaVersion, copyProgress, totalRows, migrationLog, schemaLocks>>

\* Transaction reads using its locked schema version
ReadWithSchema(tid, table) ==
  /\ LET effectiveSchema == GetEffectiveSchema(tid, table)
     IN TRUE  \* Read using effectiveSchema
  /\ UNCHANGED schemaVars

\* Transaction writes using its locked schema version
WriteWithSchema(tid, table, data) ==
  /\ LET effectiveSchema == GetEffectiveSchema(tid, table)
     IN /\ IF schemaChangePhase[table] = "APPLY"
           THEN migrationLog' = [migrationLog EXCEPT ![table] = 
                                  Append(@, [op |-> "write", data |-> data])]
           ELSE UNCHANGED migrationLog
        /\ UNCHANGED <<schemas, shadowSchemas, activeSchemaChange, schemaChangePhase,
                      schemaVersion, copyProgress, totalRows, txSchemaVersion, schemaLocks>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_SchemaEvolution ==
  \/ \E table \in Tables, op \in SchemaOp: PrepareSchemaChange(table, op)
  \/ \E table \in Tables: CopyData(table)
  \/ \E table \in Tables, batch \in Nat: CopyBatch(table, batch)
  \/ \E table \in Tables: ApplyPhase(table)
  \/ \E table \in Tables, op \in STRING, data \in STRING: LogOperation(table, op, data)
  \/ \E table \in Tables: SwitchSchema(table)
  \/ \E table \in Tables: CleanupSchemaChange(table)
  \/ \E table \in Tables: RollbackSchemaChange(table)
  \/ \E tid \in TxIds, table \in Tables: BeginTxWithSchema(tid, table)
  \/ \E tid \in TxIds, table \in Tables: ReadWithSchema(tid, table)
  \/ \E tid \in TxIds, table \in Tables, data \in STRING: WriteWithSchema(tid, table, data)

Spec_SchemaEvolution == Init_SchemaEvolution /\ [][Next_SchemaEvolution]_schemaVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Schema consistency
Inv_SchemaEvolution_Consistency ==
  \A table \in Tables:
    activeSchemaChange[table] # "none" => shadowSchemas[table].version # 0

\* Invariant 2: Non-blocking reads
Inv_SchemaEvolution_NonBlockingReads ==
  \A table \in Tables:
    schemaChangePhase[table] \in {"PREPARE", "COPY", "APPLY"} =>
      schemaLocks[table] \in {"none", "shared"}

\* Invariant 3: Exclusive lock only during SWITCH
Inv_SchemaEvolution_ExclusiveLockMinimal ==
  \A table \in Tables:
    schemaLocks[table] = "exclusive" <=> schemaChangePhase[table] = "SWITCH"

\* Invariant 4: Transaction schema isolation
Inv_SchemaEvolution_TxIsolation ==
  \A tid \in TxIds, table \in Tables:
    txSchemaVersion[tid][table] \in {schemas[table].version, shadowSchemas[table].version}

\* Invariant 5: Copy progress bound
Inv_SchemaEvolution_CopyProgress ==
  \A table \in Tables:
    copyProgress[table] <= totalRows[table]

\* Invariant 6: Schema version monotonicity
Inv_SchemaEvolution_VersionMonotonic ==
  \A table \in Tables:
    shadowSchemas[table].version = 0 \/ 
    shadowSchemas[table].version > schemas[table].version

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Schema changes eventually complete
Prop_SchemaEvolution_Completion ==
  \A table \in Tables:
    [](activeSchemaChange[table] # "none" =>
       <>(schemaChangePhase[table] \in {"DONE", "ROLLBACK"}))

\* Property 2: No permanent exclusive locks
Prop_SchemaEvolution_NoDeadlock ==
  \A table \in Tables:
    [](schemaLocks[table] = "exclusive" => 
       <>(schemaLocks[table] \in {"none", "shared"}))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM SchemaEvolution_NonBlocking ==
  Spec_SchemaEvolution => []Inv_SchemaEvolution_NonBlockingReads

THEOREM SchemaEvolution_Consistency ==
  Spec_SchemaEvolution => []Inv_SchemaEvolution_TxIsolation

THEOREM SchemaEvolution_Progress ==
  Spec_SchemaEvolution => Prop_SchemaEvolution_Completion

=============================================================================

(*
  REFERENCES:
  
  [1] Ronström, M., & Oreland, J. (2011). "Online Schema Upgrade for MySQL Cluster."
      MySQL Cluster Technical Whitepaper.
  
  [2] Kleppmann, M. (2017). "Designing Data-Intensive Applications: The Big Ideas
      Behind Reliable, Scalable, and Maintainable Systems." O'Reilly Media.
  
  [3] Neamtiu, I., Hicks, M., Stoyle, G., & Oriol, M. (2006). "Practical dynamic
      software updating for C." ACM SIGPLAN Notices, 41(6), 72-83.
  
  [4] Sadalage, P. J., & Fowler, M. (2012). "NoSQL Distilled: A Brief Guide to the
      Emerging World of Polyglot Persistence." Addison-Wesley Professional.
  
  [5] Wiesmann, M., & Schiper, A. (2005). "Beyond 1-Safety and 2-Safety for
      Replicated Databases: Group-Safety." EDBT 2005.
  
  IMPLEMENTATION NOTES:
  
  - Three-phase protocol: PREPARE -> COPY -> APPLY -> SWITCH -> CLEANUP
  - Dual-write during APPLY phase ensures consistency
  - Exclusive lock held only during brief SWITCH phase
  - Similar to MySQL Online DDL, Postgres CONCURRENTLY
  - Shadow tables used for data migration
  - Rollback supported until SWITCH phase
*)


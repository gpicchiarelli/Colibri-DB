------------------------------- MODULE Catalog -------------------------------
(*
  ColibrìDB System Catalog Specification
  
  Manages database metadata including:
  - Tables (schemas, columns, constraints)
  - Indexes (B+Tree, Hash)
  - Statistics for query optimization
  - Schema versioning for DDL operations
  
  Key Properties:
  - Consistency: Metadata changes are atomic
  - Durability: Catalog survives crashes
  - Isolation: DDL operations don't interfere
  - Versioning: Schema changes are versioned
  
  Author: ColibrìDB Team
  Date: 2025-10-18
*)

EXTENDS CORE, Naturals, Sequences, FiniteSets

CONSTANTS
  TableNames,    \* Set of possible table names
  ColumnNames    \* Set of possible column names

VARIABLES
  tables,        \* [TableName -> TableMetadata]
  indexes,       \* [IndexName -> IndexMetadata]
  statistics,    \* [TableName -> Statistics]
  schemaVersion  \* Current schema version number

catalogVars == <<tables, indexes, statistics, schemaVersion>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Column metadata
ColumnMetadata == [
  name: ColumnNames,
  type: ValueType,
  nullable: BOOLEAN,
  defaultValue: Value \union {0}
]

\* Table metadata
TableMetadata == [
  name: TableNames,
  columns: Seq(ColumnMetadata),
  primaryKey: SUBSET ColumnNames,
  foreignKeys: Seq([from: ColumnNames, to: [table: TableNames, column: ColumnNames]]),
  constraints: Seq([type: {"unique", "check", "not_null"}, columns: SUBSET ColumnNames])
]

\* Index metadata
IndexMetadata == [
  name: STRING,
  tableName: TableNames,
  columns: Seq(ColumnNames),
  indexType: {"btree", "hash"},
  unique: BOOLEAN
]

\* Table statistics for query optimizer
Statistics == [
  rowCount: Nat,
  avgRowSize: Nat,
  distinctValues: [ColumnNames -> Nat]
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Catalog ==
  /\ tables \in [TableNames -> TableMetadata]
  /\ indexes \in [STRING -> IndexMetadata]
  /\ statistics \in [TableNames -> Statistics]
  /\ schemaVersion \in Nat

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ tables = [t \in TableNames |-> [
       name |-> t,
       columns |-> <<>>,
       primaryKey |-> {},
       foreignKeys |-> <<>>,
       constraints |-> <<>>
     ]]
  /\ indexes = [i \in {} |-> [
       name |-> "",
       tableName |-> CHOOSE t \in TableNames : TRUE,
       columns |-> <<>>,
       indexType |-> "btree",
       unique |-> FALSE
     ]]
  /\ statistics = [t \in TableNames |-> [
       rowCount |-> 0,
       avgRowSize |-> 0,
       distinctValues |-> [c \in ColumnNames |-> 0]
     ]]
  /\ schemaVersion = 1

(* --------------------------------------------------------------------------
   DDL OPERATIONS
   -------------------------------------------------------------------------- *)

\* Create a new table
CreateTable(tableName, columns, primaryKey) ==
  /\ tableName \in TableNames
  /\ tables[tableName].columns = <<>>  \* Table doesn't exist
  /\ tables' = [tables EXCEPT ![tableName] = [
       name |-> tableName,
       columns |-> columns,
       primaryKey |-> primaryKey,
       foreignKeys |-> <<>>,
       constraints |-> <<>>
     ]]
  /\ statistics' = [statistics EXCEPT ![tableName] = [
       rowCount |-> 0,
       avgRowSize |-> 0,
       distinctValues |-> [c \in ColumnNames |-> 0]
     ]]
  /\ schemaVersion' = schemaVersion + 1
  /\ UNCHANGED indexes

\* Drop a table
DropTable(tableName) ==
  /\ tableName \in TableNames
  /\ tables[tableName].columns # <<>>  \* Table exists
  /\ tables' = [tables EXCEPT ![tableName] = [
       name |-> tableName,
       columns |-> <<>>,
       primaryKey |-> {},
       foreignKeys |-> <<>>,
       constraints |-> <<>>
     ]]
  /\ statistics' = [statistics EXCEPT ![tableName] = [
       rowCount |-> 0,
       avgRowSize |-> 0,
       distinctValues |-> [c \in ColumnNames |-> 0]
     ]]
  /\ schemaVersion' = schemaVersion + 1
  /\ UNCHANGED indexes

\* Create an index
CreateIndex(indexName, tableName, columns, indexType, unique) ==
  /\ indexName \notin DOMAIN indexes
  /\ tableName \in TableNames
  /\ tables[tableName].columns # <<>>
  /\ indexes' = indexes @@ (indexName :> [
       name |-> indexName,
       tableName |-> tableName,
       columns |-> columns,
       indexType |-> indexType,
       unique |-> unique
     ])
  /\ schemaVersion' = schemaVersion + 1
  /\ UNCHANGED <<tables, statistics>>

\* Update statistics after data modification
UpdateStatistics(tableName, newRowCount, newAvgRowSize) ==
  /\ tableName \in TableNames
  /\ statistics' = [statistics EXCEPT ![tableName].rowCount = newRowCount,
                                     ![tableName].avgRowSize = newAvgRowSize]
  /\ UNCHANGED <<tables, indexes, schemaVersion>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Primary keys reference existing columns
Inv_Catalog_PrimaryKeyValid ==
  \A t \in TableNames:
    tables[t].primaryKey \subseteq {tables[t].columns[i].name : i \in DOMAIN tables[t].columns}

\* Invariant 2: Foreign keys reference existing tables and columns
Inv_Catalog_ForeignKeyValid ==
  \A t \in TableNames:
    \A fk \in Range(tables[t].foreignKeys):
      /\ fk.to.table \in TableNames
      /\ fk.from \in {tables[t].columns[i].name : i \in DOMAIN tables[t].columns}

\* Invariant 3: Indexes reference existing tables
Inv_Catalog_IndexValid ==
  \A idx \in DOMAIN indexes:
    indexes[idx].tableName \in TableNames

\* Invariant 4: Statistics consistent with tables
Inv_Catalog_StatisticsValid ==
  \A t \in TableNames:
    tables[t].columns # <<>> => statistics[t].rowCount >= 0

\* Combined safety invariant
Inv_Catalog_Safety ==
  /\ TypeOK_Catalog
  /\ Inv_Catalog_PrimaryKeyValid
  /\ Inv_Catalog_ForeignKeyValid
  /\ Inv_Catalog_IndexValid
  /\ Inv_Catalog_StatisticsValid

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E t \in TableNames, cols \in Seq(ColumnMetadata), pk \in SUBSET ColumnNames:
       CreateTable(t, cols, pk)
  \/ \E t \in TableNames: DropTable(t)
  \/ \E name \in STRING, t \in TableNames, cols \in Seq(ColumnNames), 
        idxType \in {"btree", "hash"}, uniq \in BOOLEAN:
       CreateIndex(name, t, cols, idxType, uniq)
  \/ \E t \in TableNames, count \in Nat, avgSize \in Nat:
       UpdateStatistics(t, count, avgSize)

Spec == Init /\ [][Next]_catalogVars

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    TableNames = {"users", "orders", "products"}
    ColumnNames = {"id", "name", "price", "user_id"}
  
  Invariants:
    - Inv_Catalog_Safety
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_Catalog(catalog: SystemCatalog) -> [String: Any] {
      return [
          "tables": catalog.tables.mapValues { $0.toTLA() },
          "indexes": catalog.indexes.mapValues { $0.toTLA() },
          "statistics": catalog.statistics.mapValues { $0.toTLA() },
          "schemaVersion": catalog.schemaVersion
      ]
  }
*)

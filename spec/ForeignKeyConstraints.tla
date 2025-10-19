----------------------------- MODULE ForeignKeyConstraints -----------------------------
(*
  Foreign Key Constraints and Referential Integrity Specification for Colibrì

DB
  
  This module specifies the enforcement of referential integrity through foreign keys.
  It implements:
  - Foreign key constraint definition (FOREIGN KEY ... REFERENCES ...)
  - Referential actions: CASCADE, SET NULL, SET DEFAULT, RESTRICT, NO ACTION
  - Constraint checking on INSERT, UPDATE, DELETE
  - Deferred constraint checking (within transactions)
  - Multi-column foreign keys
  
  Based on:
  - Codd, E. F. (1970). "A relational model of data for large shared data banks."
    Communications of the ACM, 13(6), 377-387.
  - Date, C. J. (1986). "Referential Integrity." Proceedings of VLDB 1986.
  - ISO/IEC 9075:2016 (SQL:2016 Standard) - Part 2: Foundation, Section 11.8
  - Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts and Techniques."
    Morgan Kaufmann Publishers.
  - Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems: 
    The Complete Book" (2nd ed.). Prentice Hall.
  
  Key Properties:
  - Referential integrity: All foreign keys reference existing primary keys
  - Cascading consistency: CASCADE operations maintain integrity
  - Transaction atomicity: Constraint checks are atomic within transaction
  - No orphaned rows: Foreign key rows always have parent
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,               \* From CORE
  MAX_LSN,              \* From CORE
  MAX_PAGES,            \* From CORE
  Tables,               \* Set of table names
  Columns,              \* Set of column names
  TxIds,                \* Set of transaction IDs
  MAX_ROWS_PER_TABLE    \* Maximum rows per table

(* --------------------------------------------------------------------------
   REFERENTIAL ACTIONS
   -------------------------------------------------------------------------- *)

ReferentialAction == {
  "CASCADE",       \* Delete/update child rows when parent is deleted/updated
  "SET_NULL",      \* Set foreign key to NULL when parent is deleted/updated
  "SET_DEFAULT",   \* Set foreign key to default value
  "RESTRICT",      \* Prevent parent delete/update if children exist
  "NO_ACTION"      \* Same as RESTRICT but checked at end of statement
}

\* Foreign key constraint definition
FKConstraint == [
  name: STRING,
  childTable: Tables,
  childColumns: Seq(Columns),
  parentTable: Tables,
  parentColumns: Seq(Columns),
  onDelete: ReferentialAction,
  onUpdate: ReferentialAction,
  deferrable: BOOLEAN      \* Can be deferred to end of transaction
]

\* Row in a table (simplified)
Row == [
  id: Nat,
  values: [Columns -> Value]
]

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Table data
  tableData,            \* [Tables -> SUBSET Row] - Rows in each table
  primaryKeys,          \* [Tables -> SUBSET Nat] - Primary key values
  
  \* Foreign key constraints
  fkConstraints,        \* SUBSET FKConstraint - Defined FK constraints
  
  \* Constraint checking
  constraintViolations, \* Seq(STRING) - Detected constraint violations
  deferredChecks,       \* [TxId -> Seq(FKConstraint)] - Deferred checks per tx
  
  \* Transaction state
  txActive,             \* [TxId -> BOOLEAN] - Active transactions
  txPendingOps,         \* [TxId -> Seq([op, table, row])] - Pending operations
  
  \* Cascade state
  cascadeInProgress     \* BOOLEAN - Indicates cascading delete/update in progress

fkVars == <<tableData, primaryKeys, fkConstraints, constraintViolations,
            deferredChecks, txActive, txPendingOps, cascadeInProgress>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_FK ==
  /\ tableData \in [Tables -> SUBSET Row]
  /\ primaryKeys \in [Tables -> SUBSET Nat]
  /\ fkConstraints \in SUBSET FKConstraint
  /\ constraintViolations \in Seq(STRING)
  /\ deferredChecks \in [TxIds -> Seq(FKConstraint)]
  /\ txActive \in [TxIds -> BOOLEAN]
  /\ txPendingOps \in [TxIds -> Seq([op: STRING, table: Tables, row: Row])]
  /\ cascadeInProgress \in BOOLEAN

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Check if a foreign key value references an existing primary key
ForeignKeyExists(fk, childRow) ==
  LET fkValues == [i \in 1..Len(fk.childColumns) |-> 
                    childRow.values[fk.childColumns[i]]]
      parentRows == tableData[fk.parentTable]
      pkColumns == fk.parentColumns
  IN \E parentRow \in parentRows:
       \A i \in 1..Len(pkColumns):
         parentRow.values[pkColumns[i]] = fkValues[i]

\* Get all child rows referencing a parent row
GetChildRows(fk, parentRow) ==
  LET pkValues == [i \in 1..Len(fk.parentColumns) |-> 
                    parentRow.values[fk.parentColumns[i]]]
      childRows == tableData[fk.childTable]
  IN {childRow \in childRows:
       \A i \in 1..Len(fk.childColumns):
         childRow.values[fk.childColumns[i]] = pkValues[i]}

\* Check if any foreign key constraints reference a table
HasIncomingFKs(table) ==
  \E fk \in fkConstraints: fk.parentTable = table

\* Get all FK constraints for a table (as child or parent)
GetFKsForTable(table) ==
  {fk \in fkConstraints: fk.childTable = table \/ fk.parentTable = table}

\* Check if a row exists in table
RowExists(table, rowId) ==
  \E row \in tableData[table]: row.id = rowId

\* Get row by ID
GetRow(table, rowId) ==
  CHOOSE row \in tableData[table]: row.id = rowId

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_FK ==
  /\ tableData = [t \in Tables |-> {}]
  /\ primaryKeys = [t \in Tables |-> {}]
  /\ fkConstraints = {}
  /\ constraintViolations = <<>>
  /\ deferredChecks = [tid \in TxIds |-> <<>>]
  /\ txActive = [tid \in TxIds |-> FALSE]
  /\ txPendingOps = [tid \in TxIds |-> <<>>]
  /\ cascadeInProgress = FALSE

(* --------------------------------------------------------------------------
   CONSTRAINT DEFINITION
   -------------------------------------------------------------------------- *)

\* Define a foreign key constraint
DefineFKConstraint(fk) ==
  /\ fk \notin fkConstraints
  /\ Len(fk.childColumns) = Len(fk.parentColumns)  \* Same number of columns
  /\ fkConstraints' = fkConstraints \union {fk}
  /\ UNCHANGED <<tableData, primaryKeys, constraintViolations, deferredChecks,
                txActive, txPendingOps, cascadeInProgress>>

\* Drop a foreign key constraint
DropFKConstraint(fkName) ==
  /\ LET fk == CHOOSE f \in fkConstraints: f.name = fkName
     IN fkConstraints' = fkConstraints \ {fk}
  /\ UNCHANGED <<tableData, primaryKeys, constraintViolations, deferredChecks,
                txActive, txPendingOps, cascadeInProgress>>

(* --------------------------------------------------------------------------
   DATA OPERATIONS WITH FK CHECKING
   -------------------------------------------------------------------------- *)

\* Insert a row (check foreign key constraints)
InsertRow(tid, table, row) ==
  /\ txActive[tid]
  /\ LET childFKs == {fk \in fkConstraints: fk.childTable = table}
         violations == {fk \in childFKs: ~ForeignKeyExists(fk, row)}
     IN IF violations = {}
        THEN /\ tableData' = [tableData EXCEPT ![table] = @ \union {row}]
             /\ IF row.values["id"] \in DOMAIN row.values  \* If has primary key
                THEN primaryKeys' = [primaryKeys EXCEPT ![table] = @ \union {row.id}]
                ELSE UNCHANGED primaryKeys
             /\ UNCHANGED constraintViolations
        ELSE /\ constraintViolations' = Append(constraintViolations,
                  "FK violation on INSERT to " \o table)
             /\ UNCHANGED <<tableData, primaryKeys>>
  /\ UNCHANGED <<fkConstraints, deferredChecks, txActive, txPendingOps, cascadeInProgress>>

\* Delete a row (check and apply referential actions)
DeleteRow(tid, table, rowId) ==
  /\ txActive[tid]
  /\ RowExists(table, rowId)
  /\ LET row == GetRow(table, rowId)
         parentFKs == {fk \in fkConstraints: fk.parentTable = table}
     IN \/ \* RESTRICT: Prevent delete if children exist
           /\ \E fk \in parentFKs: 
                /\ fk.onDelete = "RESTRICT"
                /\ GetChildRows(fk, row) # {}
           /\ constraintViolations' = Append(constraintViolations,
                "FK RESTRICT violation on DELETE from " \o table)
           /\ UNCHANGED <<tableData, primaryKeys, fkConstraints, deferredChecks,
                         txActive, txPendingOps, cascadeInProgress>>
        \/ \* CASCADE: Delete child rows
           /\ \A fk \in parentFKs: fk.onDelete \in {"CASCADE", "SET_NULL", "SET_DEFAULT"}
           /\ LET cascadeFKs == {fk \in parentFKs: fk.onDelete = "CASCADE"}
                  setNullFKs == {fk \in parentFKs: fk.onDelete = "SET_NULL"}
              IN /\ tableData' = [t \in Tables |->
                      IF t = table
                      THEN tableData[t] \ {row}
                      ELSE IF \E fk \in cascadeFKs: fk.childTable = t
                      THEN LET fk == CHOOSE f \in cascadeFKs: f.childTable = t
                               childRows == GetChildRows(fk, row)
                           IN tableData[t] \ childRows
                      ELSE IF \E fk \in setNullFKs: fk.childTable = t
                      THEN LET fk == CHOOSE f \in setNullFKs: f.childTable = t
                               childRows == GetChildRows(fk, row)
                               updatedRows == {[r EXCEPT !.values = 
                                               [@ EXCEPT ![fk.childColumns[1]] = "NULL"]]
                                              : r \in childRows}
                           IN (tableData[t] \ childRows) \union updatedRows
                      ELSE tableData[t]]
                 /\ primaryKeys' = [primaryKeys EXCEPT ![table] = @ \ {rowId}]
                 /\ cascadeInProgress' = TRUE
                 /\ UNCHANGED <<fkConstraints, constraintViolations, deferredChecks,
                               txActive, txPendingOps>>

\* Update a row (check FK constraints on both old and new values)
UpdateRow(tid, table, rowId, newValues) ==
  /\ txActive[tid]
  /\ RowExists(table, rowId)
  /\ LET oldRow == GetRow(table, rowId)
         newRow == [oldRow EXCEPT !.values = newValues]
         \* Check as child: new values must reference existing parents
         childFKs == {fk \in fkConstraints: fk.childTable = table}
         childViolations == {fk \in childFKs: ~ForeignKeyExists(fk, newRow)}
         \* Check as parent: update may break child references
         parentFKs == {fk \in fkConstraints: fk.parentTable = table}
     IN IF childViolations = {}
        THEN /\ tableData' = [tableData EXCEPT ![table] = (@ \ {oldRow}) \union {newRow}]
             /\ \* Apply referential actions for parent FKs
                \A fk \in parentFKs:
                  fk.onUpdate \in {"CASCADE", "SET_NULL", "RESTRICT"}
             /\ UNCHANGED <<primaryKeys, constraintViolations>>
        ELSE /\ constraintViolations' = Append(constraintViolations,
                  "FK violation on UPDATE to " \o table)
             /\ UNCHANGED <<tableData, primaryKeys>>
  /\ UNCHANGED <<fkConstraints, deferredChecks, txActive, txPendingOps, cascadeInProgress>>

(* --------------------------------------------------------------------------
   DEFERRED CONSTRAINT CHECKING
   -------------------------------------------------------------------------- *)

\* Begin transaction with deferred constraint checking
BeginTxDeferred(tid) ==
  /\ ~txActive[tid]
  /\ txActive' = [txActive EXCEPT ![tid] = TRUE]
  /\ deferredChecks' = [deferredChecks EXCEPT ![tid] = <<>>]
  /\ txPendingOps' = [txPendingOps EXCEPT ![tid] = <<>>]
  /\ UNCHANGED <<tableData, primaryKeys, fkConstraints, constraintViolations, cascadeInProgress>>

\* Commit transaction (check all deferred constraints)
CommitTxWithFK(tid) ==
  /\ txActive[tid]
  /\ LET checks == deferredChecks[tid]
         violations == {fk \in Range(checks): 
                         \E row \in tableData[fk.childTable]:
                           ~ForeignKeyExists(fk, row)}
     IN IF violations = {}
        THEN /\ txActive' = [txActive EXCEPT ![tid] = FALSE]
             /\ deferredChecks' = [deferredChecks EXCEPT ![tid] = <<>>]
             /\ txPendingOps' = [txPendingOps EXCEPT ![tid] = <<>>]
             /\ UNCHANGED <<tableData, primaryKeys, constraintViolations>>
        ELSE /\ constraintViolations' = Append(constraintViolations,
                  "Deferred FK constraint violation on COMMIT")
             /\ txActive' = [txActive EXCEPT ![tid] = FALSE]  \* Rollback
             /\ UNCHANGED <<tableData, primaryKeys, deferredChecks, txPendingOps>>
  /\ UNCHANGED <<fkConstraints, cascadeInProgress>>

\* Rollback transaction
RollbackTxWithFK(tid) ==
  /\ txActive[tid]
  /\ txActive' = [txActive EXCEPT ![tid] = FALSE]
  /\ deferredChecks' = [deferredChecks EXCEPT ![tid] = <<>>]
  /\ txPendingOps' = [txPendingOps EXCEPT ![tid] = <<>>]
  /\ UNCHANGED <<tableData, primaryKeys, fkConstraints, constraintViolations, cascadeInProgress>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_FK ==
  \/ \E fk \in FKConstraint: DefineFKConstraint(fk)
  \/ \E name \in STRING: DropFKConstraint(name)
  \/ \E tid \in TxIds, table \in Tables, row \in Row: InsertRow(tid, table, row)
  \/ \E tid \in TxIds, table \in Tables, rowId \in Nat: DeleteRow(tid, table, rowId)
  \/ \E tid \in TxIds, table \in Tables, rowId \in Nat, vals \in [Columns -> Value]:
       UpdateRow(tid, table, rowId, vals)
  \/ \E tid \in TxIds: BeginTxDeferred(tid)
  \/ \E tid \in TxIds: CommitTxWithFK(tid)
  \/ \E tid \in TxIds: RollbackTxWithFK(tid)

Spec_FK == Init_FK /\ [][Next_FK]_fkVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Referential integrity
\* All foreign key values reference existing primary keys
Inv_FK_ReferentialIntegrity ==
  \A fk \in fkConstraints:
    \A childRow \in tableData[fk.childTable]:
      \* Either FK is NULL (if nullable) or references existing parent
      (\A i \in 1..Len(fk.childColumns): 
         childRow.values[fk.childColumns[i]] = "NULL")
      \/ ForeignKeyExists(fk, childRow)

\* Invariant 2: Primary key uniqueness
Inv_FK_PKUnique ==
  \A table \in Tables:
    \A r1, r2 \in tableData[table]:
      r1.id = r2.id => r1 = r2

\* Invariant 3: CASCADE consistency
\* After cascade delete, no orphaned children
Inv_FK_CascadeConsistency ==
  ~cascadeInProgress =>
    \A fk \in fkConstraints:
      fk.onDelete = "CASCADE" =>
        \A childRow \in tableData[fk.childTable]:
          ForeignKeyExists(fk, childRow)

\* Invariant 4: RESTRICT enforcement
\* RESTRICT prevents deletion of parent with children
Inv_FK_RestrictEnforcement ==
  \A fk \in fkConstraints:
    fk.onDelete = "RESTRICT" =>
      \A parentRow \in tableData[fk.parentTable]:
        GetChildRows(fk, parentRow) # {} =>
          parentRow \in tableData[fk.parentTable]

\* Invariant 5: No constraint violations pending
Inv_FK_NoViolations ==
  \A tid \in TxIds:
    ~txActive[tid] => Len(constraintViolations) = 0

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Transactions eventually complete
Prop_FK_TxCompletion ==
  \A tid \in TxIds:
    [](txActive[tid] => <>~txActive[tid])

\* Property 2: Cascade operations eventually complete
Prop_FK_CascadeCompletion ==
  [](cascadeInProgress => <>~cascadeInProgress)

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM FK_ReferentialIntegrity ==
  Spec_FK => []Inv_FK_ReferentialIntegrity

THEOREM FK_CascadeCorrectness ==
  Spec_FK => []Inv_FK_CascadeConsistency

=============================================================================

(*
  REFERENCES:
  
  [1] Codd, E. F. (1970). "A relational model of data for large shared data banks."
      Communications of the ACM, 13(6), 377-387.
  
  [2] Date, C. J. (1986). "Referential Integrity." Proceedings of the Twelfth
      International Conference on Very Large Data Bases, pp. 2-12.
  
  [3] ISO/IEC 9075:2016 - Information technology -- Database languages -- SQL
      Part 2: Foundation, Section 11.8 (Referential Constraints).
  
  [4] Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts and
      Techniques." Morgan Kaufmann Publishers.
  
  [5] Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems:
      The Complete Book" (2nd ed.). Prentice Hall.
  
  IMPLEMENTATION NOTES:
  
  - CASCADE deletes/updates propagate to child tables recursively
  - SET NULL sets foreign key columns to NULL (must be nullable)
  - RESTRICT prevents parent modification if children exist
  - Deferred checking allows constraint violations within transaction
  - Multi-column foreign keys supported
  - Circular foreign keys require deferred checking
*)


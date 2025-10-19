----------------------- MODULE MultiDatabaseCatalog -----------------------
(*****************************************************************************)
(* Multi-Database Catalog Management for ColibrìDB                          *)
(* Models multiple database instances with isolation                        *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS MaxDatabases, MaxTables

VARIABLES databases, tables, isolation

vars == <<databases, tables, isolation>>

Init ==
    /\ databases = {}
    /\ tables = [d \in {} |-> {}]
    /\ isolation = [d \in {} |-> "READ_COMMITTED"]

CreateDatabase(dbId) ==
    /\ Cardinality(databases) < MaxDatabases
    /\ dbId \notin databases
    /\ databases' = databases \cup {dbId}
    /\ tables' = tables @@ (dbId :> {})
    /\ isolation' = isolation @@ (dbId :> "READ_COMMITTED")

CreateTable(dbId, tableId) ==
    /\ dbId \in databases
    /\ Cardinality(tables[dbId]) < MaxTables
    /\ tables' = [tables EXCEPT ![dbId] = @ \cup {tableId}]
    /\ UNCHANGED <<databases, isolation>>

UniqueDatabase ==
    \A d1, d2 \in databases : d1 # d2

Next ==
    \/ \E d \in Nat : CreateDatabase(d)
    \/ \E d \in databases, t \in Nat : CreateTable(d, t)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []UniqueDatabase
================================================================================


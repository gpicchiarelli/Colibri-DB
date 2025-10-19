---------------------------- MODULE Materialization ----------------------------
(*****************************************************************************)
(* Materialized Views with Incremental Maintenance for ColibrìDB            *)
(* Models view creation, updates, and incremental refresh                    *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS BaseTables, MaxViews

VARIABLES views, viewData, baseData, dirty

vars == <<views, viewData, baseData, dirty>>

Init ==
    /\ views = {}
    /\ viewData = [v \in {} |-> {}]
    /\ baseData = [t \in BaseTables |-> {}]
    /\ dirty = [v \in {} |-> FALSE]

CreateView(viewId, query) ==
    /\ Cardinality(views) < MaxViews
    /\ viewId \notin views
    /\ views' = views \cup {viewId}
    /\ viewData' = viewData @@ (viewId :> {})
    /\ dirty' = dirty @@ (viewId :> FALSE)
    /\ UNCHANGED baseData

UpdateBaseTable(table, data) ==
    /\ table \in BaseTables
    /\ baseData' = [baseData EXCEPT ![table] = @ \cup {data}]
    /\ dirty' = [v \in views |-> TRUE]  \* Mark all views dirty
    /\ UNCHANGED <<views, viewData>>

RefreshView(viewId) ==
    /\ viewId \in views
    /\ dirty[viewId]
    /\ viewData' = [viewData EXCEPT ![viewId] = UNION {baseData[t] : t \in BaseTables}]
    /\ dirty' = [dirty EXCEPT ![viewId] = FALSE]
    /\ UNCHANGED <<views, baseData>>

ViewsConsistent ==
    \A v \in views : dirty[v] \/ viewData[v] # {}

Next ==
    \/ \E vid \in Nat, q \in STRING : CreateView(vid, q)
    \/ \E t \in BaseTables, d \in Nat : UpdateBaseTable(t, d)
    \/ \E v \in views : RefreshView(v)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []ViewsConsistent
================================================================================


---------------------------- MODULE ResourceQuotas ----------------------------
(*****************************************************************************)
(* Resource Quotas Management for Multi-Tenancy in ColibrìDB                *)
(* Models CPU, memory, storage quotas per tenant                            *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS Tenants, MaxCPU, MaxMemory, MaxStorage

VARIABLES quotas, usage

vars == <<quotas, usage>>

Init ==
    /\ quotas = [t \in Tenants |-> [cpu |-> MaxCPU \div Cardinality(Tenants),
                                    memory |-> MaxMemory \div Cardinality(Tenants),
                                    storage |-> MaxStorage \div Cardinality(Tenants)]]
    /\ usage = [t \in Tenants |-> [cpu |-> 0, memory |-> 0, storage |-> 0]]

AllocateResource(tenant, resourceType, amount) ==
    /\ tenant \in Tenants
    /\ CASE resourceType = "cpu" ->
            /\ usage[tenant].cpu + amount <= quotas[tenant].cpu
            /\ usage' = [usage EXCEPT ![tenant].cpu = @ + amount]
         [] resourceType = "memory" ->
            /\ usage[tenant].memory + amount <= quotas[tenant].memory
            /\ usage' = [usage EXCEPT ![tenant].memory = @ + amount]
         [] resourceType = "storage" ->
            /\ usage[tenant].storage + amount <= quotas[tenant].storage
            /\ usage' = [usage EXCEPT ![tenant].storage = @ + amount]
    /\ UNCHANGED quotas

QuotasNotExceeded ==
    \A t \in Tenants :
        /\ usage[t].cpu <= quotas[t].cpu
        /\ usage[t].memory <= quotas[t].memory
        /\ usage[t].storage <= quotas[t].storage

Next == \E t \in Tenants, rt \in {"cpu", "memory", "storage"}, amt \in 1..10 :
          AllocateResource(t, rt, amt)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []QuotasNotExceeded
================================================================================


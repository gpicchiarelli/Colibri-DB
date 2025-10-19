--------------------------- MODULE ConnectionPooling ---------------------------
(*****************************************************************************)
(* Connection Pooling for ColibrìDB                                          *)
(* Models connection pool with timeout, recycling, max connections           *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS MaxConnections, MaxIdleTime

VARIABLES pool, active, idle, currentTime

vars == <<pool, active, idle, currentTime>>

Init ==
    /\ pool = {}
    /\ active = {}
    /\ idle = {}
    /\ currentTime = 0

AcquireConnection(connId) ==
    /\ Cardinality(active) < MaxConnections
    /\ connId \notin active
    /\ active' = active \cup {connId}
    /\ idle' = idle \ {connId}
    /\ pool' = pool \cup {connId}
    /\ UNCHANGED currentTime

ReleaseConnection(connId) ==
    /\ connId \in active
    /\ active' = active \ {connId}
    /\ idle' = idle \cup {[conn |-> connId, idleSince |-> currentTime]}
    /\ UNCHANGED <<pool, currentTime>>

EvictIdleConnections ==
    /\ \E conn \in idle :
         /\ conn.idleSince + MaxIdleTime < currentTime
         /\ idle' = idle \ {conn}
         /\ pool' = pool \ {conn.conn}
    /\ UNCHANGED <<active, currentTime>>

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<pool, active, idle>>

PoolSizeValid ==
    Cardinality(pool) <= MaxConnections

Next ==
    \/ \E c \in Nat : AcquireConnection(c)
    \/ \E c \in active : ReleaseConnection(c)
    \/ EvictIdleConnections
    \/ Tick

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []PoolSizeValid
================================================================================


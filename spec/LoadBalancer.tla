---------------------------- MODULE LoadBalancer ----------------------------
(*****************************************************************************)
(* Load Balancer: Round-Robin, Least-Connections, etc. for ColibrìDB        *)
(* Models load distribution across backend servers                           *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS Servers, MaxConnections

VARIABLES connections, nextServer, algorithm

vars == <<connections, nextServer, algorithm>>

Init ==
    /\ connections = [s \in Servers |-> 0]
    /\ nextServer = CHOOSE s \in Servers : TRUE
    /\ algorithm = "ROUND_ROBIN"

RoundRobin ==
    /\ algorithm = "ROUND_ROBIN"
    /\ connections' = [connections EXCEPT ![nextServer] = @ + 1]
    /\ nextServer' = CHOOSE s \in Servers : s # nextServer
    /\ UNCHANGED algorithm

LeastConnections ==
    /\ algorithm = "LEAST_CONN"
    /\ LET minConn == CHOOSE s \in Servers : 
             \A other \in Servers : connections[s] <= connections[other]
       IN connections' = [connections EXCEPT ![minConn] = @ + 1]
    /\ UNCHANGED <<nextServer, algorithm>>

BalancedLoad ==
    LET maxConn == Max({connections[s] : s \in Servers})
        minConn == Min({connections[s] : s \in Servers})
    IN maxConn - minConn <= 5

Next == RoundRobin \/ LeastConnections

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []BalancedLoad
================================================================================


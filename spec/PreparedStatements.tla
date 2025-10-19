---------------------------- MODULE PreparedStatements ----------------------------
(***************************************************************************
 * TLA+ Specification: Prepared Statements Protocol
 *
 * Based on:
 * [1] SQL Standard ISO/IEC 9075:2016
 *     Part 2: Foundation, Section 6.3: Prepared Statements
 *     International Organization for Standardization
 *
 * [2] Dean, J., & Ghemawat, S. (2004).
 *     "MapReduce: Simplified Data Processing on Large Clusters"
 *     OSDI 2004. (Query planning principles)
 *     
 * [3] Graefe, G. (1993).
 *     "Query Evaluation Techniques for Large Databases"
 *     ACM Computing Surveys, 25(2), 73-169.
 *     DOI: 10.1145/152610.152611
 *
 * Models prepared statement lifecycle, parameter binding, and execution.
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxStatements,      \* Maximum prepared statements
    Connections,        \* Set of connection IDs
    SQLTemplates        \* Set of SQL templates

ASSUME MaxStatements \in Nat \ {0}

VARIABLES
    preparedStmts,      \* [stmtId |-> statement_record]
    nextStmtId,         \* Next statement ID
    stmtsByConnection,  \* [connId |-> Set of stmtId]
    executions          \* [stmtId |-> execution_count]

vars == <<preparedStmts, nextStmtId, stmtsByConnection, executions>>

(***************************************************************************
 * Statement States
 ***************************************************************************)
StmtStates == {"PREPARED", "BOUND", "EXECUTED", "CLOSED"}

(***************************************************************************
 * Type Invariant
 ***************************************************************************)
TypeOK ==
    /\ preparedStmts \in [Nat -> [
        stmtId: Nat,
        connId: Connections,
        sqlTemplate: SQLTemplates,
        state: StmtStates,
        parameters: Seq(Value)
       ]]
    /\ nextStmtId \in Nat
    /\ stmtsByConnection \in [Connections -> SUBSET Nat]
    /\ executions \in [Nat -> Nat]

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ preparedStmts = [s \in {} |-> {}]
    /\ nextStmtId = 1
    /\ stmtsByConnection = [c \in Connections |-> {}]
    /\ executions = [s \in {} |-> 0]

(***************************************************************************
 * Actions
 ***************************************************************************)

\* Prepare statement
Prepare(connId, sqlTemplate) ==
    /\ connId \in Connections
    /\ sqlTemplate \in SQLTemplates
    /\ Cardinality(stmtsByConnection[connId]) < MaxStatements
    /\ LET stmtId == nextStmtId
           stmt == [
               stmtId |-> stmtId,
               connId |-> connId,
               sqlTemplate |-> sqlTemplate,
               state |-> "PREPARED",
               parameters |-> <<>>
           ]
       IN
        /\ preparedStmts' = preparedStmts @@ (stmtId :> stmt)
        /\ nextStmtId' = nextStmtId + 1
        /\ stmtsByConnection' = [stmtsByConnection EXCEPT 
            ![connId] = @ \cup {stmtId}]
        /\ executions' = executions @@ (stmtId :> 0)

\* Bind parameters
Bind(stmtId, params) ==
    /\ stmtId \in DOMAIN preparedStmts
    /\ preparedStmts[stmtId].state = "PREPARED"
    /\ preparedStmts' = [preparedStmts EXCEPT 
        ![stmtId].parameters = params,
        ![stmtId].state = "BOUND"]
    /\ UNCHANGED <<nextStmtId, stmtsByConnection, executions>>

\* Execute statement
Execute(stmtId) ==
    /\ stmtId \in DOMAIN preparedStmts
    /\ preparedStmts[stmtId].state = "BOUND"
    /\ preparedStmts' = [preparedStmts EXCEPT 
        ![stmtId].state = "EXECUTED"]
    /\ executions' = [executions EXCEPT ![stmtId] = @ + 1]
    /\ UNCHANGED <<nextStmtId, stmtsByConnection>>

\* Close statement
Close(stmtId) ==
    /\ stmtId \in DOMAIN preparedStmts
    /\ LET connId == preparedStmts[stmtId].connId
       IN
        /\ preparedStmts' = [s \in DOMAIN preparedStmts \ {stmtId} |-> 
                            preparedStmts[s]]
        /\ stmtsByConnection' = [stmtsByConnection EXCEPT 
            ![connId] = @ \ {stmtId}]
        /\ UNCHANGED <<nextStmtId, executions>>

Next ==
    \/ \E c \in Connections, sql \in SQLTemplates : Prepare(c, sql)
    \/ \E s \in DOMAIN preparedStmts, p \in Seq(Value) : Bind(s, p)
    \/ \E s \in DOMAIN preparedStmts : Execute(s)
    \/ \E s \in DOMAIN preparedStmts : Close(s)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties
 ***************************************************************************)

\* Statement limit per connection
StatementLimitEnforced ==
    \A c \in Connections : 
        Cardinality(stmtsByConnection[c]) <= MaxStatements

\* Execution requires binding
ExecutionRequiresBinding ==
    \A s \in DOMAIN preparedStmts :
        preparedStmts[s].state = "EXECUTED" =>
            preparedStmts[s].parameters # <<>>

Safety ==
    /\ StatementLimitEnforced
    /\ ExecutionRequiresBinding

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety

================================================================================


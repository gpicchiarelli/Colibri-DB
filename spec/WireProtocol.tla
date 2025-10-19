---------------------------- MODULE WireProtocol ----------------------------
(***************************************************************************
 * TLA+ Specification: Database Wire Protocol
 *
 * Based on:
 * [1] PostgreSQL Protocol 3.0 Documentation
 *     "PostgreSQL Frontend/Backend Protocol"
 *     https://www.postgresql.org/docs/current/protocol.html
 *     Official PostgreSQL documentation
 *
 * [2] MySQL Client/Server Protocol
 *     "MySQL Internals: Client/Server Protocol"
 *     https://dev.mysql.com/doc/internals/en/client-server-protocol.html
 *     Official MySQL documentation
 *
 * [3] Gray, J., & Reuter, A. (1992).
 *     "Transaction Processing: Concepts and Techniques"
 *     Morgan Kaufmann. Chapter 10: Client-Server Architecture
 *     ISBN: 1558601902
 *
 * This specification models the wire protocol including:
 * - Message framing and serialization
 * - Request/response flow
 * - Authentication handshake
 * - Query execution protocol
 * - Transaction boundaries
 * - Error propagation
 * - Connection state synchronization
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxMessageSize,    \* Maximum message size in bytes
    MaxPipelineDepth,  \* Maximum pipelined requests
    Clients,           \* Set of client IDs
    Servers            \* Set of server IDs

ASSUME MaxMessageSize \in Nat \ {0}
ASSUME MaxPipelineDepth \in Nat \ {0}

(***************************************************************************
 * Message Types (per PostgreSQL Protocol 3.0)
 ***************************************************************************)
MessageTypes == {
    \* Client -> Server
    "AUTH_REQUEST",       \* Authentication credentials
    "QUERY",              \* Simple query
    "PARSE",              \* Parse prepared statement
    "BIND",               \* Bind parameters
    "EXECUTE",            \* Execute prepared statement
    "DESCRIBE",           \* Describe statement/portal
    "SYNC",               \* Synchronization point
    "FLUSH",              \* Flush output
    "TERMINATE",          \* Close connection
    "COPY_DATA",          \* COPY data
    "COPY_DONE",          \* COPY completion
    "COPY_FAIL",          \* COPY failure
    
    \* Server -> Client
    "AUTH_OK",            \* Authentication successful
    "AUTH_REQUIRED",      \* Authentication required (challenge)
    "ERROR_RESPONSE",     \* Error occurred
    "NOTICE_RESPONSE",    \* Notice/warning
    "READY_FOR_QUERY",    \* Ready to accept new query
    "PARSE_COMPLETE",     \* Parse completed
    "BIND_COMPLETE",      \* Bind completed
    "ROW_DESCRIPTION",    \* Result column info
    "DATA_ROW",           \* Result row data
    "COMMAND_COMPLETE",   \* Command completed
    "EMPTY_QUERY",        \* Empty query string
    "PARAMETER_STATUS",   \* Parameter value
    
    \* Bidirectional
    "COPY_IN_RESPONSE",   \* Start COPY FROM
    "COPY_OUT_RESPONSE"   \* Start COPY TO
}

(***************************************************************************
 * Transaction States (per PostgreSQL)
 ***************************************************************************)
TransactionStates == {
    "IDLE",           \* Not in transaction block (I)
    "IN_TRANSACTION", \* In transaction block (T)
    "FAILED"          \* Failed transaction block (E)
}

(***************************************************************************
 * Protocol States
 ***************************************************************************)
ProtocolStates == {
    "STARTUP",        \* Initial startup phase
    "AUTHENTICATING", \* Authentication in progress
    "READY",          \* Ready for queries
    "EXECUTING",      \* Executing query
    "COPYING",        \* COPY in progress
    "CLOSING",        \* Connection closing
    "CLOSED"          \* Connection closed
}

VARIABLES
    \* Network state
    network,           \* [<<from, to>> |-> Sequence of messages]
    
    \* Client state
    clientStates,      \* [cid |-> client_state]
    clientTxnState,    \* [cid |-> transaction_state]
    clientPipeline,    \* [cid |-> pending_requests]
    
    \* Server state
    serverStates,      \* [sid |-> server_state]
    serverConnections, \* [sid |-> Set of cid]
    serverTxnState,    \* [<<sid, cid>> |-> transaction_state]
    
    \* Message sequencing
    clientSeqNum,      \* [cid |-> sequence_number]
    serverSeqNum       \* [<<sid, cid>> |-> sequence_number]

netVars == <<network>>
clientVars == <<clientStates, clientTxnState, clientPipeline, clientSeqNum>>
serverVars == <<serverStates, serverConnections, serverTxnState, serverSeqNum>>
vars == <<netVars, clientVars, serverVars>>

(***************************************************************************
 * Message Structure
 ***************************************************************************)
Message == [
    type: MessageTypes,
    from: Clients \cup Servers,
    to: Clients \cup Servers,
    seqNum: Nat,
    payload: [STRING -> Value],
    size: Nat
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ network \in [((Clients \cup Servers) \X (Clients \cup Servers)) -> Seq(Message)]
    /\ clientStates \in [Clients -> ProtocolStates]
    /\ clientTxnState \in [Clients -> TransactionStates]
    /\ clientPipeline \in [Clients -> Seq(Message)]
    /\ serverStates \in [Servers -> ProtocolStates]
    /\ serverConnections \in [Servers -> SUBSET Clients]
    /\ serverTxnState \in [((Servers \X Clients)) -> TransactionStates]
    /\ clientSeqNum \in [Clients -> Nat]
    /\ serverSeqNum \in [((Servers \X Clients)) -> Nat]

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ network = [link \in (Clients \cup Servers) \X (Clients \cup Servers) |-> <<>>]
    /\ clientStates = [c \in Clients |-> "STARTUP"]
    /\ clientTxnState = [c \in Clients |-> "IDLE"]
    /\ clientPipeline = [c \in Clients |-> <<>>]
    /\ serverStates = [s \in Servers |-> "READY"]
    /\ serverConnections = [s \in Servers |-> {}]
    /\ serverTxnState = [link \in (Servers \X Clients) |-> "IDLE"]
    /\ clientSeqNum = [c \in Clients |-> 1]
    /\ serverSeqNum = [link \in (Servers \X Clients) |-> 1]

(***************************************************************************
 * Helper Functions
 ***************************************************************************)
\* Send message over network
SendMessage(from, to, msg) ==
    LET link == <<from, to>>
    IN network' = [network EXCEPT ![link] = Append(@, msg)]

\* Receive message from network
ReceiveMessage(from, to) ==
    LET link == <<from, to>>
    IN IF Len(network[link]) > 0
       THEN <<Head(network[link]), 
              [network EXCEPT ![link] = Tail(@)]>>
       ELSE <<NULL, network>>

\* Check if message available
HasMessage(from, to) ==
    LET link == <<from, to>>
    IN Len(network[link]) > 0

(***************************************************************************
 * Actions: Authentication Phase (PostgreSQL Protocol)
 ***************************************************************************)

\* Client initiates authentication
ClientStartAuth(client, server) ==
    /\ client \in Clients
    /\ server \in Servers
    /\ clientStates[client] = "STARTUP"
    /\ LET msg == [
           type |-> "AUTH_REQUEST",
           from |-> client,
           to |-> server,
           seqNum |-> clientSeqNum[client],
           payload |-> [user |-> "dbuser", database |-> "dbname"],
           size |-> 64
       ]
       IN
        /\ SendMessage(client, server, msg)
        /\ clientStates' = [clientStates EXCEPT ![client] = "AUTHENTICATING"]
        /\ clientSeqNum' = [clientSeqNum EXCEPT ![client] = @ + 1]
        /\ UNCHANGED <<clientTxnState, clientPipeline, serverVars, serverSeqNum>>

\* Server responds to authentication
ServerAuthenticate(server, client, success) ==
    /\ server \in Servers
    /\ client \in Clients
    /\ HasMessage(client, server)
    /\ LET <<msg, net'>> == ReceiveMessage(client, server)
       IN
        /\ msg.type = "AUTH_REQUEST"
        /\ network' = net'
        /\ IF success
           THEN
               /\ LET resp == [
                      type |-> "AUTH_OK",
                      from |-> server,
                      to |-> client,
                      seqNum |-> serverSeqNum[<<server, client>>],
                      payload |-> [status |-> "authenticated"],
                      size |-> 32
                  ]
                  IN SendMessage(server, client, resp)
               /\ serverConnections' = [serverConnections EXCEPT 
                   ![server] = @ \cup {client}]
               /\ serverSeqNum' = [serverSeqNum EXCEPT 
                   ![<<server, client>>] = @ + 1]
           ELSE
               /\ LET resp == [
                      type |-> "ERROR_RESPONSE",
                      from |-> server,
                      to |-> client,
                      seqNum |-> serverSeqNum[<<server, client>>],
                      payload |-> [error |-> "auth_failed"],
                      size |-> 64
                  ]
                  IN SendMessage(server, client, resp)
               /\ UNCHANGED <<serverConnections, serverSeqNum>>
        /\ UNCHANGED <<clientVars, serverStates, serverTxnState>>

\* Client receives authentication result
ClientReceiveAuthResult(client, server) ==
    /\ client \in Clients
    /\ server \in Servers
    /\ clientStates[client] = "AUTHENTICATING"
    /\ HasMessage(server, client)
    /\ LET <<msg, net'>> == ReceiveMessage(server, client)
       IN
        /\ network' = net'
        /\ IF msg.type = "AUTH_OK"
           THEN clientStates' = [clientStates EXCEPT ![client] = "READY"]
           ELSE clientStates' = [clientStates EXCEPT ![client] = "CLOSING"]
        /\ UNCHANGED <<clientTxnState, clientPipeline, clientSeqNum, serverVars>>

(***************************************************************************
 * Actions: Query Execution (Simple Query Protocol)
 ***************************************************************************)

\* Client sends query
ClientSendQuery(client, server, queryText) ==
    /\ client \in Clients
    /\ server \in Servers
    /\ clientStates[client] = "READY"
    /\ Len(clientPipeline[client]) < MaxPipelineDepth
    /\ LET msg == [
           type |-> "QUERY",
           from |-> client,
           to |-> server,
           seqNum |-> clientSeqNum[client],
           payload |-> [sql |-> queryText],
           size |-> 128
       ]
       IN
        /\ SendMessage(client, server, msg)
        /\ clientStates' = [clientStates EXCEPT ![client] = "EXECUTING"]
        /\ clientPipeline' = [clientPipeline EXCEPT ![client] = Append(@, msg)]
        /\ clientSeqNum' = [clientSeqNum EXCEPT ![client] = @ + 1]
        /\ UNCHANGED <<clientTxnState, serverVars, serverSeqNum>>

\* Server processes query
ServerProcessQuery(server, client) ==
    /\ server \in Servers
    /\ client \in Clients
    /\ client \in serverConnections[server]
    /\ HasMessage(client, server)
    /\ LET <<msg, net'>> == ReceiveMessage(client, server)
       IN
        /\ msg.type = "QUERY"
        /\ network' = net'
        /\ serverStates' = [serverStates EXCEPT ![server] = "EXECUTING"]
        \* Send row description
        /\ LET rowDesc == [
               type |-> "ROW_DESCRIPTION",
               from |-> server,
               to |-> client,
               seqNum |-> serverSeqNum[<<server, client>>],
               payload |-> [columns |-> "col1,col2"],
               size |-> 64
           ]
           IN SendMessage(server, client, rowDesc)
        /\ serverSeqNum' = [serverSeqNum EXCEPT 
            ![<<server, client>>] = @ + 1]
        /\ UNCHANGED <<serverConnections, serverTxnState, clientVars>>

\* Server sends query result
ServerSendResult(server, client, success) ==
    /\ server \in Servers
    /\ client \in Clients
    /\ serverStates[server] = "EXECUTING"
    /\ LET seqNum == serverSeqNum[<<server, client>>]
       IN
        /\ IF success
           THEN
               \* Send data rows and command complete
               /\ LET dataRow == [
                      type |-> "DATA_ROW",
                      from |-> server,
                      to |-> client,
                      seqNum |-> seqNum,
                      payload |-> [values |-> "val1,val2"],
                      size |-> 128
                  ]
                  cmdComplete == [
                      type |-> "COMMAND_COMPLETE",
                      from |-> server,
                      to |-> client,
                      seqNum |-> seqNum + 1,
                      payload |-> [tag |-> "SELECT 1"],
                      size |-> 32
                  ]
                  ready == [
                      type |-> "READY_FOR_QUERY",
                      from |-> server,
                      to |-> client,
                      seqNum |-> seqNum + 2,
                      payload |-> [status |-> serverTxnState[<<server, client>>]],
                      size |-> 16
                  ]
                  IN
                   /\ SendMessage(server, client, dataRow)
                   /\ SendMessage(server, client, cmdComplete)
                   /\ SendMessage(server, client, ready)
                   /\ serverSeqNum' = [serverSeqNum EXCEPT 
                       ![<<server, client>>] = @ + 3]
           ELSE
               \* Send error response
               /\ LET error == [
                      type |-> "ERROR_RESPONSE",
                      from |-> server,
                      to |-> client,
                      seqNum |-> seqNum,
                      payload |-> [error |-> "query_error"],
                      size |-> 64
                  ]
                  ready == [
                      type |-> "READY_FOR_QUERY",
                      from |-> server,
                      to |-> client,
                      seqNum |-> seqNum + 1,
                      payload |-> [status |-> "FAILED"],
                      size |-> 16
                  ]
                  IN
                   /\ SendMessage(server, client, error)
                   /\ SendMessage(server, client, ready)
                   /\ serverSeqNum' = [serverSeqNum EXCEPT 
                       ![<<server, client>>] = @ + 2]
                   /\ serverTxnState' = [serverTxnState EXCEPT
                       ![<<server, client>>] = "FAILED"]
        /\ serverStates' = [serverStates EXCEPT ![server] = "READY"]
        /\ UNCHANGED <<serverConnections, clientVars>>

\* Client receives query result
ClientReceiveResult(client, server) ==
    /\ client \in Clients
    /\ server \in Servers
    /\ clientStates[client] = "EXECUTING"
    /\ HasMessage(server, client)
    /\ Len(clientPipeline[client]) > 0
    /\ LET <<msg, net'>> == ReceiveMessage(server, client)
       IN
        /\ network' = net'
        /\ IF msg.type = "READY_FOR_QUERY"
           THEN
               /\ clientStates' = [clientStates EXCEPT ![client] = "READY"]
               /\ clientPipeline' = [clientPipeline EXCEPT 
                   ![client] = Tail(@)]
               /\ clientTxnState' = [clientTxnState EXCEPT 
                   ![client] = msg.payload.status]
           ELSE
               \* Intermediate message (row data, etc.)
               UNCHANGED <<clientStates, clientPipeline, clientTxnState>>
        /\ UNCHANGED <<clientSeqNum, serverVars>>

(***************************************************************************
 * Actions: Connection Termination
 ***************************************************************************)

\* Client closes connection
ClientCloseConnection(client, server) ==
    /\ client \in Clients
    /\ server \in Servers
    /\ clientStates[client] \in {"READY", "CLOSING"}
    /\ LET msg == [
           type |-> "TERMINATE",
           from |-> client,
           to |-> server,
           seqNum |-> clientSeqNum[client],
           payload |-> [x \in {} |-> {}],
           size |-> 16
       ]
       IN
        /\ SendMessage(client, server, msg)
        /\ clientStates' = [clientStates EXCEPT ![client] = "CLOSED"]
        /\ UNCHANGED <<clientTxnState, clientPipeline, clientSeqNum, serverVars>>

\* Server processes connection close
ServerCloseConnection(server, client) ==
    /\ server \in Servers
    /\ client \in Clients
    /\ client \in serverConnections[server]
    /\ HasMessage(client, server)
    /\ LET <<msg, net'>> == ReceiveMessage(client, server)
       IN
        /\ msg.type = "TERMINATE"
        /\ network' = net'
        /\ serverConnections' = [serverConnections EXCEPT 
            ![server] = @ \ {client}]
        /\ UNCHANGED <<serverStates, serverTxnState, serverSeqNum, clientVars>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E c \in Clients, s \in Servers : ClientStartAuth(c, s)
    \/ \E s \in Servers, c \in Clients, success \in BOOLEAN :
        ServerAuthenticate(s, c, success)
    \/ \E c \in Clients, s \in Servers : ClientReceiveAuthResult(c, s)
    \/ \E c \in Clients, s \in Servers, q \in STRING :
        ClientSendQuery(c, s, q)
    \/ \E s \in Servers, c \in Clients : ServerProcessQuery(s, c)
    \/ \E s \in Servers, c \in Clients, success \in BOOLEAN :
        ServerSendResult(s, c, success)
    \/ \E c \in Clients, s \in Servers : ClientReceiveResult(c, s)
    \/ \E c \in Clients, s \in Servers : ClientCloseConnection(c, s)
    \/ \E s \in Servers, c \in Clients : ServerCloseConnection(s, c)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties
 ***************************************************************************)

\* Message order preserved
MessageOrderPreserved ==
    \A link \in DOMAIN network :
        LET msgs == network[link]
        IN \A i, j \in 1..Len(msgs) :
            i < j => msgs[i].seqNum < msgs[j].seqNum

\* No message loss (within pipeline)
NoMessageLoss ==
    \A c \in Clients :
        Len(clientPipeline[c]) <= MaxPipelineDepth

\* Transaction state consistency
TxnStateConsistent ==
    \A s \in Servers, c \in Clients :
        c \in serverConnections[s] =>
            serverTxnState[<<s, c>>] \in TransactionStates

\* Message size bounds
MessageSizeBounded ==
    \A link \in DOMAIN network :
        \A i \in 1..Len(network[link]) :
            network[link][i].size <= MaxMessageSize

Safety ==
    /\ MessageOrderPreserved
    /\ NoMessageLoss
    /\ TxnStateConsistent
    /\ MessageSizeBounded

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Messages eventually delivered
MessagesEventuallyDelivered ==
    \A link \in DOMAIN network :
        (Len(network[link]) > 0) ~> (Len(network[link]) = 0)

\* Queries eventually complete
QueriesEventuallyComplete ==
    \A c \in Clients :
        clientStates[c] = "EXECUTING" ~> clientStates[c] = "READY"

Liveness ==
    /\ MessagesEventuallyDelivered
    /\ QueriesEventuallyComplete

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []Liveness

================================================================================


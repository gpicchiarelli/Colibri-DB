---------------------------- MODULE ARTIndex ----------------------------
(***************************************************************************
 * TLA+ Specification: Adaptive Radix Tree (ART)
 *
 * Based on:
 * [1] Leis, V., Kemper, A., & Neumann, T. (2013).
 *     "The Adaptive Radix Tree: ARTful Indexing for Main-Memory Databases"
 *     IEEE ICDE 2013, pp. 38-49.
 *     DOI: 10.1109/ICDE.2013.6544812
 *     Original ART paper
 *
 * [2] Graefe, G. (2010).
 *     "A Survey of B-Tree Locking Techniques"
 *     ACM Transactions on Database Systems (TODS), 35(3), Article 16.
 *     DOI: 10.1145/1806907.1806908
 *     Concurrent access patterns
 *
 * [3] Bayer, R., & McCreight, E. M. (1972).
 *     "Organization and Maintenance of Large Ordered Indices"
 *     Acta Informatica, 1(3), 173-189.
 *     DOI: 10.1007/BF00288683
 *     Foundation for tree indexes
 *
 * [4] Morrison, D. R. (1968).
 *     "PATRICIA—Practical Algorithm To Retrieve Information 
 *      Coded in Alphanumeric"
 *     Journal of the ACM (JACM), 15(4), 514-534.
 *     DOI: 10.1145/321479.321481
 *     Radix tree foundation
 *
 * This specification models ART including:
 * - Adaptive node types (Node4, Node16, Node48, Node256)
 * - Path compression (lazy expansion)
 * - Prefix compression
 * - Insert, search, delete operations
 * - Node type transitions
 * - Space efficiency
 * - Cache-conscious layout
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxKeyLength,       \* Maximum key length in bytes
    Keys,               \* Set of keys (byte sequences)
    Values,             \* Set of values
    ByteValues          \* Possible byte values (0..255)

ASSUME MaxKeyLength \in Nat \ {0}
ASSUME ByteValues = 0..255

(***************************************************************************
 * Node Types (Leis 2013, Section 3.2)
 ***************************************************************************)
NodeTypes == {
    "NODE4",            \* 2-4 children (cache line optimized)
    "NODE16",           \* 5-16 children (SIMD search)
    "NODE48",           \* 17-48 children (256-byte index + pointers)
    "NODE256",          \* 49-256 children (direct array)
    "LEAF"              \* Leaf node with value
}

(***************************************************************************
 * Node Structure (Leis 2013, Section 3)
 ***************************************************************************)
\* Each node has:
\* - type: NodeType
\* - prefix: common prefix bytes
\* - prefixLen: length of prefix
\* - children: mapping from byte to child node ID

VARIABLES
    \* Tree structure
    nodes,              \* [nodeId |-> node_record]
    rootId,             \* Root node ID
    nextNodeId,         \* Next available node ID
    
    \* Node metadata
    nodeTypes,          \* [nodeId |-> node_type]
    nodePrefixes,       \* [nodeId |-> prefix_bytes]
    nodePrefixLen,      \* [nodeId |-> prefix_length]
    nodeChildren,       \* [nodeId |-> [byte |-> child_id]]
    nodeValues,         \* [nodeId |-> value] (for leaf nodes)
    
    \* Statistics
    treeHeight,         \* Current tree height
    totalNodes,         \* Total number of nodes
    totalKeys           \* Total number of keys

treeVars == <<nodes, rootId, nextNodeId>>
nodeVars == <<nodeTypes, nodePrefixes, nodePrefixLen, nodeChildren, nodeValues>>
statsVars == <<treeHeight, totalNodes, totalKeys>>
vars == <<treeVars, nodeVars, statsVars>>

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ nodes \subseteq Nat
    /\ rootId \in Nat \cup {0}
    /\ nextNodeId \in Nat
    /\ nodeTypes \in [Nat -> NodeTypes]
    /\ nodePrefixes \in [Nat -> Seq(ByteValues)]
    /\ nodePrefixLen \in [Nat -> 0..MaxKeyLength]
    /\ nodeChildren \in [Nat -> [ByteValues -> Nat]]
    /\ nodeValues \in [Nat -> Values]
    /\ treeHeight \in Nat
    /\ totalNodes \in Nat
    /\ totalKeys \in Nat

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ nodes = {}
    /\ rootId = 0
    /\ nextNodeId = 1
    /\ nodeTypes = [n \in {} |-> "NODE4"]
    /\ nodePrefixes = [n \in {} |-> <<>>]
    /\ nodePrefixLen = [n \in {} |-> 0]
    /\ nodeChildren = [n \in {} |-> [b \in ByteValues |-> 0]]
    /\ nodeValues = [n \in {} |-> NULL]
    /\ treeHeight = 0
    /\ totalNodes = 0
    /\ totalKeys = 0

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Count children of a node
ChildCount(nodeId) ==
    IF nodeId \notin nodes
    THEN 0
    ELSE Cardinality({b \in ByteValues : nodeChildren[nodeId][b] # 0})

\* Get node type based on child count (Leis 2013, Table 1)
GetNodeType(childCount) ==
    IF childCount <= 4 THEN "NODE4"
    ELSE IF childCount <= 16 THEN "NODE16"
    ELSE IF childCount <= 48 THEN "NODE48"
    ELSE "NODE256"

\* Check if node type should grow
ShouldGrowNode(nodeId) ==
    LET count == ChildCount(nodeId)
        ntype == nodeTypes[nodeId]
    IN
        \/ (ntype = "NODE4" /\ count > 4)
        \/ (ntype = "NODE16" /\ count > 16)
        \/ (ntype = "NODE48" /\ count > 48)

\* Check if node type should shrink
ShouldShrinkNode(nodeId) ==
    LET count == ChildCount(nodeId)
        ntype == nodeTypes[nodeId]
    IN
        \/ (ntype = "NODE16" /\ count <= 4)
        \/ (ntype = "NODE48" /\ count <= 16)
        \/ (ntype = "NODE256" /\ count <= 48)

\* Extract prefix from key
KeyPrefix(key, start, len) ==
    SubSeq(key, start, start + len - 1)

\* Common prefix length (Leis 2013, Section 3.1)
CommonPrefixLength(seq1, seq2) ==
    LET minLen == Min(Len(seq1), Len(seq2))
    IN
        CHOOSE i \in 0..minLen :
            /\ \A j \in 1..i : seq1[j] = seq2[j]
            /\ (i = minLen \/ seq1[i+1] # seq2[i+1])

(***************************************************************************
 * Actions: Node Creation and Management
 ***************************************************************************)

\* Create new node with given type
CreateNode(ntype, prefix, prefixLen) ==
    LET nodeId == nextNodeId
    IN
        /\ nodes' = nodes \cup {nodeId}
        /\ nextNodeId' = nextNodeId + 1
        /\ nodeTypes' = nodeTypes @@ (nodeId :> ntype)
        /\ nodePrefixes' = nodePrefixes @@ (nodeId :> prefix)
        /\ nodePrefixLen' = nodePrefixLen @@ (nodeId :> prefixLen)
        /\ nodeChildren' = nodeChildren @@ 
            (nodeId :> [b \in ByteValues |-> 0])
        /\ totalNodes' = totalNodes + 1
        /\ UNCHANGED <<rootId, nodeValues, treeHeight, totalKeys>>

\* Grow node to larger type (Leis 2013, Section 3.2)
GrowNode(nodeId) ==
    /\ nodeId \in nodes
    /\ ShouldGrowNode(nodeId)
    /\ LET oldType == nodeTypes[nodeId]
           childCount == ChildCount(nodeId)
           newType == GetNodeType(childCount)
       IN
        /\ nodeTypes' = [nodeTypes EXCEPT ![nodeId] = newType]
        /\ UNCHANGED <<treeVars, nodePrefixes, nodePrefixLen, nodeChildren,
                       nodeValues, statsVars>>

\* Shrink node to smaller type
ShrinkNode(nodeId) ==
    /\ nodeId \in nodes
    /\ ShouldShrinkNode(nodeId)
    /\ LET childCount == ChildCount(nodeId)
           newType == GetNodeType(childCount)
       IN
        /\ nodeTypes' = [nodeTypes EXCEPT ![nodeId] = newType]
        /\ UNCHANGED <<treeVars, nodePrefixes, nodePrefixLen, nodeChildren,
                       nodeValues, statsVars>>

(***************************************************************************
 * Actions: Insert Operation (Leis 2013, Algorithm 1)
 ***************************************************************************)

\* Insert key-value pair into empty tree
InsertIntoEmptyTree(key, value) ==
    /\ rootId = 0
    /\ key \in Keys
    /\ value \in Values
    /\ LET leafId == nextNodeId
       IN
        /\ nodes' = nodes \cup {leafId}
        /\ rootId' = leafId
        /\ nextNodeId' = nextNodeId + 1
        /\ nodeTypes' = nodeTypes @@ (leafId :> "LEAF")
        /\ nodePrefixes' = nodePrefixes @@ (leafId :> key)
        /\ nodePrefixLen' = nodePrefixLen @@ (leafId :> Len(key))
        /\ nodeChildren' = nodeChildren @@ 
            (leafId :> [b \in ByteValues |-> 0])
        /\ nodeValues' = nodeValues @@ (leafId :> value)
        /\ treeHeight' = 1
        /\ totalNodes' = 1
        /\ totalKeys' = 1

\* Insert key-value pair (simplified recursive insert)
InsertKey(nodeId, key, value, depth) ==
    /\ nodeId \in nodes
    /\ key \in Keys
    /\ value \in Values
    /\ depth < MaxKeyLength
    /\ LET ntype == nodeTypes[nodeId]
           prefix == nodePrefixes[nodeId]
           prefixLen == nodePrefixLen[nodeId]
       IN
        IF ntype = "LEAF"
        THEN
            \* Leaf node: need to split if keys differ
            /\ prefix # key
            /\ LET commonPrefixLen == CommonPrefixLength(prefix, key)
                   \* Create new inner node
                   newNodeId == nextNodeId
                   \* Create new leaf for new key
                   newLeafId == nextNodeId + 1
                   oldByte == IF commonPrefixLen < Len(prefix)
                             THEN prefix[commonPrefixLen + 1]
                             ELSE 0
                   newByte == IF commonPrefixLen < Len(key)
                             THEN key[commonPrefixLen + 1]
                             ELSE 0
               IN
                /\ nodes' = nodes \cup {newNodeId, newLeafId}
                /\ nextNodeId' = nextNodeId + 2
                /\ nodeTypes' = nodeTypes @@ 
                    (newNodeId :> "NODE4") @@ 
                    (newLeafId :> "LEAF")
                /\ nodePrefixes' = nodePrefixes @@ 
                    (newNodeId :> KeyPrefix(key, 1, commonPrefixLen)) @@
                    (newLeafId :> key)
                /\ nodePrefixLen' = nodePrefixLen @@ 
                    (newNodeId :> commonPrefixLen) @@
                    (newLeafId :> Len(key))
                /\ nodeChildren' = [nodeChildren EXCEPT 
                    ![newNodeId] = [b \in ByteValues |-> 
                        IF b = oldByte THEN nodeId
                        ELSE IF b = newByte THEN newLeafId
                        ELSE 0]]
                /\ nodeValues' = nodeValues @@ (newLeafId :> value)
                /\ totalNodes' = totalNodes + 2
                /\ totalKeys' = totalKeys + 1
                /\ UNCHANGED <<rootId, treeHeight>>
        ELSE
            \* Inner node: navigate to child
            /\ depth + prefixLen < Len(key)
            /\ LET keyByte == key[depth + prefixLen + 1]
                   childId == nodeChildren[nodeId][keyByte]
               IN
                IF childId = 0
                THEN
                    \* No child: create new leaf
                    /\ LET newLeafId == nextNodeId
                       IN
                        /\ nodes' = nodes \cup {newLeafId}
                        /\ nextNodeId' = nextNodeId + 1
                        /\ nodeTypes' = nodeTypes @@ (newLeafId :> "LEAF")
                        /\ nodePrefixes' = nodePrefixes @@ (newLeafId :> key)
                        /\ nodePrefixLen' = nodePrefixLen @@ 
                            (newLeafId :> Len(key))
                        /\ nodeChildren' = [nodeChildren EXCEPT 
                            ![nodeId][keyByte] = newLeafId]
                        /\ nodeValues' = nodeValues @@ (newLeafId :> value)
                        /\ totalNodes' = totalNodes + 1
                        /\ totalKeys' = totalKeys + 1
                        /\ UNCHANGED <<rootId, treeHeight>>
                ELSE
                    \* Recurse to child (simplified)
                    UNCHANGED vars

(***************************************************************************
 * Actions: Search Operation (Leis 2013, Algorithm 2)
 ***************************************************************************)

\* Search for key starting at node
SearchKey(nodeId, key, depth) ==
    /\ nodeId \in nodes
    /\ key \in Keys
    /\ depth < MaxKeyLength
    /\ LET ntype == nodeTypes[nodeId]
           prefix == nodePrefixes[nodeId]
           prefixLen == nodePrefixLen[nodeId]
       IN
        IF ntype = "LEAF"
        THEN
            \* Leaf: check if key matches
            prefix = key
        ELSE
            \* Inner node: check prefix and navigate
            /\ depth + prefixLen <= Len(key)
            /\ KeyPrefix(key, depth + 1, prefixLen) = prefix
            /\ LET keyByte == IF depth + prefixLen < Len(key)
                              THEN key[depth + prefixLen + 1]
                              ELSE 0
                   childId == nodeChildren[nodeId][keyByte]
               IN
                childId # 0 /\ SearchKey(childId, key, depth + prefixLen + 1)
    /\ UNCHANGED vars

(***************************************************************************
 * Actions: Delete Operation (Leis 2013, Section 3.3)
 ***************************************************************************)

\* Delete key (simplified)
DeleteKey(nodeId, key, depth) ==
    /\ nodeId \in nodes
    /\ key \in Keys
    /\ depth < MaxKeyLength
    /\ SearchKey(nodeId, key, depth)
    \* Simplified: just mark as deleted
    /\ totalKeys' = totalKeys - 1
    /\ UNCHANGED <<treeVars, nodeTypes, nodePrefixes, nodePrefixLen,
                   nodeChildren, nodeValues, treeHeight, totalNodes>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E key \in Keys, value \in Values : InsertIntoEmptyTree(key, value)
    \/ \E nodeId \in nodes, key \in Keys, value \in Values, depth \in 0..MaxKeyLength :
        InsertKey(nodeId, key, value, depth)
    \/ \E nodeId \in nodes : GrowNode(nodeId)
    \/ \E nodeId \in nodes : ShrinkNode(nodeId)
    \/ \E nodeId \in nodes, key \in Keys, depth \in 0..MaxKeyLength :
        SearchKey(nodeId, key, depth)
    \/ \E nodeId \in nodes, key \in Keys, depth \in 0..MaxKeyLength :
        DeleteKey(nodeId, key, depth)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Leis 2013)
 ***************************************************************************)

\* Node type matches child count (Leis 2013, Table 1)
NodeTypeMatchesChildren ==
    \A nodeId \in nodes :
        nodeTypes[nodeId] # "LEAF" =>
            LET count == ChildCount(nodeId)
                ntype == nodeTypes[nodeId]
            IN
                \/ (ntype = "NODE4" /\ count <= 4)
                \/ (ntype = "NODE16" /\ count <= 16)
                \/ (ntype = "NODE48" /\ count <= 48)
                \/ (ntype = "NODE256" /\ count <= 256)

\* Prefix length bounded
PrefixLengthBounded ==
    \A nodeId \in nodes : nodePrefixLen[nodeId] <= MaxKeyLength

\* Total nodes consistent
TotalNodesConsistent ==
    totalNodes = Cardinality(nodes)

\* Tree height reasonable
TreeHeightReasonable ==
    treeHeight <= MaxKeyLength

Safety ==
    /\ NodeTypeMatchesChildren
    /\ PrefixLengthBounded
    /\ TotalNodesConsistent
    /\ TreeHeightReasonable

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Inserts eventually complete
InsertsEventuallyComplete ==
    \A key \in Keys, value \in Values :
        InsertIntoEmptyTree(key, value) ~> (rootId # 0)

\* Searches eventually complete
SearchesEventuallyComplete ==
    \A nodeId \in nodes, key \in Keys, depth \in 0..MaxKeyLength :
        SearchKey(nodeId, key, depth) ~> TRUE

Liveness ==
    /\ InsertsEventuallyComplete

(***************************************************************************
 * Performance Properties (Leis 2013, Section 5)
 ***************************************************************************)

\* Space efficiency: ART uses less space than traditional tries
\* due to path compression and adaptive node sizes

\* Cache efficiency: Small node types (NODE4, NODE16) fit in cache lines
\* NODE4: ~32 bytes (fits in L1 cache line)
\* NODE16: ~64 bytes (fits in cache line)

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []NodeTypeMatchesChildren

================================================================================


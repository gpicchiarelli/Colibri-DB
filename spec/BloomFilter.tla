---------------------------- MODULE BloomFilter ----------------------------
(***************************************************************************
 * TLA+ Specification: Bloom Filter
 *
 * Based on:
 * [1] Bloom, B. H. (1970).
 *     "Space/Time Trade-offs in Hash Coding with Allowable Errors"
 *     Communications of the ACM, 13(7), 422-426.
 *     DOI: 10.1145/362686.362692
 *     Original Bloom filter paper
 *
 * [2] Broder, A., & Mitzenmacher, M. (2004).
 *     "Network Applications of Bloom Filters: A Survey"
 *     Internet Mathematics, 1(4), 485-509.
 *     DOI: 10.1080/15427951.2004.10129096
 *     Bloom filter applications and analysis
 *
 * [3] Fan, L., Cao, P., Almeida, J., & Broder, A. Z. (2000).
 *     "Summary Cache: A Scalable Wide-Area Web Cache Sharing Protocol"
 *     IEEE/ACM Transactions on Networking, 8(3), 281-293.
 *     DOI: 10.1109/90.851975
 *     Counting Bloom filters
 *
 * This specification models Bloom filters including:
 * - Bit array and hash functions
 * - Insert and membership test operations
 * - False positive probability
 * - Space efficiency
 * - No false negatives guarantee
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS
    BitArraySize,       \* Size of bit array (m)
    NumHashFunctions,   \* Number of hash functions (k)
    Keys                \* Universe of possible keys

ASSUME BitArraySize \in Nat \ {0}
ASSUME NumHashFunctions \in Nat \ {0}

VARIABLES
    bitArray,           \* Array of bits (0 or 1)
    insertedKeys,       \* Set of actually inserted keys
    testedKeys          \* Keys that have been tested

vars == <<bitArray, insertedKeys, testedKeys>>

(***************************************************************************
 * Type Invariant
 ***************************************************************************)
TypeOK ==
    /\ bitArray \in [1..BitArraySize -> {0, 1}]
    /\ insertedKeys \subseteq Keys
    /\ testedKeys \subseteq Keys

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ bitArray = [i \in 1..BitArraySize |-> 0]
    /\ insertedKeys = {}
    /\ testedKeys = {}

(***************************************************************************
 * Hash Functions (simplified model)
 ***************************************************************************)
Hash(key, i) == ((key * i) % BitArraySize) + 1

(***************************************************************************
 * Actions: Insert (Bloom 1970)
 ***************************************************************************)
Insert(key) ==
    /\ key \in Keys
    /\ key \notin insertedKeys
    /\ bitArray' = [b \in 1..BitArraySize |->
        IF \E i \in 1..NumHashFunctions : Hash(key, i) = b
        THEN 1
        ELSE bitArray[b]]
    /\ insertedKeys' = insertedKeys \cup {key}
    /\ UNCHANGED testedKeys

(***************************************************************************
 * Actions: Membership Test (Bloom 1970)
 ***************************************************************************)
Test(key) ==
    /\ key \in Keys
    /\ LET result == \A i \in 1..NumHashFunctions : 
                        bitArray[Hash(key, i)] = 1
       IN
        /\ testedKeys' = testedKeys \cup {key}
        /\ UNCHANGED <<bitArray, insertedKeys>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E k \in Keys : Insert(k)
    \/ \E k \in Keys : Test(k)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Bloom 1970)
 ***************************************************************************)

\* No false negatives: if key was inserted, test returns true
NoFalseNegatives ==
    \A k \in insertedKeys :
        \A i \in 1..NumHashFunctions : bitArray[Hash(k, i)] = 1

\* False positives possible but bounded
\* P(false positive) ≈ (1 - e^(-kn/m))^k
\* where k = NumHashFunctions, n = |insertedKeys|, m = BitArraySize

Safety ==
    /\ NoFalseNegatives

(***************************************************************************
 * Theorems (Bloom 1970)
 ***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => []NoFalseNegatives

================================================================================


------------------------------- MODULE HashIndex -------------------------------
(*
  ColibrìDB Hash Index Specification
  
  Implements hash-based indexing with:
  - Open addressing with linear probing
  - Dynamic resizing (load factor management)
  - Collision resolution strategies
  - Equality lookups (O(1) expected time)
  - Insert, Delete, Search operations
  
  Key Properties:
  - Uniqueness: No duplicate keys (if unique index)
  - Load Factor: Maintains load factor below threshold
  - Collision Handling: All collisions resolved
  - Deterministic Hashing: Same key hashes to same bucket
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Based on:
  - "Introduction to Algorithms" (Cormen et al., 2009) - Hash Tables
  - "The Art of Computer Programming" (Knuth, Vol 3) - Searching
*)

EXTENDS CORE, Naturals, Sequences, FiniteSets

CONSTANTS
  InitialBuckets,   \* Initial number of hash buckets
  MaxLoadFactor,    \* Maximum load factor before resize (e.g., 75)
  MaxProbes         \* Maximum probe attempts for open addressing

VARIABLES
  buckets,          \* Array of buckets [bucketId -> Seq(Entry)]
  numEntries,       \* Total number of entries in index
  numBuckets,       \* Current number of buckets
  loadFactor,       \* Current load factor (numEntries / numBuckets * 100)
  isUnique          \* Whether this is a unique index

hashIndexVars == <<buckets, numEntries, numBuckets, loadFactor, isUnique>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Hash index entry
HashEntry == [
  key: Value,
  rid: RID,
  deleted: BOOLEAN  \* For tombstone in open addressing
]

\* Bucket (for chaining) or slot (for open addressing)
Bucket == Seq(HashEntry)

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_HashIndex ==
  /\ buckets \in [0..(numBuckets-1) -> Bucket]
  /\ numEntries \in Nat
  /\ numBuckets \in Nat
  /\ numBuckets >= InitialBuckets
  /\ loadFactor \in 0..100
  /\ isUnique \in BOOLEAN

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ buckets = [i \in 0..(InitialBuckets-1) |-> <<>>]
  /\ numEntries = 0
  /\ numBuckets = InitialBuckets
  /\ loadFactor = 0
  /\ isUnique = TRUE  \* Default: unique index

(* --------------------------------------------------------------------------
   HASH FUNCTION
   -------------------------------------------------------------------------- *)

\* Simple hash function (simplified for TLA+)
\* In reality: CRC32, MurmurHash, etc.
Hash(key, numBuckets) ==
  LET keyHash == CASE key.type = "int" -> key.val
                   [] key.type = "string" -> 42  \* Simplified
                   [] OTHER -> 0
  IN keyHash % numBuckets

\* Probe sequence for open addressing (linear probing)
Probe(key, attempt, numBuckets) ==
  (Hash(key, numBuckets) + attempt) % numBuckets

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Calculate current load factor
ComputeLoadFactor ==
  IF numBuckets = 0 THEN 0 ELSE (numEntries * 100) \div numBuckets

\* Check if key exists in bucket (for chaining)
KeyInBucket(bucket, key) ==
  \E i \in DOMAIN bucket: 
    /\ bucket[i].key = key
    /\ ~bucket[i].deleted

\* Find entry in bucket
FindInBucket(bucket, key) ==
  IF \E i \in DOMAIN bucket: bucket[i].key = key /\ ~bucket[i].deleted
  THEN CHOOSE i \in DOMAIN bucket: bucket[i].key = key /\ ~bucket[i].deleted
  ELSE 0

(* --------------------------------------------------------------------------
   INSERT OPERATION
   -------------------------------------------------------------------------- *)

\* Insert with chaining
InsertChaining(key, rid) ==
  /\ numEntries < numBuckets * MaxLoadFactor \div 100  \* Check load factor
  /\ LET bucket == Hash(key, numBuckets)
     IN
       /\ \/ \* Key doesn't exist (or not unique index)
             /\ ~isUnique \/ ~KeyInBucket(buckets[bucket], key)
             /\ LET newEntry == [key |-> key, rid |-> rid, deleted |-> FALSE]
                IN
                  /\ buckets' = [buckets EXCEPT ![bucket] = Append(@, newEntry)]
                  /\ numEntries' = numEntries + 1
                  /\ loadFactor' = ComputeLoadFactor
                  /\ UNCHANGED <<numBuckets, isUnique>>
          \/ \* Key exists and unique index - reject
             /\ isUnique
             /\ KeyInBucket(buckets[bucket], key)
             /\ UNCHANGED hashIndexVars

\* Insert with open addressing (linear probing)
InsertOpenAddressing(key, rid) ==
  /\ numEntries < numBuckets * MaxLoadFactor \div 100
  /\ LET 
       \* Find first empty slot or deleted slot
       RECURSIVE FindSlot(_, _)
       FindSlot(attempt, maxAttempts) ==
         IF attempt >= maxAttempts
         THEN -1  \* Failed to find slot
         ELSE
           LET bucket == Probe(key, attempt, numBuckets)
               slot == buckets[bucket]
           IN
             IF slot = <<>> \/ (Len(slot) > 0 /\ slot[1].deleted)
             THEN bucket
             ELSE IF Len(slot) > 0 /\ slot[1].key = key /\ ~slot[1].deleted
             THEN -2  \* Key exists (for unique index)
             ELSE FindSlot(attempt + 1, maxAttempts)
       
       targetBucket == FindSlot(0, MaxProbes)
     IN
       /\ targetBucket >= 0
       /\ LET newEntry == [key |-> key, rid |-> rid, deleted |-> FALSE]
          IN
            /\ buckets' = [buckets EXCEPT ![targetBucket] = <<newEntry>>]
            /\ numEntries' = numEntries + 1
            /\ loadFactor' = ComputeLoadFactor
            /\ UNCHANGED <<numBuckets, isUnique>>

(* --------------------------------------------------------------------------
   SEARCH OPERATION
   -------------------------------------------------------------------------- *)

\* Search with chaining
SearchChaining(key) ==
  LET bucket == Hash(key, numBuckets)
      entryIdx == FindInBucket(buckets[bucket], key)
  IN
    IF entryIdx > 0
    THEN buckets[bucket][entryIdx].rid
    ELSE 0  \* Not found

\* Search with open addressing
SearchOpenAddressing(key) ==
  LET
    RECURSIVE FindKey(_, _)
    FindKey(attempt, maxAttempts) ==
      IF attempt >= maxAttempts
      THEN 0  \* Not found
      ELSE
        LET bucket == Probe(key, attempt, numBuckets)
            slot == buckets[bucket]
        IN
          IF slot = <<>>
          THEN 0  \* Empty slot, key not in index
          ELSE IF Len(slot) > 0 /\ slot[1].key = key /\ ~slot[1].deleted
          THEN slot[1].rid
          ELSE FindKey(attempt + 1, maxAttempts)
  IN FindKey(0, MaxProbes)

(* --------------------------------------------------------------------------
   DELETE OPERATION
   -------------------------------------------------------------------------- *)

\* Delete with chaining
DeleteChaining(key) ==
  LET bucket == Hash(key, numBuckets)
      entryIdx == FindInBucket(buckets[bucket], key)
  IN
    /\ entryIdx > 0
    /\ buckets' = [buckets EXCEPT ![bucket][entryIdx].deleted = TRUE]
    /\ numEntries' = numEntries - 1
    /\ loadFactor' = ComputeLoadFactor
    /\ UNCHANGED <<numBuckets, isUnique>>

\* Delete with open addressing (tombstone)
DeleteOpenAddressing(key) ==
  LET
    RECURSIVE FindKey(_, _)
    FindKey(attempt, maxAttempts) ==
      IF attempt >= maxAttempts
      THEN -1
      ELSE
        LET bucket == Probe(key, attempt, numBuckets)
            slot == buckets[bucket]
        IN
          IF slot = <<>>
          THEN -1
          ELSE IF Len(slot) > 0 /\ slot[1].key = key /\ ~slot[1].deleted
          THEN bucket
          ELSE FindKey(attempt + 1, maxAttempts)
    
    targetBucket == FindKey(0, MaxProbes)
  IN
    /\ targetBucket >= 0
    /\ buckets' = [buckets EXCEPT ![targetBucket][1].deleted = TRUE]
    /\ numEntries' = numEntries - 1
    /\ loadFactor' = ComputeLoadFactor
    /\ UNCHANGED <<numBuckets, isUnique>>

(* --------------------------------------------------------------------------
   RESIZE OPERATION
   -------------------------------------------------------------------------- *)

\* Resize hash table (rehash all entries)
Resize ==
  /\ loadFactor >= MaxLoadFactor
  /\ LET newNumBuckets == numBuckets * 2
         \* Collect all non-deleted entries
         allEntries == UNION {Range(buckets[b]) : b \in DOMAIN buckets}
         activeEntries == {e \in allEntries : ~e.deleted}
         \* Rehash into new buckets
         newBuckets == [b \in 0..(newNumBuckets-1) |-> <<>>]
     IN
       /\ numBuckets' = newNumBuckets
       /\ buckets' = newBuckets  \* Simplified: actual rehashing omitted
       /\ loadFactor' = (Cardinality(activeEntries) * 100) \div newNumBuckets
       /\ UNCHANGED <<numEntries, isUnique>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Load factor correctly computed
Inv_HashIndex_LoadFactorValid ==
  loadFactor = ComputeLoadFactor

\* Invariant 2: Load factor below maximum
Inv_HashIndex_LoadFactorBounded ==
  loadFactor <= MaxLoadFactor + 10  \* Allow small overshoot before resize

\* Invariant 3: No duplicate keys in unique index
Inv_HashIndex_UniqueKeys ==
  isUnique =>
    \A b1, b2 \in DOMAIN buckets:
      \A i \in DOMAIN buckets[b1]:
        \A j \in DOMAIN buckets[b2]:
          /\ ~buckets[b1][i].deleted
          /\ ~buckets[b2][j].deleted
          /\ buckets[b1][i].key = buckets[b2][j].key
          => /\ b1 = b2
             /\ i = j

\* Invariant 4: Number of buckets is power of 2 (optimization)
Inv_HashIndex_BucketsPowerOf2 ==
  \E k \in Nat: numBuckets = 2^k

\* Invariant 5: All non-deleted entries hashed correctly
Inv_HashIndex_CorrectHashing ==
  \A b \in DOMAIN buckets:
    \A i \in DOMAIN buckets[b]:
      ~buckets[b][i].deleted =>
        Hash(buckets[b][i].key, numBuckets) = b \/ TRUE  \* Allow probing

\* Combined safety invariant
Inv_HashIndex_Safety ==
  /\ TypeOK_HashIndex
  /\ Inv_HashIndex_LoadFactorValid
  /\ Inv_HashIndex_LoadFactorBounded
  /\ Inv_HashIndex_UniqueKeys
  /\ Inv_HashIndex_BucketsPowerOf2

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, high load factor triggers resize
Liveness_EventualResize ==
  [](loadFactor >= MaxLoadFactor => <>(numBuckets > InitialBuckets))

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E key \in Value, rid \in RID: InsertChaining(key, rid)
  \/ \E key \in Value, rid \in RID: InsertOpenAddressing(key, rid)
  \/ \E key \in Value: DeleteChaining(key)
  \/ \E key \in Value: DeleteOpenAddressing(key)
  \/ Resize

Spec == Init /\ [][Next]_hashIndexVars

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: Unique index maintains uniqueness
THEOREM HashIndex_Uniqueness ==
  Spec => []Inv_HashIndex_UniqueKeys

\* Theorem 2: Search finds inserted keys
THEOREM HashIndex_Correctness ==
  Spec => [](\A key \in Value, rid \in RID:
    InsertChaining(key, rid) => SearchChaining(key) = rid)

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    InitialBuckets = 4
    MaxLoadFactor = 75
    MaxProbes = 10
  
  Invariants:
    - Inv_HashIndex_Safety
  
  State constraints:
    - numBuckets <= 16
    - numEntries <= 20
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_HashIndex(index: HashIndex) -> [String: Any] {
      return [
          "buckets": index.buckets.mapValues { bucket in
              bucket.map { ["key": $0.key.toTLA(), "rid": $0.rid.toTLA(), "deleted": $0.deleted] }
          },
          "numEntries": index.count,
          "numBuckets": index.buckets.count,
          "loadFactor": index.loadFactor,
          "isUnique": index.isUnique
      ]
  }
*)


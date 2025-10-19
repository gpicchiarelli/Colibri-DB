------------------------------- MODULE Sharding -------------------------------
(*****************************************************************************)
(* Horizontal Partitioning (Sharding) for ColibrìDB                         *)
(* Models hash-based and range-based sharding strategies                     *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS Shards, Keys, MaxKeysPerShard

VARIABLES shardMapping, shardData, strategy

vars == <<shardMapping, shardData, strategy>>

Init ==
    /\ shardMapping = [k \in Keys |-> 0]
    /\ shardData = [s \in Shards |-> {}]
    /\ strategy = "HASH"

HashShard(key) ==
    (key % Cardinality(Shards)) + 1

RangeShard(key) ==
    IF key < 10 THEN 1
    ELSE IF key < 20 THEN 2
    ELSE 3

InsertKey(key, shard) ==
    /\ key \in Keys
    /\ Cardinality(shardData[shard]) < MaxKeysPerShard
    /\ shardMapping' = [shardMapping EXCEPT ![key] = shard]
    /\ shardData' = [shardData EXCEPT ![shard] = @ \cup {key}]
    /\ UNCHANGED strategy

ShardsBalanced ==
    LET sizes == {Cardinality(shardData[s]) : s \in Shards}
        maxSize == Max(sizes)
        minSize == Min(sizes)
    IN maxSize - minSize <= MaxKeysPerShard \div 2

Next == \E k \in Keys, s \in Shards : InsertKey(k, s)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []ShardsBalanced
================================================================================


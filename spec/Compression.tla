------------------------------ MODULE Compression ------------------------------
(*****************************************************************************)
(* Compression Algorithms for ColibrìDB                                     *)
(*                                                                           *)
(* Models: LZ4, Snappy, Zstd, Gzip compression with trade-offs             *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Ziv & Lempel (1977, 1978): LZ77/LZ78 algorithms                      *)
(*   - Collet & Turner: Zstandard compression                               *)
(*   - Google Snappy: Fast compression library                              *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS Algorithms, MaxBlocks, CompressionLevels

VARIABLES
    compressedBlocks,   \* Compressed data blocks
    statistics,         \* Compression statistics
    algorithm           \* Current algorithm

vars == <<compressedBlocks, statistics, algorithm>>

Init ==
    /\ compressedBlocks = <<>>
    /\ statistics = [totalBytes |-> 0, compressedBytes |-> 0, ratio |-> 0]
    /\ algorithm = "LZ4"

CompressionRatio(alg, level, dataSize) ==
    CASE alg = "LZ4" -> dataSize \div 2
      [] alg = "SNAPPY" -> dataSize \div 2
      [] alg = "ZSTD" -> dataSize \div (level + 1)
      [] alg = "GZIP" -> dataSize \div 4

Compress(data, alg, level) ==
    /\ Len(compressedBlocks) < MaxBlocks
    /\ LET compressed == CompressionRatio(alg, level, Len(data))
       IN /\ compressedBlocks' = Append(compressedBlocks,
              [original |-> Len(data), compressed |-> compressed, alg |-> alg])
          /\ statistics' = [statistics EXCEPT
               !.totalBytes = @ + Len(data),
               !.compressedBytes = @ + compressed]
    /\ UNCHANGED algorithm

Decompress(blockId) ==
    /\ blockId \in DOMAIN compressedBlocks
    /\ UNCHANGED vars

ValidCompressionRatio ==
    \A block \in compressedBlocks : block.compressed <= block.original

Next ==
    \/ \E d \in STRING, a \in Algorithms, l \in CompressionLevels : Compress(d, a, l)
    \/ \E b \in DOMAIN compressedBlocks : Decompress(b)

Spec == Init /\ [][Next]_vars

THEOREM CompressionCorrectness == Spec => []ValidCompressionRatio

================================================================================


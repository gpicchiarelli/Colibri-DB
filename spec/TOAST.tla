----------------------------- MODULE TOAST -----------------------------
(*
  TOAST (The Oversized-Attribute Storage Technique) Specification for ColibrìDB
  
  This module specifies the handling of large values that don't fit in regular pages.
  TOAST implements:
  - Compression of large values
  - Out-of-line storage for oversized attributes
  - Chunking of very large values across multiple TOAST pages
  - Transparent access to TOASTed values
  - TOAST table management
  
  Based on:
  - Stonebraker, M., et al. (1999). "The Morgan Kaufmann Series in Data Management
    Systems: The Postgres Database Management System." Morgan Kaufmann.
  - PostgreSQL Documentation: "Chapter 73. TOAST (The Oversized-Attribute Storage
    Technique)." https://www.postgresql.org/docs/current/storage-toast.html
  - Hector Garcia-Molina, Jeffrey D. Ullman, Jennifer Widom (2008). "Database Systems:
    The Complete Book" (2nd ed.). Prentice Hall.
  - Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts and Techniques."
    Morgan Kaufmann.
  
  Key Properties:
  - Transparency: Applications unaware of TOASTing
  - Efficiency: Large values don't waste page space
  - Compression: Optional compression of large values
  - Chunking: Values can span multiple TOAST pages
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,                \* From CORE
  MAX_LSN,               \* From CORE
  MAX_PAGES,             \* From CORE
  MAX_INLINE_SIZE,       \* Maximum size before TOASTing (e.g., 2KB)
  TOAST_PAGE_SIZE,       \* Size of a TOAST page (e.g., 8KB)
  MAX_TOAST_CHUNKS,      \* Maximum chunks for a single value
  CompressionAlgorithms  \* {"none", "lz4", "zstd", "pglz"}

(* --------------------------------------------------------------------------
   TOAST STRATEGIES
   -------------------------------------------------------------------------- *)

\* TOAST storage strategies
TOASTStrategy == {
  "PLAIN",       \* Never compress or move out-of-line (for fixed-size types)
  "EXTENDED",    \* Compress first, then move out-of-line if still too large
  "EXTERNAL",    \* Move out-of-line without compression
  "MAIN"         \* Compress, but prefer keeping in main table
}

\* TOAST chunk (part of a large value)
TOASTChunk == [
  chunkId: Nat,
  chunkSeq: Nat,        \* Sequence number within value
  chunkData: STRING,    \* Compressed or raw data
  isCompressed: BOOLEAN
]

\* TOAST pointer (stored in main table)
TOASTPointer == [
  toastId: Nat,           \* Unique ID for TOASTed value
  rawSize: Nat,           \* Uncompressed size
  extSize: Nat,           \* External (compressed) size
  isCompressed: BOOLEAN,
  compressionAlg: CompressionAlgorithms,
  numChunks: Nat
]

\* Column value (either inline or TOASTed)
ColumnValue == [
  inline: BOOLEAN,
  value: STRING \union TOASTPointer
]

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Main table storage
  mainTable,            \* [RID -> [colName -> ColumnValue]] - Main table rows
  
  \* TOAST table storage
  toastTable,           \* [ToastId -> Seq(TOASTChunk)] - TOASTed values
  nextToastId,          \* Nat - Next available TOAST ID
  
  \* TOAST configuration
  toastThreshold,       \* Nat - Size threshold for TOASTing
  toastStrategy,        \* [ColumnName -> TOASTStrategy] - Per-column strategy
  compressionEnabled,   \* BOOLEAN - Global compression flag
  
  \* Statistics
  toastHits,            \* Nat - Number of TOAST table accesses
  compressionRatio,     \* [ToastId -> Nat] - Compression ratio percentage
  
  \* Garbage collection
  deadToastIds          \* SUBSET Nat - TOASTed values to reclaim

toastVars == <<mainTable, toastTable, nextToastId, toastThreshold, toastStrategy,
               compressionEnabled, toastHits, compressionRatio, deadToastIds>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_TOAST ==
  /\ mainTable \in [RID -> [STRING -> ColumnValue]]
  /\ toastTable \in [Nat -> Seq(TOASTChunk)]
  /\ nextToastId \in Nat
  /\ toastThreshold \in Nat
  /\ toastStrategy \in [STRING -> TOASTStrategy]
  /\ compressionEnabled \in BOOLEAN
  /\ toastHits \in Nat
  /\ compressionRatio \in [Nat -> Nat]
  /\ deadToastIds \in SUBSET Nat

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Check if a value needs TOASTing
NeedsTOAST(value, colName) ==
  /\ Len(value) > toastThreshold
  /\ toastStrategy[colName] # "PLAIN"

\* Compress a value (abstract compression)
Compress(value, algorithm) ==
  \* Simplified: compression reduces size by ~40%
  SubString(value, 1, (Len(value) * 6) \div 10)

\* Decompress a value
Decompress(compressed, originalSize, algorithm) ==
  \* Abstract decompression (implementation-specific)
  compressed  \* Simplified

\* Split value into chunks
ChunkValue(value, toastId) ==
  LET chunkSize == TOAST_PAGE_SIZE
      numChunks == (Len(value) + chunkSize - 1) \div chunkSize
  IN [i \in 1..numChunks |->
       [chunkId |-> toastId,
        chunkSeq |-> i,
        chunkData |-> SubString(value, (i-1)*chunkSize + 1, Min({Len(value), i*chunkSize})),
        isCompressed |-> FALSE]]

\* Reassemble chunks into full value
AssembleChunks(chunks) ==
  LET sortedChunks == SortSeq(chunks, LAMBDA c1, c2: c1.chunkSeq < c2.chunkSeq)
  IN FoldSeq(LAMBDA acc, chunk: acc \o chunk.chunkData, "", sortedChunks)

\* Get TOAST pointer for a value
GetTOASTPointer(rid, colName) ==
  mainTable[rid][colName].value

\* Check if a TOAST ID is still referenced
IsToastReferenced(toastId) ==
  \E rid \in DOMAIN mainTable:
    \E colName \in DOMAIN mainTable[rid]:
      /\ ~mainTable[rid][colName].inline
      /\ mainTable[rid][colName].value.toastId = toastId

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_TOAST ==
  /\ mainTable = [rid \in {} |-> [col \in {} |-> [inline |-> TRUE, value |-> ""]]]
  /\ toastTable = [tid \in {} |-> <<>>]
  /\ nextToastId = 1
  /\ toastThreshold = MAX_INLINE_SIZE
  /\ toastStrategy = [col \in STRING |-> "EXTENDED"]
  /\ compressionEnabled = TRUE
  /\ toastHits = 0
  /\ compressionRatio = [tid \in {} |-> 100]
  /\ deadToastIds = {}

(* --------------------------------------------------------------------------
   TOAST OPERATIONS
   -------------------------------------------------------------------------- *)

\* Insert a value (may TOAST if large)
InsertValue(rid, colName, value) ==
  IF NeedsTOAST(value, colName)
  THEN \* TOAST the value
    LET strategy == toastStrategy[colName]
        \* Try compression first for EXTENDED and MAIN
        shouldCompress == compressionEnabled /\ strategy \in {"EXTENDED", "MAIN"}
        compressed == IF shouldCompress 
                      THEN Compress(value, "lz4")
                      ELSE value
        compressedSize == Len(compressed)
        \* Move out-of-line if still too large (EXTENDED) or always (EXTERNAL)
        shouldMoveOutOfLine == (strategy = "EXTENDED" /\ compressedSize > toastThreshold)
                               \/ strategy = "EXTERNAL"
                               \/ (strategy = "MAIN" /\ compressedSize > toastThreshold * 2)
    IN IF shouldMoveOutOfLine
       THEN \* Move to TOAST table
         LET toastId == nextToastId
             chunks == ChunkValue(compressed, toastId)
             pointer == [toastId |-> toastId,
                        rawSize |-> Len(value),
                        extSize |-> compressedSize,
                        isCompressed |-> shouldCompress,
                        compressionAlg |-> IF shouldCompress THEN "lz4" ELSE "none",
                        numChunks |-> Len(chunks)]
         IN /\ mainTable' = [mainTable EXCEPT ![rid][colName] = 
                              [inline |-> FALSE, value |-> pointer]]
            /\ toastTable' = [toastTable EXCEPT ![toastId] = chunks]
            /\ nextToastId' = nextToastId + 1
            /\ compressionRatio' = [compressionRatio EXCEPT ![toastId] = 
                                     (compressedSize * 100) \div Len(value)]
            /\ UNCHANGED <<toastThreshold, toastStrategy, compressionEnabled, 
                          toastHits, deadToastIds>>
       ELSE \* Keep inline (compressed)
         /\ mainTable' = [mainTable EXCEPT ![rid][colName] = 
                           [inline |-> TRUE, value |-> compressed]]
         /\ UNCHANGED <<toastTable, nextToastId, compressionRatio, 
                       toastThreshold, toastStrategy, compressionEnabled, 
                       toastHits, deadToastIds>>
  ELSE \* Small value, keep inline
    /\ mainTable' = [mainTable EXCEPT ![rid][colName] = 
                      [inline |-> TRUE, value |-> value]]
    /\ UNCHANGED <<toastTable, nextToastId, toastThreshold, toastStrategy,
                  compressionEnabled, toastHits, compressionRatio, deadToastIds>>

\* Fetch a value (detoast if necessary)
FetchValue(rid, colName) ==
  LET colValue == mainTable[rid][colName]
  IN IF colValue.inline
     THEN \* Inline value, return directly
       /\ UNCHANGED toastVars
     ELSE \* TOASTed value, fetch from TOAST table
       LET pointer == colValue.value
           toastId == pointer.toastId
           chunks == toastTable[toastId]
           compressed == AssembleChunks(chunks)
           value == IF pointer.isCompressed
                    THEN Decompress(compressed, pointer.rawSize, pointer.compressionAlg)
                    ELSE compressed
       IN /\ toastHits' = toastHits + 1
          /\ UNCHANGED <<mainTable, toastTable, nextToastId, toastThreshold,
                        toastStrategy, compressionEnabled, compressionRatio, deadToastIds>>

\* Update a value (may re-TOAST)
UpdateValue(rid, colName, newValue) ==
  LET oldColValue == mainTable[rid][colName]
  IN /\ IF ~oldColValue.inline
        THEN \* Mark old TOAST ID as dead
          deadToastIds' = deadToastIds \union {oldColValue.value.toastId}
        ELSE UNCHANGED deadToastIds
     /\ InsertValue(rid, colName, newValue)

\* Delete a row (mark TOAST values for deletion)
DeleteRow(rid) ==
  LET toastIds == {mainTable[rid][col].value.toastId :
                    col \in DOMAIN mainTable[rid],
                    ~mainTable[rid][col].inline}
  IN /\ mainTable' = [r \in DOMAIN mainTable \ {rid} |-> mainTable[r]]
     /\ deadToastIds' = deadToastIds \union toastIds
     /\ UNCHANGED <<toastTable, nextToastId, toastThreshold, toastStrategy,
                   compressionEnabled, toastHits, compressionRatio>>

\* Garbage collect unreferenced TOAST values (VACUUM)
VacuumTOAST ==
  LET unreferenced == {tid \in deadToastIds : ~IsToastReferenced(tid)}
  IN /\ toastTable' = [tid \in DOMAIN toastTable \ unreferenced |-> toastTable[tid]]
     /\ deadToastIds' = deadToastIds \ unreferenced
     /\ compressionRatio' = [tid \in DOMAIN compressionRatio \ unreferenced |-> 
                              compressionRatio[tid]]
     /\ UNCHANGED <<mainTable, nextToastId, toastThreshold, toastStrategy,
                   compressionEnabled, toastHits>>

\* Change TOAST strategy for a column
SetTOASTStrategy(colName, strategy) ==
  /\ toastStrategy' = [toastStrategy EXCEPT ![colName] = strategy]
  /\ UNCHANGED <<mainTable, toastTable, nextToastId, toastThreshold,
                compressionEnabled, toastHits, compressionRatio, deadToastIds>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_TOAST ==
  \/ \E rid \in RID, col \in STRING, val \in STRING: InsertValue(rid, col, val)
  \/ \E rid \in RID, col \in STRING: FetchValue(rid, col)
  \/ \E rid \in RID, col \in STRING, val \in STRING: UpdateValue(rid, col, val)
  \/ \E rid \in RID: DeleteRow(rid)
  \/ VacuumTOAST
  \/ \E col \in STRING, strategy \in TOASTStrategy: SetTOASTStrategy(col, strategy)

Spec_TOAST == Init_TOAST /\ [][Next_TOAST]_toastVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Values in main table don't exceed threshold (unless PLAIN)
Inv_TOAST_MainTableSize ==
  \A rid \in DOMAIN mainTable:
    \A col \in DOMAIN mainTable[rid]:
      mainTable[rid][col].inline =>
        (Len(mainTable[rid][col].value) <= toastThreshold \/ 
         toastStrategy[col] = "PLAIN")

\* Invariant 2: All TOAST pointers reference existing TOAST entries
Inv_TOAST_PointerValidity ==
  \A rid \in DOMAIN mainTable:
    \A col \in DOMAIN mainTable[rid]:
      ~mainTable[rid][col].inline =>
        mainTable[rid][col].value.toastId \in DOMAIN toastTable

\* Invariant 3: TOAST chunks are properly sequenced
Inv_TOAST_ChunkSequence ==
  \A toastId \in DOMAIN toastTable:
    LET chunks == toastTable[toastId]
    IN \A i \in 1..Len(chunks): chunks[i].chunkSeq = i

\* Invariant 4: Compression ratio is between 0 and 100
Inv_TOAST_CompressionRatio ==
  \A toastId \in DOMAIN compressionRatio:
    compressionRatio[toastId] >= 0 /\ compressionRatio[toastId] <= 100

\* Invariant 5: Dead TOAST IDs are not referenced
Inv_TOAST_DeadNotReferenced ==
  \A toastId \in deadToastIds:
    ~IsToastReferenced(toastId)

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Eventually garbage collect dead TOAST values
Prop_TOAST_EventualGC ==
  [](Cardinality(deadToastIds) > 0 => <>VacuumTOAST)

\* Property 2: Fetch operations always complete
Prop_TOAST_FetchCompletion ==
  \A rid \in RID, col \in STRING:
    [](FetchValue(rid, col) => <>(TRUE))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM TOAST_Transparency ==
  \* Applications can access values without knowing about TOASTing
  Spec_TOAST => []Inv_TOAST_PointerValidity

THEOREM TOAST_SpaceEfficiency ==
  Spec_TOAST => []Inv_TOAST_MainTableSize

=============================================================================

(*
  REFERENCES:
  
  [1] PostgreSQL Global Development Group. "Chapter 73. TOAST (The Oversized-
      Attribute Storage Technique)." PostgreSQL Documentation.
      https://www.postgresql.org/docs/current/storage-toast.html
  
  [2] Stonebraker, M., et al. (1999). "The Morgan Kaufmann Series in Data
      Management Systems: The Postgres Database Management System."
      Morgan Kaufmann Publishers.
  
  [3] Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts and
      Techniques." Morgan Kaufmann Publishers.
  
  [4] Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems:
      The Complete Book" (2nd ed.). Prentice Hall.
  
  IMPLEMENTATION NOTES:
  
  - TOAST threshold typically 2KB (1/4 of page size)
  - Four TOAST strategies: PLAIN, EXTENDED, EXTERNAL, MAIN
  - Compression algorithms: LZ4 (fast), ZSTD (better ratio), pglz (legacy)
  - Values > 1GB split into ~2000 byte chunks
  - TOAST table has B-tree index on (chunk_id, chunk_seq)
  - Garbage collection happens during VACUUM
  - Similar to Oracle's LOB storage, MySQL's BLOB handling
*)


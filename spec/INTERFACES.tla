------------------------------ MODULE INTERFACES ------------------------------
(*
  ColibrìDB Abstract API Interfaces
  
  This module defines abstract API contracts used across ColibrìDB components.
  These interfaces provide type signatures and preconditions/postconditions
  for key operations.
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Version: 1.0.0
*)

EXTENDS CORE

(* --------------------------------------------------------------------------
   WAL INTERFACE
   -------------------------------------------------------------------------- *)

\* WAL append operation
\* Precondition: record is valid
\* Postcondition: record appended with assigned LSN, nextLSN incremented
WAL_Append(wal, record) == TRUE  \* Abstract predicate

\* WAL flush operation
\* Precondition: lsn <= nextLSN
\* Postcondition: all records up to lsn durably written, flushedLSN updated
WAL_Flush(wal, lsn) == TRUE  \* Abstract predicate

\* WAL checkpoint operation
\* Precondition: system is in consistent state
\* Postcondition: checkpoint record written with DPT and ATT
WAL_Checkpoint(wal, dpt, att) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   TRANSACTION INTERFACE
   -------------------------------------------------------------------------- *)

\* Transaction begin
\* Precondition: none
\* Postcondition: new transaction created with unique TxId, status = active
TX_Begin(tm, isolationLevel) == TRUE  \* Abstract predicate

\* Transaction commit
\* Precondition: txId is active transaction
\* Postcondition: transaction committed, all writes visible, locks released
TX_Commit(tm, txId) == TRUE  \* Abstract predicate

\* Transaction rollback
\* Precondition: txId is active transaction
\* Postcondition: transaction aborted, all writes undone, locks released
TX_Rollback(tm, txId) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   LOCK INTERFACE
   -------------------------------------------------------------------------- *)

\* Lock acquisition
\* Precondition: resource is valid
\* Postcondition: lock granted if compatible, or txId added to wait queue
LOCK_Acquire(lm, resource, mode, txId) == TRUE  \* Abstract predicate

\* Lock release
\* Precondition: txId holds lock on resource
\* Postcondition: lock released, waiters notified
LOCK_Release(lm, resource, txId) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   MVCC INTERFACE
   -------------------------------------------------------------------------- *)

\* Create snapshot for transaction
\* Precondition: txId is active
\* Postcondition: snapshot contains set of visible transactions
MVCC_Snapshot(mvcc, txId) == TRUE  \* Abstract predicate

\* Check visibility of a version for a snapshot
\* Precondition: version and snapshot are valid
\* Postcondition: returns TRUE if version is visible to snapshot
MVCC_IsVisible(version, snapshot) == TRUE  \* Abstract predicate

\* Register new version
\* Precondition: txId is active, key is valid
\* Postcondition: new version added to version chain
MVCC_CreateVersion(mvcc, key, version, txId) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   BUFFER POOL INTERFACE
   -------------------------------------------------------------------------- *)

\* Fetch page from buffer pool
\* Precondition: pageId is valid
\* Postcondition: page returned from cache or loaded from disk
BUFFER_GetPage(pool, pageId) == TRUE  \* Abstract predicate

\* Write page to buffer pool
\* Precondition: pageId and page are valid
\* Postcondition: page in cache, marked dirty if dirty = TRUE
BUFFER_PutPage(pool, pageId, page, dirty) == TRUE  \* Abstract predicate

\* Evict page from buffer pool
\* Precondition: page is unpinned and evictable
\* Postcondition: page removed from cache, written to disk if dirty
BUFFER_Evict(pool, pageId) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   BTREE INTERFACE
   -------------------------------------------------------------------------- *)

\* Insert key-value pair into B+Tree
\* Precondition: key is valid
\* Postcondition: key inserted, tree remains balanced
BTREE_Insert(tree, key, value) == TRUE  \* Abstract predicate

\* Search for key in B+Tree
\* Precondition: key is valid
\* Postcondition: returns value if found, or NULL
BTREE_Search(tree, key) == TRUE  \* Abstract predicate

\* Delete key from B+Tree
\* Precondition: key exists
\* Postcondition: key deleted, tree remains balanced
BTREE_Delete(tree, key) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   RECOVERY INTERFACE
   -------------------------------------------------------------------------- *)

\* Perform ARIES recovery
\* Precondition: system crashed or starting up
\* Postcondition: database restored to consistent state, committed tx visible
RECOVERY_ARIES(db, wal) == TRUE  \* Abstract predicate

\* Analysis phase
\* Precondition: WAL is readable
\* Postcondition: ATT and DPT built from WAL scan
RECOVERY_Analysis(wal) == TRUE  \* Abstract predicate

\* Redo phase
\* Precondition: ATT and DPT built
\* Postcondition: all logged operations replayed idempotently
RECOVERY_Redo(wal, dpt) == TRUE  \* Abstract predicate

\* Undo phase
\* Precondition: Redo complete
\* Postcondition: uncommitted transactions rolled back
RECOVERY_Undo(wal, att) == TRUE  \* Abstract predicate

(* --------------------------------------------------------------------------
   HEAP INTERFACE
   -------------------------------------------------------------------------- *)

\* Insert row into heap table
\* Precondition: row is valid
\* Postcondition: row inserted, RID assigned
HEAP_Insert(heap, row) == TRUE  \* Abstract predicate

\* Read row from heap table
\* Precondition: rid is valid
\* Postcondition: returns row data
HEAP_Read(heap, rid) == TRUE  \* Abstract predicate

\* Update row in heap table
\* Precondition: rid exists
\* Postcondition: row updated to new data
HEAP_Update(heap, rid, newRow) == TRUE  \* Abstract predicate

\* Delete row from heap table
\* Precondition: rid exists
\* Postcondition: row marked deleted (tombstone)
HEAP_Delete(heap, rid) == TRUE  \* Abstract predicate

=============================================================================

(*
  USAGE:
  
  These interface predicates serve as contracts for operations.
  Concrete TLA+ modules will implement these operations and prove
  that preconditions and postconditions are maintained.
  
  Example:
  
  ---- MODULE WAL ----
  EXTENDS CORE, INTERFACES
  
  Append(record) ==
    /\ WAL_Append(wal, record)  \* Use interface contract
    /\ wal' = [wal EXCEPT !.records = Append(@, record)]
    /\ ...
  ====================
*)


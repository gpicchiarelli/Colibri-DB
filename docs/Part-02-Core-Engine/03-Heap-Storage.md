# Capitolo 7 — Storage Heap e Gestione Tuple

## 7.1 File Heap
- `FileHeapTable` dettagli: header, slot directory, gestione id (`RID`).
- Inserimento (`insert`), lettura (`read`), update/delete.

## 7.2 Integrazione con Buffer Pool
- `openPage`, `markDirty(pageLSN:)`.
- Pagina vs record: versioning e tombstone.

## 7.3 Free Space Management
- `FreeSpaceMap`, `allocatePage`.
- Algoritmi di scelta pagina (first fit, best fit).

## 7.4 Vacuum e Compattazione
- `Database.vacuumTable`, `VacuumJob`.
- Interazione con WAL (CLR, undo).

## 7.5 Laboratorio
- Esempio di frammentazione -> vacuum -> verifica.

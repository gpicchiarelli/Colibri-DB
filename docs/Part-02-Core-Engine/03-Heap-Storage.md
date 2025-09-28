# Capitolo 7 — Storage Heap e Gestione Tuple

## 7.1 Modello heap
Il file heap è un contenitore non ordinato di tuple. La struttura fisica consiste in pagine con slot directory. `FileHeapTable` fornisce l'API per manipolare tuple persistenti.

## 7.2 Inserimento
`insert(row:pageLSN:)`:
1. Seleziona una pagina con spazio (`FreeSpaceMap.nextPage`).
2. Carica la pagina dal buffer pool.
3. Codifica la tupla in formato binario (usando `RowEncoder`).
4. Aggiorna la directory degli slot.
5. Ritorna un `RID` (pageId, slotId).

Analizziamo la complessità e i possibili errori (pagina full, encoding fallito).

## 7.3 Lettura e update
`read(rid:)` decodifica la tupla. `update(rid:newRow:pageLSN:)` effettua un delete+insert (per MVP). Spieghiamo come l'aggiornamento gestisce tombstone e versioni.

## 7.4 Delete e tombstone
`delete(rid:pageLSN:)` marca lo slot come vuoto. Il vacuum successivo compatterà la pagina.

## 7.5 FreeSpaceMap
Struttura heap di priorità che mantiene pagine con spazio disponibile. Analizziamo il codice e la complessità.

## 7.6 Vacuum e compattazione
`vacuum()` e `compactPage(pageId:)` eliminano tombstone e riducono frammentazione. Collegamento con comandi CLI (`\vacuum`).

## 7.7 Laboratorio
- Inserire, cancellare e osservare `FreeSpaceMap`.
- Eseguire vacuum e confrontare la dimensione del file.

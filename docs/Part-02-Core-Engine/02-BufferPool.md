# Capitolo 6 — Buffer Pool e Gestione Pagine

## 6.1 Modello teorico
Il buffer pool funge da cache per pagine di disco. L'obiettivo è minimizzare gli I/O mantenendo coerenza con la memoria persistente. Dal punto di vista della teoria delle code, possiamo modellare l'accesso alle pagine come un processo stocastico e analizzare le politiche di rimpiazzamento (LRU, CLOCK, MRU). ColibrìDB implementa una variante di LRU con lock.

## 6.2 Strutture dati
- `BufferPool`: mantiene `frames` (dictionary), `lruList`, `lock`.
- `BufferFrame`: contiene `pageId`, `data`, `pinCount`, `isDirty`, `lastAccess`.

## 6.3 Pin/unpin
`pin(pageId:)` carica una pagina nel buffer; incrementa `pinCount`. `unpin(pageId:)` decrementa e consente l'eviction. Gli invarianti assicurano che una pagina con `pinCount > 0` non venga rimossa.

## 6.4 Dirty tracking e flush
`markDirty(pageId:)` registra le pagine modificate. `flushAll()` scorre i frame dirty e chiama `storage.write(page:)` dopo aver verificato `page.pageLSN ≤ wal.flushedLSN`.

## 6.5 Eviction
`evictVictim()` seleziona la pagina meno recentemente usata con `pinCount == 0`. Se nessuna pagina è disponibile, solleva un'eccezione (indica configurazione insufficiente).

## 6.6 Namespace manager
`BufferNamespaceManager` gestisce più buffer pool (per tabelle, indici). Documentiamo `registerNamespace`, `flush(namespace:)` e `stats(namespace:)`.

## 6.7 Laboratorio
- Caricare una tabella in memoria e misurare hit ratio.
- Simulare workload per verificare politica LRU.
- Utilizzare `coldb-dev \buffer stats` per osservare le metriche in tempo reale.

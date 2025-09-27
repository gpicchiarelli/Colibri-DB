# Buffer Pool

## Obiettivi
- Ridurre I/O casuale mantenendo in memoria pagine calde di tabelle e indici.
- Applicare politiche flessibili (LRU, Clock, LRU-2 approssimato) selezionabili a runtime.
- Misurare hit/miss/dirty/pinned per guidare tuning e manutenzione automatica.
- Consentire flusher asincroni per ridurre la latenza percepita dalle transazioni.

## Implementazione attuale
- `LRUBufferPool` gestisce pagine di dimensione fissa (`pageSize`) con capacità configurabile per area (tabelle/indici).
- Quote per namespace tramite `BufferNamespaceManager` impediscono che un indice monopolizzi il pool.
- Deferred write opzionale: le pagine dirty vengono accumulate e flushate a soglia (`maxDirty`) o tramite background timer.
- Eviction policy runtime (`setEvictionPolicy`) supporta `lru`, `clock`, `lru2`.
- Pins per prevenire eviction di pagine critiche (es. root di B+Tree, pagine in uso da transazioni).

## API principali
- `getPage(pid)` — lettura non bloccante; aggiorna la politica di accesso.
- `pinPage(pid)` / `unpinPage(pid)` — incrementa/decrementa il contatore di pin.
- `putPage(pid, data, dirty)` — scrive/aggiorna una pagina e gestisce flush immediato o differito.
- `flushPage(pid)` / `flushAll()` — sincronizza con lo storage sottostante.
- `startBackgroundFlush(every:)` — avvia un timer per flush asincrono; attiva automaticamente la modalità deferred write.

## Telemetria
- `statsString()` restituisce una stringa sintetica con hits/misses/evictions/pages/pinned/dirty.
- `Database.bufferPoolStats()` aggrega le statistiche per namespace e viene esposto via CLI (`\\bp`).
- `Database.bufferPoolAggregateStats()` fornisce la vista complessiva (`\\stats`, `\\stats prometheus`).

## Integrazione con il resto del motore
- `FileHeapTable` usa il buffer pool per leggere/scrivere pagine heap.
- `FileBPlusTreeIndex` alloca un pool separato con timer di flush rapido (0.5s) per ridurre la latenza delle scritture sugli indici persistenti.
- Le politiche di compattazione consultano `hits/misses` per valutare l'efficacia del buffer.

## Roadmap
- Adaptive Replacement Cache (ARC) e 2Q avanzato.
- Segmentazione hot/cold dinamica guidata da metriche.
- Persistenza periodica delle statistiche per analisi storica.
- Telemetria integrata con `os_log` e Instruments per profiling su Apple Silicon.

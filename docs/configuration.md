# Configurazione (`colibridb.conf.json`)

La configurazione è serializzata in JSON e decodificata in `DBConfig`. Le chiavi mancanti ereditano i valori di default, così gli upgrade restano retro-compatibili.

## Parametri generali
- `dataDir` — percorso directory dati (default `./data`).
- `storageEngine` — `"FileHeap"` o `"InMemory"` per test.
- `indexImplementation` — backend predefinito per gli indici in-memory (`Hash`, `ART`, `BTree`, ...).
- `pageSizeBytes` — dimensione pagina (default 8192).
- `bufferPoolSizeBytes` — dimensione teorica complessiva del buffer pool (informativa; il pool reale usa quote per namespace).
- `walEnabled` / `checksumEnabled` — abilita WAL e checksum a livello di database.
- `walFullFSyncEnabled` — forza l'uso di `F_FULLFSYNC` sul WAL (solo macOS) per massima durabilità; il flag ora vale anche per i WAL degli indici e per i comandi `\flush ... fullsync`.
- `ioSequentialReadHint` — abilita hint I/O (F_RDAHEAD, `posix_fadvise`, `preadv2`/`preadv`) su scan heap, replay WAL e rebuild degli indici.
- `cliEnabled`, `metricsEnabled`, `serverEnabled` — feature flag per front-end futuri.

## Buffer pool & caching
- `bufferPoolEnabled` — abilita il buffer pool globale (true consigliato).
- `dataBufferPoolPages` — pagine dedicate alle tabelle (default 16384 ≈ 128MB @ 8KB).
- `indexBufferPoolPages` — pagine per gli indici persistenti (default 4096 ≈ 32MB).
- `bufferFlushQoS` — livello di QoS (`utility`, `background`, `userInitiated`, ecc.) per la queue di flush del buffer pool.
- `walCompression` — abilita la compressione (`none`, `lzfse`, `zlib`) sui payload del WAL; i record sono decompressi in automatico in fase di replay.
- `pageFlushCompression` — quando diverso da `none`, genera uno snapshot compresso (`.lzfse`/`.zlib`) del file heap a ogni `flush`.

## Compattazione & manutenzione
- `autoCompactionEnabled` — avvia il vacuum periodico all'avvio.
- `autoCompactionIntervalSeconds` — intervallo tra run del vacuum.
- `autoCompactionPagesPerRun` — numero di pagine processate per run.
- `heapFragmentationThreshold` — soglia minima di frammentazione per attivare compattazione.
- `heapFragmentationMinPages` — pagine minime da campionare.
- `heapFragmentationSamplePages` — campione utilizzato per stimare frammentazione.
- `indexLeafOccupancyThreshold` — soglia occupazione foglie B+Tree per pianificare compattazioni.
- `indexCompactionCooldownSeconds` — cooldown minimo tra due compattazioni dello stesso indice.

## Ottimizzazione & statistiche
- `optimizerStatsSampleRows` — numero di righe campionate per stimare cardinalità.

## Concorrenza
- `maxConnectionsLogical` — target di connessioni logiche multiplexate.
- `maxConnectionsPhysical` — numero massimo di worker fisici.
- `lockTimeoutSeconds` — timeout predefinito dei lock.
- `defaultIsolationLevel` — isolamento predefinito (`readCommitted`, `repeatableRead`, ...); il valore è serializzato tramite enum.

## Esempio completo
```json
{
  "dataDir": "./data",
  "storageEngine": "FileHeap",
  "indexImplementation": "BTree",
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "bufferPoolEnabled": true,
  "dataBufferPoolPages": 16384,
  "indexBufferPoolPages": 4096,
  "autoCompactionEnabled": true,
  "autoCompactionIntervalSeconds": 5.0,
  "autoCompactionPagesPerRun": 32,
  "heapFragmentationThreshold": 0.2,
  "indexLeafOccupancyThreshold": 0.6,
  "lockTimeoutSeconds": 5.0,
  "defaultIsolationLevel": "readCommitted",
  "walFullFSyncEnabled": false,
  "bufferFlushQoS": "utility",
  "ioSequentialReadHint": false,
  "walCompression": "none",
  "pageFlushCompression": "none"
}
```

Aggiorna `docs/configuration.md` ogni volta che vengono aggiunte nuove chiavi in `DBConfig`.

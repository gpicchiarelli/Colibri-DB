# Benchmarking ColibrìDB

Questo documento descrive come eseguire benchmark micro/macro del motore ColibrìDB utilizzando il nuovo harness `benchmarks`.

## Prerequisiti
- macOS 13+
- Toolchain Swift 6.2 (è sufficiente `swift build`)
- Spazio su disco per dati temporanei (gli scenari B+Tree creano directory effimere sotto `/tmp`).

## Compilazione
```
swift build -c release --product benchmarks
swift build -c release --product benchmarks-extra
```
I target `benchmarks` e `benchmarks-extra` dipendono da `ColibriCore` e utilizzano configurazioni in‑memory oppure directory temporanee per ridurre l’impatto sulla sandbox del progetto.

## Esecuzione
```
.build/release/benchmarks [iterations] [scenario]
.build/release/benchmarks-extra [iterations] [scenario] [--workers=N] [--json]
```
- **iterations** (opzionale): numero di iterazioni per lo scenario; default `10000`.
- **scenario** (opzionale): uno tra `heap-insert`, `heap-scan`, `btree-lookup`, `planner-join`. Se omesso vengono eseguiti tutti in sequenza.
- Usa `--help` per un riepilogo degli argomenti.

### Scenari disponibili (benchmarks)
| Scenario | Descrizione | Configurazione |
| --- | --- | --- |
| `heap-insert` | Inserimento massivo in tabella in-memory | `DBConfig(storageEngine: "InMemory")`, vacuum disabilitato |
| `heap-scan` | Scan completo dopo popolamento tabella | Same as above |
| `btree-lookup` | Costruzione indice B+Tree e lookup puntuali | Tabelle su disco temporaneo, indice persistente |
| `planner-join` | Query pianificata con filtro + join + ORDER BY | Planner Volcano con parallel map (2 worker) |

Ogni run stampa per scenario: numero di iterazioni, tempo totale in millisecondi e throughput (operazioni/s).
Con `benchmarks-extra` viene stampato anche un rapporto parlante con statistiche di latenza (mean, p50, p90, p95, p99, min, max, stddev) e metadati utili. Aggiungendo `--json` il rapporto viene emesso in formato JSON per la CI.

Esempi:
```
# Tutti gli scenari con 5k iterazioni
.build/release/benchmarks 5000

# Solo benchmark B+Tree con 20k lookup
.build/release/benchmarks 20000 btree-lookup
```

### Scenari disponibili (benchmarks-extra)
| Scenario | Categoria | Descrizione breve |
| --- | --- | --- |
| heap-delete | Heap | Delete per chiave dopo popolamento |
| heap-read-rid | Heap | Letture puntuali via RID |
| fileheap-insert-wal-off | File/WAL | Insert su heap file senza WAL |
| fileheap-insert-wal-fsync | File/WAL | Insert con WAL e fsync pieno |
| wal-append-none/lzfse/zlib | WAL | Append micro (algoritmo compressione) |
| btree-insert | B+Tree | Insert incrementale con indice presente |
| btree-range | B+Tree | Range scan [lo,hi] su indice persistente |
| btree-bulk-build | B+Tree | Rebuild bulk da table scan |
| idx-hash/art/skiplist/lsm | Indici in‑memory | Lookup/range con vari backend |
| tx-commit/tx-rollback | Transazioni | Begin/commit/rollback ripetuti |
| tx-contention | Transazioni | Throughput in contesa (flag --workers) |
| mvcc-snapshot-read | MVCC | Scan snapshot mentre un writer modifica |
| planner-index-scan | Planner | Accesso via indice con predicate |
| planner-sort-limit | Planner | Sort + limit con parallelismo |
| checkpoint | Manutenzione | Durata checkpoint su dati on‑disk |
| vacuum-compact | Manutenzione | Compattazione pagine heap |

Esempi:
```
# Rebuild bulk B+Tree
.build/release/benchmarks-extra 5000 btree-bulk-build

# Contesa transazionale con 8 worker
.build/release/benchmarks-extra 20000 tx-contention --workers=8
```

## Linee guida per interpretare i risultati
- **Throughput (ops/s)**: metrica primaria per confrontare modifiche; registrare i valori baseline per confronto regressioni.
- **Elapsed ms**: utile per valutare la varianza; eseguire più run e calcolare media/deviazione.
- **Resource usage**: monitorare CPU (`Activity Monitor` o `top`) e I/O (`fs_usage`) durante gli scenari per capire le curve di scaling.

## Estensioni future
- Aggiungere scenari WAL/flush con `config.walEnabled = true`.
- Eseguire workload misti (read/write) e join multipli con parametri via CLI.
- Integrare esportazione CSV/JSON dei risultati per pipeline CI.

Per pianificare nuovi benchmark consultare anche `docs/dimensional-limits.md` per dimensionare dataset e buffer in modo coerente.

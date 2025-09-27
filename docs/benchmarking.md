# Benchmarking ColibrìDB

Questo documento descrive come eseguire benchmark micro/macro del motore ColibrìDB utilizzando il nuovo harness `benchmarks`.

## Prerequisiti
- macOS 13+
- Toolchain Swift 6.2 (è sufficiente `swift build`)
- Spazio su disco per dati temporanei (gli scenari B+Tree creano directory effimere sotto `/tmp`).

## Compilazione
```
swift build -c release --product benchmarks
```
Il target `benchmarks` dipende da `ColibriCore` e utilizza configurazioni in‑memory oppure directory temporanee per ridurre l’impatto sulla sandbox del progetto.

## Esecuzione
```
.build/release/benchmarks [iterations] [scenario] [--workers=N] [--granular] [--json]
```
- **iterations** (opzionale): numero di iterazioni per lo scenario; default `10000`.
- **scenario** (opzionale): vedi tabella completa sotto. Se omesso vengono eseguiti tutti in sequenza.
- **--workers**: per scenari concorrenti (es. `tx-contention`).
- **--granular**: stampa statistiche di latenza per singola operazione dove applicabile.
- **--json**: oltre al riepilogo, emette un report JSON con statistiche complete.
- Usa `--help` per un riepilogo degli argomenti.

### Scenari disponibili (temi)
| Scenario | Tema | Descrizione breve |
| --- | --- | --- |
| `heap-insert` | Heap | Inserimento massivo in tabella in-memory |
| `heap-scan` | Heap | Scan completo dopo popolamento tabella |
| `heap-delete` | Heap | Delete per chiave dopo popolamento |
| `heap-read-rid` | Heap | Letture puntuali via RID |
| `fileheap-insert-wal-off` | File/WAL | Insert su heap file senza WAL |
| `fileheap-insert-wal-fsync` | File/WAL | Insert con WAL e fsync pieno |
| `wal-append-none/lzfse/zlib` | WAL | Append micro (algoritmo compressione) |
| `btree-lookup` | B+Tree | Lookup puntuali su indice persistente |
| `btree-insert` | B+Tree | Insert incrementale con indice presente |
| `btree-range` | B+Tree | Range scan [lo,hi] su indice persistente |
| `btree-bulk-build` | B+Tree | Rebuild bulk da table scan |
| `idx-hash/art/art-range/skiplist/skiplist-range/fractal/fractal-range/btree/btree-range/lsm/lsm-range` | Indici in‑memory | Lookup e range per tutti i backend supportati |
| `tx-commit/tx-rollback` | Transazioni | Begin/commit/rollback ripetuti |
| `tx-contention` | Transazioni | Throughput in contesa (`--workers`) |
| `mvcc-snapshot-read` | MVCC | Scan snapshot mentre un writer modifica |
| `planner-join` | Planner | Query con filtro + join + ORDER BY |
| `planner-index-scan` | Planner | Accesso via indice con predicate |
| `planner-sort-limit` | Planner | Sort + limit con parallelismo |
| `checkpoint` | Manutenzione | Durata checkpoint su dati on‑disk |
| `vacuum-compact` | Manutenzione | Compattazione pagine heap |

Ogni run stampa per scenario: numero di iterazioni, tempo totale in millisecondi e throughput (operazioni/s). Con `--granular` vengono riportate anche statistiche di latenza (media, p50, p90, p95, p99, min, max, stddev) e metadati utili. Con `--json` il report viene emesso in formato JSON per la CI.

Esempi:
Esempi:
```
# Tutti gli scenari con 5k iterazioni
.build/release/benchmarks 5000

# Solo rebuild bulk B+Tree
.build/release/benchmarks 5000 btree-bulk-build

# Contesa transazionale con 8 worker in output JSON
.build/release/benchmarks 20000 tx-contention --workers=8 --granular --json
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

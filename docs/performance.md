# Performance Planning & Profiling

Questa nota raccoglie le attività consigliate per fissare baseline prestazionali e diagnosticarne eventuali regressioni su ColibrìDB, in particolare su hardware Apple Silicon.

## Baseline iniziali
1. **Seleziona un profilo hardware** (ad esempio, MacBook Pro M3 Pro 12c). Documenta frequenze, memoria e versione macOS.
2. **Costruisci il motore in Release**:
   ```
   swift build -c release --product coldb
   swift build -c release --product benchmarks
   ```
3. **Esegui i benchmark micro** (`benchmarks`) con iterazioni multiple (es. 10k) registrando media e deviazione standard:
   ```
   .build/release/benchmarks 10000
   ```
4. **Esegui un carico macro** (script CLI o workload sintetico) con mix read/write. Misura throughput (righe/s) e latenza (ms) con `time` o strumenti esterni.
5. **Registra le metriche** (buffer pool hit ratio, WAL LSN, vacuum) via CLI (`\bp`, `\stats`, `\vacuum stats`).

## Profiling Apple Silicon
- **Time Profiler** (Instruments) — individua hot path CPU.
- **System Trace** — correlazione tra thread e lock manager, scheduling P/E core.
- **os_signpost** — flush (`HeapFlush`, `IndexFlush`, `DBFlushAll`), vacuum (`VacuumTick`, `VacuumTable`, `VacuumIndexCompact`) e planner (`PlannerPlan`) emettono signpost standard; analizzali con Instruments → Logging → Points of Interest.
- **fs_usage** / **iostat** — analizza pattern I/O durante benchmark WAL/indice.

### Hint I/O
- Abilitare `ioSequentialReadHint` in config per applicare `F_RDAHEAD`, `posix_fadvise` e `preadv`/`preadv2` su scan heap, replay WAL (dati + indici) e rebuild B+Tree.
- Con `walFullFSyncEnabled` attivo anche i WAL degli indici usano `F_FULLFSYNC`; i comandi `\flush ... fullsync` richiedono la sync hardware sulle heap/indici su macOS.
- `walCompression` riduce il footprint del log (LZFSE/Zlib). Nei workload write-heavy confronta throughput e tempo CPU per assicurarti che il guadagno I/O compensi la compressione.
- `pageFlushCompression` genera snapshot compressi delle heap dopo ogni `flush`; utile per backup incrementali o seed di ambienti CI, sconsigliato nei test di latenza pura.

## Parametri chiave da monitorare
| Componente | Parametro | Come misurare |
| --- | --- | --- |
| Heap | Inserimenti/s, bytes/page | `benchmarks heap-insert`, `\table compact` metriche |
| B+Tree | Lookup/s, profondità media | `benchmarks btree-lookup`, `FileBPlusTreeIndex.validateDeep()` |
| WAL | Append/s, dimensione log | Profilo `FileWAL`, `ls -lh data/wal.log` |
| Buffer pool | Hit/miss ratio, evictions | CLI `\bp`, `BufferNamespaceManager` stats |
| Planner | Tempo di pianificazione, righe restituite | `benchmarks planner-join`, log `ExecutionContext` |

## Gestione regression
1. **Baseline**: archivia risultati `benchmarks` (es. CSV) e output CLI.
2. **Nuova feature**: riesegui i benchmark a parità di iterazioni e confronta.
3. **Scostamento >5%**: attiva Time Profiler e System Trace, verifica contese (`LockManager`), controlla WAL e flush condizionali.
4. **Documenta** i cambi in `docs/performance.md` o issue GitHub per tracciabilità.

## Spunti di ottimizzazione futura
- Evitare allocazioni in hot path (riusare `PlanRow`/buffer).
- Introdurre `@inlinable` e specializzazione su predicate branchless.
- Portare `ParallelMapOperator` su task group/actor per ridurre warning e migliorare bilanciamento.
- Introdurre histogram/feedback loop nel cost-model per stimare meglio join su dataset sbilanciati.
- Implementare WAL async batching per ridurre fsync a flush coalescenti.

Per ogni ottimizzazione misurare **prima e dopo** con `benchmarks` e almeno uno scenario macro. Integrare le misure principali nei report di release.

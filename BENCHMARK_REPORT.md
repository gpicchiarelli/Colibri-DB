# Benchmark Report - 2025-10-17

## Sommario

I benchmark di Colibrì-DB sono stati sistemati e verificati. La maggior parte funziona correttamente, con un problema critico identificato negli indici B+Tree su FileHeap.

## Correzioni Applicate

### 1. Errori di Compilazione
- **Problema**: Uso errato di `BenchmarkResult` invece di `InternalBenchmarkResult` in tutti i file di estensione
- **Soluzione**: Sostituito tutti i riferimenti con il tipo corretto
- **File corretti**: `Benchmarks+*.swift` (tutti i file di estensione)

### 2. API Calls Errate
- **Problema**: Uso di `insert(table:row:tid:)` invece di `insert(into:row:tid:)`
- **Soluzione**: Corretto tutti i riferimenti API
- **File corretti**: `CompleteBenchmarkSuite.swift`

### 3. Istogramma Per Valori Piccoli
- **Problema**: L'istogramma mostrava `[0.0,0.0)` per latenze in microsecondi
- **Soluzione**: Modificata la logica per usare scala lineare con più decimali per valori < 1.0ms
- **File corretto**: `Benchmarks.swift` (funzione `generateHistogram`)
- **Risultato**: Ora mostra valori leggibili come `[0.0048,0.0180)` invece di `[0.0,0.0)`

## Benchmark Verificati

### ✅ Funzionanti Correttamente

1. **heap-insert** (100 iterazioni)
   - Throughput: ~125k ops/sec
   - Latenza media: 0.007ms, p99: 0.078ms
   - Storage: InMemory

2. **heap-scan** (100 iterazioni)
   - Latenza: 0.37ms per scan completa
   - Storage: InMemory

3. **tx-commit** (50 iterazioni)
   - Throughput: ~3.5k-4k tx/sec
   - Latenza media: 0.25ms, p99: 0.33ms
   - Storage: FileHeap + WAL

4. **wal-append-none** (50 iterazioni)
   - Funziona correttamente
   - Compressione: none

5. **idx-hash-lookup** (100 iterazioni)
   - Throughput: ~145k lookups/sec
   - Latenza media: 0.006ms
   - Storage: InMemory, Index: Hash

6. **idx-skiplist-lookup** (50 iterazioni)
   - Latenza media: 0.009ms, p99: 0.010ms
   - Distribuzione eccellente delle latenze
   - Storage: InMemory, Index: SkipList

7. **planner-join** (20 richieste → 1 esecuzione)
   - Funziona correttamente
   - Join tra tabelle users e orders

### ❌ Problema Critico Identificato

**btree-lookup** (500 iterazioni)
- **Problema**: L'indice B+Tree persistente non viene popolato correttamente su FileHeap
- **Sintomi**: 
  - La maggior parte delle lookup falliscono
  - Warning: "Index lookup failed for key X, using scan fallback"
  - Throughput degradato: ~447 ops/sec invece dei previsti >100k ops/sec
- **Causa Probabile**: 
  - Il metodo `rebuildIndexBulk()` viene chiamato correttamente
  - Il metodo `updateIndexes()` inserisce i dati nell'indice durante gli inserimenti
  - Il metodo `flushAll()` viene chiamato per persistere i dati
  - Tuttavia, le lookup successive non trovano i dati nell'indice
  - Possibile problema di sincronizzazione o persistenza nell'indice B+Tree su disco
- **Workaround**: Gli indici B+Tree in-memory (AnyString) funzionano perfettamente
- **Impatto**: Alto - gli indici B+Tree sono fondamentali per le performance
- **Raccomandazione**: Investigazione approfondita del modulo `FileBPlusTreeIndex`

## Dettagli Tecnici

### Modalità di Esecuzione

I benchmark supportano due modalità:

1. **Non-granulare** (default): 
   - Misura il tempo totale e calcola la latenza media
   - Più veloce ma meno dettagliato
   - Esempio: `benchmarks 1000 heap-insert`

2. **Granulare** (`--granular`):
   - Misura la latenza di ogni singola operazione
   - Fornisce statistiche dettagliate (p50, p90, p95, p99, p999)
   - Genera istogramma di distribuzione
   - Esempio: `benchmarks 1000 heap-insert --granular`

### Altre Opzioni

- `--json`: Output in formato JSON
- `--csv`: Output in formato CSV
- `--sysmetrics`: Raccoglie metriche di sistema (CPU, memoria, I/O)
- `--no-warmup`: Disabilita il warm-up pre-benchmark
- `--seed=N`: Imposta seed per riproducibilità
- `--out=file`: Scrive output su file
- `--workers=N`: Numero di worker per benchmark concorrenti

## Prossimi Passi

1. **Priorità Alta**: Investigare e correggere il problema con gli indici B+Tree su FileHeap
   - Verificare la persistenza dei dati nell'indice
   - Controllare la sincronizzazione tra scritture e letture
   - Testare il metodo `rebuildIndexBulk()` in isolamento

2. **Miglioramenti Futuri**:
   - Aggiungere più test di integrazione per indici persistenti
   - Implementare benchmark specifici per testare la persistenza degli indici
   - Documentare meglio le differenze tra modalità granulare e non-granulare

3. **Monitoraggio**:
   - Eseguire periodicamente la suite completa di benchmark
   - Tracciare regressioni di performance
   - Mantenere baseline di performance aggiornate

## Conclusioni

I benchmark sono ora funzionanti e forniscono metriche accurate per la maggior parte delle operazioni. Il problema critico con gli indici B+Tree su FileHeap richiede attenzione immediata, ma non impedisce il testing delle altre funzionalità del database.


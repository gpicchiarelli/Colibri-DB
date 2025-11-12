# 🏗️ ColibrDB Developer Guide

Questa guida fornisce informazioni dettagliate per sviluppatori che vogliono contribuire al core di ColibrDB.

## 📋 Indice
- [Architettura Generale](#architettura-generale)
- [Moduli Core](#moduli-core)
- [Convenzioni di Sviluppo](#convenzioni-di-sviluppo)
- [Pattern Architetturali](#pattern-architetturali)
- [Gestione della Concorrenza](#gestione-della-concorrenza)
- [Performance e Ottimizzazione](#performance-e-ottimizzazione)
- [Debugging e Troubleshooting](#debugging-e-troubleshooting)

## 🏗️ Architettura Generale

### Principi Fondamentali
ColibrDB è progettato seguendo questi principi:

1. **Performance First**: Ogni componente è ottimizzato per velocità e throughput
2. **Modularità**: Architettura pluggabile per indici e storage
3. **Concorrenza**: Supporto multi-threading con MVCC
4. **Durabilità**: WAL e recovery ARIES-compliant
5. **Scalabilità**: Progettato per milioni di connessioni logiche

### Diagramma Architetturale
```
┌─────────────────────────────────────────────────────────────┐
│                    ColibrDB Architecture                    │
├─────────────────────────────────────────────────────────────┤
│  CLI (coldb)  │  Server (coldb-server)  │  Benchmarks      │
├─────────────────────────────────────────────────────────────┤
│                    ColibriCore                              │
│  ┌─────────────┬─────────────┬─────────────┬─────────────┐  │
│  │   Catalog   │  Database   │   Planner   │  Functions  │  │
│  └─────────────┴─────────────┴─────────────┴─────────────┘  │
│  ┌─────────────┬─────────────┬─────────────┬─────────────┐  │
│  │   Storage   │     WAL     │   Buffer    │   Index     │  │
│  └─────────────┴─────────────┴─────────────┴─────────────┘  │
│  ┌─────────────┬─────────────┬─────────────┬─────────────┐  │
│  │   MVCC      │    Lock     │  Checkpoint │  Recovery   │  │
│  └─────────────┴─────────────┴─────────────┴─────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

## 🔧 Moduli Core

### 1. Storage Engine (`Sources/ColibriCore/Storage/`)
**Responsabilità**: Gestione persistenza dati su disco

#### Componenti Principali
- **HeapTable**: Gestione tabelle in memoria
- **FileHeapTable**: Gestione tabelle su disco
- **Page**: Gestione pagine con slot directory
- **FreeSpaceMap**: Mappa spazi liberi persistente

#### Pattern Architetturali
```swift
// Esempio di implementazione Page
public struct Page {
    public let pageID: PageID
    public var pageLSN: UInt64
    public var slotDirectory: SlotDirectory
    public var data: Data
    
    // Thread-safe access
    private let lock = NSLock()
    
    public mutating func updateSlot(at index: Int, with data: Data) {
        lock.lock()
        defer { lock.unlock() }
        // Implementazione thread-safe
    }
}
```

#### Convenzioni
- Ogni pagina ha un `PageLSN` per recovery
- Slot directory per gestione efficiente dei record
- Free Space Map per allocazione ottimale
- Supporto per compattazione online

### 2. Write-Ahead Logging (`Sources/ColibriCore/WAL/`)
**Responsabilità**: Durabilità e recovery ARIES-compliant

#### Componenti Principali
- **FileWALManager**: Gestione file WAL
- **WALRecord**: Record tipizzati con checksum
- **CheckpointManager**: Gestione checkpoint
- **RecoveryManager**: Recovery ARIES-compliant

#### Pattern Architetturali
```swift
// Esempio di WAL Record
public struct WALRecord {
    public let lsn: UInt64
    public let transactionID: UInt64
    public let type: WALRecordType
    public let data: Data
    public let checksum: UInt32
    
    // Thread-safe logging
    public static func log(_ record: WALRecord, to manager: FileWALManager) async throws {
        // Implementazione con group commit
    }
}
```

#### Convenzioni
- LSN monotonicamente crescente
- Checksum CRC32 per integrità
- Group commit per performance
- Recovery ARIES-compliant

### 3. Buffer Pool (`Sources/ColibriCore/Buffer/`)
**Responsabilità**: Caching intelligente delle pagine

#### Componenti Principali
- **BufferPool**: Gestione cache LRU/Clock
- **BufferFrame**: Frame con pin/unpin
- **Flusher**: Flush in background
- **EvictionPolicy**: Politiche di eviction

#### Pattern Architetturali
```swift
// Esempio di Buffer Pool
public final class BufferPool {
    private let frames: [BufferFrame]
    private let evictionPolicy: EvictionPolicy
    private let flusher: BackgroundFlusher
    
    public func pinPage(_ pageID: PageID) -> BufferFrame? {
        // Implementazione con eviction LRU/Clock
    }
    
    public func unpinPage(_ pageID: PageID, dirty: Bool) {
        // Gestione dirty tracking
    }
}
```

#### Convenzioni
- Eviction LRU/Clock per performance
- Dirty tracking per WAL
- Flush in background per latenza
- Quote per namespace

### 4. Index Engine (`Sources/ColibriCore/Index/`)
**Responsabilità**: Indicizzazione pluggabile

#### Componenti Principali
- **BPlusTreeIndex**: Indice B+Tree persistente
- **HashIndex**: Indice hash
- **ARTIndex**: Adaptive Radix Tree
- **LSMIndex**: Log-Structured Merge Tree

#### Pattern Architetturali
```swift
// Esempio di Index Interface
public protocol Index {
    func insert(key: Value, value: Value) async throws
    func delete(key: Value) async throws
    func search(key: Value) async throws -> [Value]
    func rangeSearch(from: Value, to: Value) async throws -> [Value]
}
```

#### Convenzioni
- Interfaccia pluggabile
- Supporto per operazioni bulk
- Recovery da WAL
- Validazione integrità

### 5. MVCC (`Sources/ColibriCore/Transactions/`)
**Responsabilità**: Controllo concorrenza multi-versione

#### Componenti Principali
- **MVCCManager**: Gestione versioni
- **TransactionManager**: Gestione transazioni
- **LockManager**: Gestione lock
- **IsolationLevel**: Livelli di isolamento

#### Pattern Architetturali
```swift
// Esempio di MVCC
public final class MVCCManager {
    private let versionStore: VersionStore
    private let transactionManager: TransactionManager
    
    public func readValue(key: Value, at timestamp: UInt64) -> Value? {
        // Implementazione snapshot isolation
    }
    
    public func writeValue(key: Value, value: Value, transactionID: UInt64) {
        // Implementazione write-ahead
    }
}
```

#### Convenzioni
- Snapshot isolation per letture
- Write-ahead per scritture
- Deadlock detection
- Timeout configurabili

## 📝 Convenzioni di Sviluppo

### Struttura File
```swift
//
//  NomeFile.swift
//  ColibrDB
//
//  Created by [Nome] on [Data].
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: [Descrizione breve del modulo]

import Foundation

/// Descrizione della classe/funzione
public final class NomeClasse {
    // MARK: - Properties
    
    /// Descrizione della proprietà
    public let proprieta: Tipo
    
    // MARK: - Initialization
    
    /// Inizializzatore
    public init(proprieta: Tipo) {
        self.proprieta = proprieta
    }
    
    // MARK: - Public Methods
    
    /// Descrizione del metodo
    public func metodo() {
        // Implementazione
    }
}
```

### Naming Conventions
- **Classi**: PascalCase (`BufferPool`, `WALManager`)
- **Funzioni**: camelCase (`pinPage`, `flushToDisk`)
- **Variabili**: camelCase (`pageID`, `transactionID`)
- **Costanti**: camelCase (`maxPageSize`, `defaultBufferSize`)
- **Enum**: PascalCase (`WALRecordType`, `IsolationLevel`)

### Error Handling
```swift
// Usa Result per operazioni che possono fallire
public func readPage(_ pageID: PageID) -> Result<Page, StorageError> {
    // Implementazione
}

// Usa throws per operazioni async
public func writePage(_ page: Page) async throws {
    // Implementazione
}
```

## 🔄 Pattern Architetturali

### 1. Iterator Pattern
Per l'elaborazione query:
```swift
public protocol Iterator {
    func next() -> Row?
    func close()
}

public struct ScanIterator: Iterator {
    // Implementazione scan
}
```

### 2. Strategy Pattern
Per indici pluggabili:
```swift
public protocol IndexStrategy {
    func insert(key: Value, value: Value) async throws
    func search(key: Value) async throws -> [Value]
}
```

### 3. Observer Pattern
Per notifiche di eventi:
```swift
public protocol WALObserver {
    func onWALFlush(lsn: UInt64)
    func onCheckpoint(lsn: UInt64)
}
```

### 4. Factory Pattern
Per creazione componenti:
```swift
public struct IndexFactory {
    public static func createIndex(type: IndexType) -> Index {
        switch type {
        case .bTree: return BPlusTreeIndex()
        case .hash: return HashIndex()
        case .art: return ARTIndex()
        }
    }
}
```

## 🧵 Gestione della Concorrenza

### Thread Safety
- **NSLock**: Per sezioni critiche brevi
- **NSRecursiveLock**: Per lock annidati
- **DispatchQueue**: Per operazioni asincrone
- **Actor**: Per stato condiviso (Swift 6.0)

### Esempio di Thread Safety
```swift
public final class ThreadSafeCounter {
    private var _value: Int = 0
    private let lock = NSLock()
    
    public var value: Int {
        lock.lock()
        defer { lock.unlock() }
        return _value
    }
    
    public func increment() {
        lock.lock()
        defer { lock.unlock() }
        _value += 1
    }
}
```

### MVCC Implementation
```swift
public final class MVCCManager {
    private let versionStore = VersionStore()
    private let transactionManager = TransactionManager()
    
    public func read(key: Value, transactionID: UInt64) -> Value? {
        let snapshot = transactionManager.getSnapshot(transactionID)
        return versionStore.read(key: key, at: snapshot)
    }
    
    public func write(key: Value, value: Value, transactionID: UInt64) {
        let version = Version(key: key, value: value, transactionID: transactionID)
        versionStore.write(version)
    }
}
```

## ⚡ Performance e Ottimizzazione

### Principi di Ottimizzazione
1. **Cache Locality**: Strutture dati compatte
2. **Branchless Code**: Evitare branch prediction
3. **SIMD**: Utilizzare NEON su ARM64
4. **Lock-Free**: Strutture dati lock-free quando possibile
5. **Batching**: Operazioni in batch per throughput

### Esempio di Ottimizzazione
```swift
// Ottimizzazione per cache locality
public struct CompactRow {
    private let data: UnsafeMutablePointer<UInt8>
    private let offsets: [UInt16]
    
    public func getValue(at index: Int) -> Value {
        let offset = Int(offsets[index])
        return Value(data: Data(bytes: data + offset, count: 4))
    }
}
```

### Benchmarking
```swift
// Esempio di benchmark
@main
struct PerformanceBenchmark {
    static func main() async {
        let benchmark = WALThroughputBenchmark()
        let result = await benchmark.run(duration: 30)
        print("WAL Throughput: \(result.operationsPerSecond) ops/sec")
    }
}
```

## 🐛 Debugging e Troubleshooting

### Logging
```swift
// Sistema di logging centralizzato
public enum LogLevel {
    case debug, info, warning, error
}

public struct Logger {
    public static func log(_ level: LogLevel, _ message: String, file: String = #file, line: Int = #line) {
        // Implementazione logging
    }
}
```

### Debug Tools
```bash
# Debug con verbose logging
swift run coldb --verbose

# Debug WAL
swift run coldb-dev --wal-debug

# Debug buffer pool
swift run coldb-dev --buffer-debug

# Debug MVCC
swift run coldb-dev --mvcc-debug
```

### Profiling
```bash
# Profiling con Instruments
swift run benchmarks --profile

# Memory profiling
swift run benchmarks --memory-profile

# CPU profiling
swift run benchmarks --cpu-profile
```

## 📊 Metriche e Monitoring

### Metriche Chiave
- **WAL Throughput**: Operazioni WAL per secondo
- **Buffer Hit Rate**: Percentuale hit nel buffer pool
- **Transaction Throughput**: Transazioni per secondo
- **Index Performance**: Lookup per secondo
- **Memory Usage**: Utilizzo memoria

### Esempio di Metriche
```swift
public struct PerformanceMetrics {
    public var walThroughput: Double = 0
    public var bufferHitRate: Double = 0
    public var transactionThroughput: Double = 0
    public var memoryUsage: UInt64 = 0
    
    public func export() -> [String: Any] {
        return [
            "wal_throughput": walThroughput,
            "buffer_hit_rate": bufferHitRate,
            "transaction_throughput": transactionThroughput,
            "memory_usage": memoryUsage
        ]
    }
}
```

## 🔧 Strumenti di Sviluppo

### CLI di Sviluppo
```bash
# Avvia CLI di sviluppo
swift run coldb-dev

# Comandi disponibili
swift run coldb-dev --help

# Debug specifico
swift run coldb-dev --debug-wal
swift run coldb-dev --debug-buffer
swift run coldb-dev --debug-mvcc
```

### Testing
```bash
# Test specifici
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Test con coverage
swift test --enable-code-coverage

# Test di performance
swift run benchmarks
```

### Build e Deployment
```bash
# Build release
swift build -c release

# Test su diverse configurazioni
swift test --configuration debug
swift test --configuration release
```

---

Questa guida fornisce le basi per contribuire efficacemente al core di ColibrDB. Per domande specifiche, consulta la documentazione tecnica in `docs/` o apri una discussione su GitHub.

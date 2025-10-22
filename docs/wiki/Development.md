---
layout: doc
title: Guida per Sviluppatori
description: Guida completa per contribuire allo sviluppo di Colibrì DB
---

# 🛠️ Guida per Sviluppatori

Guida completa per contribuire allo sviluppo di Colibrì DB.

## 🎯 Panoramica

Colibrì DB è un progetto open source che accoglie contributi da sviluppatori di tutti i livelli. Questa guida ti aiuterà a:

- Configurare l'ambiente di sviluppo
- Comprendere l'architettura del codice
- Contribuire con bug fix e nuove funzionalità
- Seguire le best practices del progetto

## 🚀 Setup Ambiente di Sviluppo

### Prerequisiti

- **macOS 13.0+** (Ventura o superiore)
- **Xcode 15.0+** con Command Line Tools
- **Swift 6.2+**
- **Git** per version control
- **Docker** (opzionale, per testing)

### 1. Fork e Clone

```bash
# Fork del repository su GitHub, poi clona
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB

# Aggiungi il repository upstream
git remote add upstream https://github.com/gpicchiarelli/Colibri-DB.git
```

### 2. Configurazione Xcode

```bash
# Genera il progetto Xcode
swift package generate-xcodeproj

# Apri in Xcode
open ColibriDB.xcodeproj
```

### 3. Verifica Setup

```bash
# Compila il progetto
swift build

# Esegui i test
swift test

# Esegui i benchmark
swift run benchmarks --help
```

## 🏗️ Architettura del Codice

### Struttura del Repository

```
Colibri-DB/
├── Sources/
│   ├── ColibriCore/          # Motore database core
│   │   ├── Buffer/           # Gestione buffer pool
│   │   ├── Catalog/          # Catalogo di sistema
│   │   ├── Database/         # Operazioni database
│   │   ├── Index/            # Implementazioni indici
│   │   ├── Storage/          # Motore storage
│   │   ├── Transactions/     # MVCC e locking
│   │   ├── WAL/              # Write-Ahead Logging
│   │   ├── SQL/              # Parser e query interface
│   │   ├── Planner/          # Query planning
│   │   └── Util/             # Utility e helper
│   ├── coldb/                # CLI amministrativa
│   ├── coldb-server/         # Server di rete
│   └── benchmarks/           # Test di performance
├── Tests/                    # Suite di test
├── docs/                     # Documentazione tecnica
└── Examples/                 # Esempi di utilizzo
```

### Principi Architetturali

1. **Modularità**: Ogni componente ha responsabilità ben definite
2. **Protocol-First**: Uso estensivo di protocolli per testabilità
3. **Error Handling**: Gestione errori tipizzata e robusta
4. **Performance**: Ottimizzazioni per Apple Silicon
5. **Testabilità**: Design che facilita testing unitario e integrazione

## 🔧 Strumenti di Sviluppo

### Swift Testing

Colibrì DB utilizza il framework Swift Testing moderno:

```swift
import Testing

@Test func testDatabaseCreation() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("test_table")
    #expect(database.listTables().contains("test_table"))
}
```

### Benchmarking

```swift
import Benchmark

let benchmarks = BenchmarkSuite("Database Operations") { suite in
    suite.benchmark("Insert Performance") {
        // Benchmark insert operations
    }
    
    suite.benchmark("Query Performance") {
        // Benchmark query operations
    }
}
```

### Code Coverage

```bash
# Esegui test con coverage
swift test --enable-code-coverage

# Genera report coverage
xcrun llvm-cov show .build/debug/ColibriCorePackageTests.xctest/Contents/MacOS/ColibriCorePackageTests -instr-profile .build/debug/codecov/default.profdata
```

## 📝 Convenzioni di Codice

### Naming Conventions

```swift
// Classi: PascalCase
public class Database { }

// Funzioni e variabili: camelCase
public func createTable(_ name: String) throws { }

// Costanti: camelCase
public let defaultPageSize = 8192

// Protocolli: PascalCase + "Protocol"
public protocol StorageEngineProtocol { }

// Enums: PascalCase
public enum IsolationLevel { }
```

### Documentazione

```swift
/// Crea una nuova tabella nel database.
///
/// - Parameter name: Nome della tabella da creare
/// - Throws: `DBError.alreadyExists` se la tabella esiste già
/// - Throws: `DBError.ioError` se si verifica un errore I/O
///
/// - Note: La tabella viene creata con schema flessibile
/// - SeeAlso: `dropTable(_:)` per eliminare una tabella
public func createTable(_ name: String) throws {
    // Implementation
}
```

### Error Handling

```swift
// Usa errori tipizzati
public enum DBError: Error, CustomStringConvertible {
    case notFound(String)
    case alreadyExists(String)
    case constraintViolation(String)
    
    public var description: String {
        switch self {
        case .notFound(let message):
            return "Not found: \(message)"
        case .alreadyExists(let message):
            return "Already exists: \(message)"
        case .constraintViolation(let message):
            return "Constraint violation: \(message)"
        }
    }
}

// Propagazione errori
public func createTable(_ name: String) throws {
    guard !tables.contains(name) else {
        throw DBError.alreadyExists("Table '\(name)' already exists")
    }
    // Implementation
}
```

## 🧪 Testing

### Unit Tests

```swift
import Testing
import ColibriCore

@Test func testTableCreation() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    // Test creazione tabella
    try database.createTable("users")
    #expect(database.listTables().contains("users"))
    
    // Test creazione tabella duplicata
    #expect(throws: DBError.alreadyExists.self) {
        try database.createTable("users")
    }
}

@Test func testDataInsertion() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("users")
    
    let row = Row([
        "id": .int(1),
        "name": .string("Alice"),
        "age": .int(25)
    ])
    
    let rid = try database.insert("users", row: row)
    #expect(rid.pageId > 0)
    #expect(rid.slotId >= 0)
}
```

### Integration Tests

```swift
@Test func testTransactionWorkflow() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("users")
    
    // Test transazione completa
    let tid = try database.begin()
    
    do {
        let row1 = Row(["id": .int(1), "name": .string("Alice")])
        let row2 = Row(["id": .int(2), "name": .string("Bob")])
        
        try database.insert("users", row: row1)
        try database.insert("users", row: row2)
        
        try database.commit(tid)
        
        // Verifica che i dati siano stati committati
        let rows = try database.select("users", predicate: nil)
        #expect(rows.count == 2)
        
    } catch {
        try database.rollback(toSavepoint: "", tid: tid)
        throw error
    }
}
```

### Performance Tests

```swift
@Test func testInsertPerformance() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("perf_test")
    
    let startTime = Date()
    
    for i in 0..<10000 {
        let row = Row([
            "id": .int(Int64(i)),
            "data": .string("Test data \(i)")
        ])
        try database.insert("perf_test", row: row)
    }
    
    let endTime = Date()
    let duration = endTime.timeIntervalSince(startTime)
    
    #expect(duration < 1.0) // Dovrebbe completare in meno di 1 secondo
}
```

## 🔄 Workflow di Sviluppo

### 1. Creazione Branch

```bash
# Aggiorna main
git checkout main
git pull upstream main

# Crea branch per feature
git checkout -b feature/new-index-type

# Crea branch per bug fix
git checkout -b fix/memory-leak
```

### 2. Sviluppo

```bash
# Fai commit frequenti con messaggi chiari
git add Sources/ColibriCore/Index/NewIndexType.swift
git commit -m "feat: add LSM index implementation

- Implement LSM tree structure
- Add merge operations
- Add compaction logic
- Add unit tests

Closes #123"
```

### 3. Testing Locale

```bash
# Esegui tutti i test
swift test

# Esegui test specifici
swift test --filter LSMIndex

# Esegui benchmark
swift run benchmarks --lsm-performance

# Verifica linting
swift package resolve
```

### 4. Pull Request

```bash
# Push del branch
git push origin feature/new-index-type

# Crea PR su GitHub
# - Titolo chiaro e descrittivo
# - Descrizione dettagliata delle modifiche
# - Riferimento alle issue correlate
# - Screenshot se applicabile
```

## 📋 Checklist per Contributi

### Prima di Inviare PR

- [ ] Codice compila senza errori
- [ ] Tutti i test passano
- [ ] Nuovo codice ha test unitari
- [ ] Documentazione aggiornata
- [ ] Codice segue le convenzioni del progetto
- [ ] Commit messages seguono Conventional Commits
- [ ] PR ha titolo e descrizione chiari

### Per Bug Fix

- [ ] Bug riproducibile con test
- [ ] Fix minimale e mirato
- [ ] Test di regressione aggiunto
- [ ] Documentazione aggiornata se necessario

### Per Nuove Funzionalità

- [ ] Feature ben progettata e documentata
- [ ] Test unitari e integrazione
- [ ] Performance accettabili
- [ ] Compatibilità backward mantenuta
- [ ] Documentazione utente aggiornata

## 🐛 Debugging

### Strumenti di Debug

```swift
// Logging dettagliato
import os.log

private let logger = Logger(subsystem: "ColibriDB", category: "Database")

func createTable(_ name: String) throws {
    logger.debug("Creating table: \(name)")
    
    // Implementation
    
    logger.info("Table created successfully: \(name)")
}
```

### Profiling

```bash
# Profiling con Instruments
xcodebuild -scheme ColibriDB -configuration Release
instruments -t "Time Profiler" .build/release/coldb

# Memory profiling
instruments -t "Allocations" .build/release/coldb
```

### Debugging WAL

```swift
// Abilita debug WAL
let config = DBConfig(
    walEnabled: true,
    walDebugMode: true,
    walLogLevel: .debug
)
```

## 📊 Performance Optimization

### Apple Silicon Optimizations

```swift
// Utilizza SIMD per operazioni vettoriali
import Accelerate

func processBatch(_ data: [Double]) -> [Double] {
    var result = [Double](repeating: 0, count: data.count)
    
    vDSP_vaddD(data, 1, data, 1, &result, 1, vDSP_Length(data.count))
    
    return result
}
```

### Memory Management

```swift
// Usa autoreleasepool per operazioni batch
func processLargeDataset(_ items: [Item]) throws {
    try items.chunked(into: 1000).forEach { chunk in
        try autoreleasepool {
            for item in chunk {
                try processItem(item)
            }
        }
    }
}
```

### Concurrency

```swift
// Usa async/await per operazioni I/O
func loadData() async throws -> [Data] {
    return try await withThrowingTaskGroup(of: Data.self) { group in
        for url in urls {
            group.addTask {
                try await loadData(from: url)
            }
        }
        
        var results: [Data] = []
        for try await data in group {
            results.append(data)
        }
        return results
    }
}
```

## 🔍 Code Review

### Cosa Cercare

1. **Correttezza**: Il codice fa quello che dovrebbe?
2. **Performance**: Ci sono ottimizzazioni possibili?
3. **Sicurezza**: Ci sono vulnerabilità di sicurezza?
4. **Manutenibilità**: Il codice è leggibile e ben strutturato?
5. **Test**: I test coprono tutti i casi d'uso?

### Commenti Costruttivi

```markdown
// ❌ Non costruttivo
This is wrong.

// ✅ Costruttivo
This approach might cause a memory leak. Consider using `weak` references or ensuring proper cleanup in the deinitializer.
```

## 📚 Risorse Utili

### Documentazione

- [Swift Documentation](https://docs.swift.org/swift-book/)
- [Swift Testing](https://swiftpackageindex.com/apple/swift-testing)
- [Swift NIO](https://github.com/apple/swift-nio)
- [Database Systems Concepts](https://www.db-book.com/)

### Strumenti

- [SwiftLint](https://github.com/realm/SwiftLint) - Linting
- [SwiftFormat](https://github.com/nicklockwood/SwiftFormat) - Code formatting
- [Instruments](https://developer.apple.com/documentation/xcode/instruments) - Profiling
- [GitHub CLI](https://cli.github.com/) - Gestione PR

### Community

- [Swift Forums](https://forums.swift.org/)
- [GitHub Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- [Discord Server](https://discord.gg/colibridb) (se disponibile)

## 🚀 Prossimi Passi

### Per Nuovi Contributori

1. **Leggi la documentazione**: Inizia con [Quick Start](Quick-Start.md) e [Architecture](Architecture.md)
2. **Esplora il codice**: Guarda i file in `Sources/ColibriCore/`
3. **Risolvi issue semplici**: Cerca label "good first issue"
4. **Partecipa alle discussioni**: Unisciti alle conversazioni su GitHub

### Per Sviluppatori Esperti

1. **Contribuisci a funzionalità avanzate**: Storage engine, query optimizer
2. **Migliora le performance**: Ottimizzazioni Apple Silicon
3. **Aggiungi test**: Copertura test, benchmark
4. **Mentoring**: Aiuta nuovi contributori

---

<div align="center">

**🛠️ Development Guide Colibrì DB** - *Contribuisci al futuro dei database Swift*

[← API Reference](API-Reference.md) • [Troubleshooting →](Troubleshooting.md)

</div>

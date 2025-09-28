# 🧪 ColibrDB Testing Guide

Questa guida fornisce informazioni complete sul sistema di testing di ColibrDB, inclusi test unitari, integration test, benchmark e best practices.

## 📋 Indice
- [Panoramica Testing](#panoramica-testing)
- [Framework di Testing](#framework-di-testing)
- [Tipi di Test](#tipi-di-test)
- [Esecuzione Test](#esecuzione-test)
- [Scrittura Test](#scrittura-test)
- [Benchmark e Performance](#benchmark-e-performance)
- [Continuous Integration](#continuous-integration)
- [Debugging Test](#debugging-test)
- [Best Practices](#best-practices)

## 🎯 Panoramica Testing

### Filosofia di Testing
ColibrDB adotta un approccio multi-livello per garantire qualità e performance:

1. **Unit Tests**: Test di singole funzioni e classi
2. **Integration Tests**: Test di workflow end-to-end
3. **Performance Tests**: Benchmark per rilevare regressioni
4. **Stress Tests**: Test con carico elevato
5. **Fault Injection**: Test di resilienza e recovery

### Copertura Target
- **Unit Tests**: >90% line coverage
- **Integration Tests**: >80% scenario coverage
- **Performance Tests**: Baseline per ogni componente
- **Stress Tests**: Validazione scenari ad alto carico

## 🔧 Framework di Testing

### Swift Testing (Primario)
Swift 6.2 introduce il nuovo framework di testing nativo:

```swift
import Testing

struct DatabaseTests {
    @Test func testDatabaseCreation() async throws {
        // Arrange
        let config = DBConfig.default
        
        // Act
        let database = try await Database.create(config: config)
        
        // Assert
        #expect(database != nil)
        #expect(database.config == config)
    }
}
```

### XCTest (Legacy)
Per compatibilità con tool esistenti:

```swift
import XCTest
@testable import ColibriCore

final class DatabaseXCTests: XCTestCase {
    func testDatabaseCreation() async throws {
        // Test implementation
    }
}
```

### Test Structure
```
Tests/
├── ColibriCoreTests/           # Test del core engine
│   ├── StorageTests/           # Test storage engine
│   ├── WALTests/               # Test Write-Ahead Logging
│   ├── BufferTests/            # Test buffer pool
│   ├── IndexTests/             # Test indici
│   ├── MVCCTests/              # Test MVCC
│   └── CatalogTests/           # Test catalogo
├── IntegrationTests/           # Test di integrazione
├── PerformanceTests/           # Test di performance
└── StressTests/                # Test di stress
```

## 🧪 Tipi di Test

### 1. Unit Tests
Test di singole funzioni e classi:

```swift
import Testing
@testable import ColibriCore

struct PageTests {
    @Test func testPageCreation() {
        // Arrange
        let pageID = PageID(1)
        let data = Data(repeating: 0, count: 8192)
        
        // Act
        let page = Page(pageID: pageID, data: data)
        
        // Assert
        #expect(page.pageID == pageID)
        #expect(page.data.count == 8192)
    }
    
    @Test func testSlotDirectory() {
        // Arrange
        var page = Page(pageID: PageID(1), data: Data(repeating: 0, count: 8192))
        
        // Act
        let slotID = page.allocateSlot(size: 100)
        
        // Assert
        #expect(slotID != nil)
        #expect(page.slotDirectory.count == 1)
    }
}
```

### 2. Integration Tests
Test di workflow end-to-end:

```swift
import Testing
@testable import ColibriCore

struct DatabaseIntegrationTests {
    @Test func testCompleteWorkflow() async throws {
        // Arrange
        let config = DBConfig.default
        let database = try await Database.create(config: config)
        
        // Act
        try await database.createTable("test_table", schema: [
            "id": .integer,
            "name": .string,
            "age": .integer
        ])
        
        try await database.insert("test_table", values: [
            "id": 1,
            "name": "Alice",
            "age": 25
        ])
        
        let result = try await database.select("test_table", where: ["id": 1])
        
        // Assert
        #expect(result.count == 1)
        #expect(result[0]["name"] == "Alice")
    }
}
```

### 3. Performance Tests
Benchmark per rilevare regressioni:

```swift
import Testing
@testable import ColibriCore

struct PerformanceTests {
    @Test func testWALThroughput() async throws {
        // Arrange
        let config = DBConfig.default
        let database = try await Database.create(config: config)
        let iterations = 10000
        
        // Act
        let startTime = Date()
        for i in 0..<iterations {
            try await database.insert("test_table", values: ["id": i])
        }
        let endTime = Date()
        
        // Assert
        let duration = endTime.timeIntervalSince(startTime)
        let throughput = Double(iterations) / duration
        #expect(throughput > 1000) // Target: 1000+ ops/sec
    }
}
```

### 4. Stress Tests
Test con carico elevato:

```swift
import Testing
@testable import ColibriCore

struct StressTests {
    @Test func testConcurrentTransactions() async throws {
        // Arrange
        let config = DBConfig.default
        let database = try await Database.create(config: config)
        let concurrentTasks = 100
        let operationsPerTask = 1000
        
        // Act
        let tasks = (0..<concurrentTasks).map { taskID in
            Task {
                for i in 0..<operationsPerTask {
                    try await database.insert("test_table", values: [
                        "task_id": taskID,
                        "operation_id": i
                    ])
                }
            }
        }
        
        try await withThrowingTaskGroup(of: Void.self) { group in
            for task in tasks {
                group.addTask { try await task.value }
            }
        }
        
        // Assert
        let count = try await database.count("test_table")
        #expect(count == concurrentTasks * operationsPerTask)
    }
}
```

## 🚀 Esecuzione Test

### Comandi Base
```bash
# Tutti i test
swift test

# Test specifici per modulo
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Test con verbose output
swift test --verbose

# Test con parallelizzazione
swift test --parallel
```

### Test per Categoria
```bash
# Unit tests
swift test --filter Unit

# Integration tests
swift test --filter Integration

# Performance tests
swift test --filter Performance

# Stress tests
swift test --filter Stress
```

### Test con Coverage
```bash
# Abilita code coverage
swift test --enable-code-coverage

# Genera report coverage
swift test --enable-code-coverage
xcrun llvm-cov show .build/debug/ColibriCorePackageTests.xctest/Contents/MacOS/ColibriCorePackageTests -instr-profile .build/debug/codecov/default.profdata
```

## ✍️ Scrittura Test

### Struttura Test
```swift
import Testing
@testable import ColibriCore

struct NomeModuloTests {
    // MARK: - Setup & Teardown
    
    @Test func setUp() async throws {
        // Setup per ogni test
    }
    
    @Test func tearDown() async throws {
        // Cleanup dopo ogni test
    }
    
    // MARK: - Test Cases
    
    @Test func testFunzionalitaBase() async throws {
        // Arrange
        let input = "test"
        
        // Act
        let result = await funzione(input)
        
        // Assert
        #expect(result == "expected")
    }
    
    @Test func testCasoEdge() async throws {
        // Test per casi limite
    }
    
    @Test func testErrorHandling() async throws {
        // Test per gestione errori
    }
}
```

### Pattern di Testing
```swift
// 1. Arrange-Act-Assert
@Test func testPattern() async throws {
    // Arrange
    let input = "test"
    let expected = "expected"
    
    // Act
    let result = await funzione(input)
    
    // Assert
    #expect(result == expected)
}

// 2. Given-When-Then
@Test func testGivenWhenThen() async throws {
    // Given
    let database = try await Database.create()
    
    // When
    try await database.insert("table", values: ["id": 1])
    
    // Then
    let result = try await database.select("table")
    #expect(result.count == 1)
}

// 3. Test Data Builders
struct TestDataBuilder {
    static func createPage(id: PageID = PageID(1)) -> Page {
        return Page(pageID: id, data: Data(repeating: 0, count: 8192))
    }
    
    static func createDatabase() async throws -> Database {
        return try await Database.create(config: DBConfig.default)
    }
}
```

### Mock e Stub
```swift
// Mock per testing
protocol WALManagerProtocol {
    func log(record: WALRecord) async throws
}

class MockWALManager: WALManagerProtocol {
    var loggedRecords: [WALRecord] = []
    
    func log(record: WALRecord) async throws {
        loggedRecords.append(record)
    }
}

// Test con mock
@Test func testWithMock() async throws {
    // Arrange
    let mockWAL = MockWALManager()
    let database = Database(walManager: mockWAL)
    
    // Act
    try await database.insert("table", values: ["id": 1])
    
    // Assert
    #expect(mockWAL.loggedRecords.count == 1)
}
```

## 📊 Benchmark e Performance

### Benchmark Framework
```swift
import Testing
@testable import ColibriCore

struct BenchmarkTests {
    @Test func benchmarkWALThroughput() async throws {
        let benchmark = WALThroughputBenchmark()
        let result = await benchmark.run(duration: 30)
        
        // Assert performance targets
        #expect(result.operationsPerSecond > 10000)
        #expect(result.averageLatency < 0.1) // 100ms
    }
    
    @Test func benchmarkBufferHitRate() async throws {
        let benchmark = BufferHitRateBenchmark()
        let result = await benchmark.run(workload: .mixed)
        
        // Assert hit rate targets
        #expect(result.hitRate > 0.95) // 95%
    }
}
```

### Esecuzione Benchmark
```bash
# Benchmark specifici
swift run benchmarks --wal-throughput
swift run benchmarks --btree-lookups
swift run benchmarks --buffer-hit-rate

# Benchmark con parametri
swift run benchmarks --wal-throughput --duration 60s
swift run benchmarks --btree-lookups --keys 1000000

# Benchmark con profiling
swift run benchmarks --profile --wal-throughput
```

### Metriche Performance
```swift
public struct PerformanceMetrics {
    public var walThroughput: Double = 0
    public var bufferHitRate: Double = 0
    public var transactionThroughput: Double = 0
    public var averageLatency: Double = 0
    public var memoryUsage: UInt64 = 0
    
    public func validate() -> Bool {
        return walThroughput > 10000 &&
               bufferHitRate > 0.95 &&
               transactionThroughput > 1000 &&
               averageLatency < 0.1
    }
}
```

## 🔄 Continuous Integration

### GitHub Actions
```yaml
name: Tests
on: [push, pull_request]

jobs:
  test:
    runs-on: macos-latest
    steps:
      - uses: actions/checkout@v4
      - uses: swift-actions/setup-swift@v1
        with:
          swift-version: "6.2"
      
      - name: Run Tests
        run: swift test
      
      - name: Run Benchmarks
        run: swift run benchmarks
      
      - name: Generate Coverage
        run: |
          swift test --enable-code-coverage
          xcrun llvm-cov show .build/debug/ColibriCorePackageTests.xctest/Contents/MacOS/ColibriCorePackageTests -instr-profile .build/debug/codecov/default.profdata
```

### Test Matrix
```yaml
strategy:
  matrix:
    swift-version: ["6.0", "6.1", "6.2"]
    platform: ["macos-latest", "ubuntu-latest"]
    configuration: ["debug", "release"]
```

## 🐛 Debugging Test

### Debugging Tools
```bash
# Debug con verbose output
swift test --verbose --filter TestName

# Debug con breakpoint
swift test --debug --filter TestName

# Debug specifico modulo
swift test --debug --filter WAL
```

### Logging in Test
```swift
import Testing
@testable import ColibriCore

struct DebugTests {
    @Test func testWithLogging() async throws {
        // Enable debug logging
        Logger.level = .debug
        
        // Test implementation
        let database = try await Database.create()
        Logger.debug("Database created successfully")
        
        // Assert
        #expect(database != nil)
    }
}
```

### Test Isolation
```swift
// Ogni test deve essere isolato
struct IsolatedTests {
    @Test func testIsolation() async throws {
        // Usa dati di test unici
        let uniqueID = UUID().uuidString
        let database = try await Database.create(name: "test_\(uniqueID)")
        
        // Test implementation
        
        // Cleanup automatico
        try await database.close()
    }
}
```

## ✅ Best Practices

### 1. Naming Conventions
```swift
// Test class naming
struct PageTests { }           // ✅ Good
struct PageTest { }            // ❌ Bad

// Test method naming
@Test func testPageCreation() { }     // ✅ Good
@Test func test() { }                 // ❌ Bad
@Test func pageCreation() { }         // ❌ Bad
```

### 2. Test Organization
```swift
struct PageTests {
    // Group related tests
    @Test func testPageCreation() { }
    @Test func testPageAllocation() { }
    @Test func testPageDeallocation() { }
    
    // Separate groups with comments
    // MARK: - Slot Directory Tests
    
    @Test func testSlotAllocation() { }
    @Test func testSlotDeallocation() { }
}
```

### 3. Assertions
```swift
// Use specific assertions
#expect(result == expected)           // ✅ Good
#expect(result != nil)                // ✅ Good
#expect(array.contains(element))      // ✅ Good

// Avoid generic assertions
#expect(true)                         // ❌ Bad
#expect(result)                       // ❌ Bad
```

### 4. Test Data
```swift
// Use test data builders
struct TestData {
    static func createPage(id: PageID = PageID(1)) -> Page {
        return Page(pageID: id, data: Data(repeating: 0, count: 8192))
    }
    
    static func createDatabase() async throws -> Database {
        return try await Database.create(config: DBConfig.default)
    }
}
```

### 5. Error Testing
```swift
@Test func testErrorHandling() async throws {
    // Test expected errors
    do {
        try await database.insert("nonexistent_table", values: [:])
        #expect(false, "Expected error not thrown")
    } catch DatabaseError.tableNotFound {
        // Expected error
    } catch {
        #expect(false, "Unexpected error: \(error)")
    }
}
```

### 6. Performance Testing
```swift
@Test func testPerformance() async throws {
    // Measure performance
    let startTime = Date()
    // ... perform operation
    let endTime = Date()
    
    let duration = endTime.timeIntervalSince(startTime)
    #expect(duration < 1.0) // Should complete in under 1 second
}
```

---

Questa guida fornisce le basi per scrivere test efficaci per ColibrDB. Per domande specifiche, consulta la documentazione tecnica o apri una discussione su GitHub.

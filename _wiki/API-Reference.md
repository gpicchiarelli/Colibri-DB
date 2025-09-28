---
layout: doc
title: API Reference
description: Documentazione completa delle API di ColibrDB
---

# 📚 API Reference

Documentazione completa delle API pubbliche di ColibrDB.

## 🎯 Panoramica

ColibrDB espone un'API modulare organizzata in diversi livelli:

- **Database Core**: API principale per operazioni database
- **Storage Engine**: API per gestione storage e pagine
- **Index Manager**: API per gestione indici
- **Transaction Manager**: API per gestione transazioni
- **WAL Manager**: API per Write-Ahead Logging
- **Buffer Pool**: API per gestione cache
- **SQL Interface**: API per esecuzione query SQL

## 🗄️ Database Core API

### `Database`

La classe principale che coordina tutti i componenti del database.

```swift
public final class Database {
    public let config: DBConfig
    
    // MARK: - Initialization
    public init(config: DBConfig)
    
    // MARK: - Table Operations
    public func createTable(_ name: String) throws
    public func dropTable(_ name: String) throws
    public func listTables() -> [String]
    
    // MARK: - Data Operations
    public func insert(_ table: String, row: Row) throws -> RID
    public func select(_ table: String, predicate: Predicate?) throws -> [Row]
    public func update(_ table: String, rid: RID, row: Row) throws
    public func delete(_ table: String, rid: RID) throws
    
    // MARK: - Transaction Management
    public func begin() throws -> UInt64
    public func commit(_ tid: UInt64) throws
    public func rollback(toSavepoint: String, tid: UInt64) throws
    
    // MARK: - Index Operations
    public func createIndex(_ name: String, on table: String, columns: [String], type: IndexType) throws
    public func dropIndex(_ name: String) throws
    public func listIndexes() -> [String]
    
    // MARK: - Maintenance
    public func vacuum() throws
    public func checkpoint() throws
    public func analyze() throws
}
```

### Esempio di Utilizzo

```swift
import ColibriCore

// Inizializza il database
let config = DBConfig(
    dataDir: "./data",
    bufferPoolSizeBytes: 1073741824,
    pageSizeBytes: 8192,
    walEnabled: true
)

let database = Database(config: config)

// Crea una tabella
try database.createTable("users")

// Inserisci dati
let row = Row([
    "id": .int(1),
    "name": .string("Alice"),
    "email": .string("alice@example.com"),
    "age": .int(25)
])

let rid = try database.insert("users", row: row)

// Interroga i dati
let rows = try database.select("users", predicate: nil)
```

## 🏗️ Storage Engine API

### `StorageEngineProtocol`

Interfaccia per i motori di storage.

```swift
public protocol StorageEngineProtocol {
    var pageSize: Int { get }
    
    mutating func open(dataDir: String) throws
    mutating func createTable(_ name: String) throws
    func table(_ name: String) throws -> TableStorageProtocol
}
```

### `TableStorageProtocol`

Interfaccia per l'accesso alle tabelle.

```swift
public protocol TableStorageProtocol {
    @discardableResult
    mutating func insert(_ row: Row) throws -> RID
    
    func scan() throws -> AnySequence<(RID, Row)>
    func read(_ rid: RID) throws -> Row
    mutating func update(_ rid: RID, _ newRow: Row) throws
    mutating func remove(_ rid: RID) throws
}
```

### `FileHeapTable`

Implementazione storage basata su file heap.

```swift
public class FileHeapTable: TableStorageProtocol {
    public let name: String
    public let pageSize: Int
    
    public init(name: String, pageSize: Int, dataDir: String) throws
    
    // Implementa TableStorageProtocol
    public func insert(_ row: Row) throws -> RID
    public func scan() throws -> AnySequence<(RID, Row)>
    public func read(_ rid: RID) throws -> Row
    public func update(_ rid: RID, _ newRow: Row) throws
    public func remove(_ rid: RID) throws
    
    // Metodi aggiuntivi
    public func compact() throws
    public func getStatistics() -> HeapFragmentationStats
}
```

### Esempio di Utilizzo Storage

```swift
// Crea una tabella file heap
let table = try FileHeapTable(
    name: "users",
    pageSize: 8192,
    dataDir: "./data"
)

// Inserisci dati
let row = Row(["id": .int(1), "name": .string("Alice")])
let rid = try table.insert(row)

// Leggi dati
let retrievedRow = try table.read(rid)

// Scansiona tutti i record
for (rid, row) in try table.scan() {
    print("RID: \(rid), Row: \(row)")
}
```

## 🔍 Index Manager API

### `IndexProtocol`

Interfaccia base per tutti i tipi di indici.

```swift
public protocol IndexProtocol {
    associatedtype Key: Hashable & Comparable
    associatedtype Ref
    
    mutating func insert(_ key: Key, _ ref: Ref) throws
    func searchEquals(_ key: Key) throws -> [Ref]
    func range(_ lo: Key?, _ hi: Key?) throws -> [Ref]
    mutating func remove(_ key: Key, _ ref: Ref) throws
}
```

### `BPlusTreeIndex`

Implementazione indice B+Tree.

```swift
public class BPlusTreeIndex<Key: Comparable & Codable>: IndexProtocol {
    public let name: String
    public let tableName: String
    public let columnName: String
    
    public init(name: String, tableName: String, columnName: String, config: IndexConfig) throws
    
    // Implementa IndexProtocol
    public func insert(_ key: Key, _ ref: RID) throws
    public func searchEquals(_ key: Key) throws -> [RID]
    public func range(_ lo: Key?, _ hi: Key?) throws -> [RID]
    public func remove(_ key: Key, _ ref: RID) throws
    
    // Metodi aggiuntivi
    public func bulkLoad(_ entries: [(Key, RID)]) throws
    public func validate() throws -> Bool
    public func getStatistics() -> IndexStatistics
}
```

### `HashIndex`

Implementazione indice Hash.

```swift
public class HashIndex<Key: Hashable & Codable>: IndexProtocol {
    public let name: String
    public let tableName: String
    public let columnName: String
    
    public init(name: String, tableName: String, columnName: String, config: IndexConfig) throws
    
    // Implementa IndexProtocol
    public func insert(_ key: Key, _ ref: RID) throws
    public func searchEquals(_ key: Key) throws -> [RID]
    public func range(_ lo: Key?, _ hi: Key?) throws -> [RID]
    public func remove(_ key: Key, _ ref: RID) throws
}
```

### Esempio di Utilizzo Indici

```swift
// Crea un indice B+Tree
let btreeIndex = try BPlusTreeIndex<String>(
    name: "idx_users_name",
    tableName: "users",
    columnName: "name",
    config: IndexConfig()
)

// Inserisci chiavi nell'indice
try btreeIndex.insert("Alice", RID(pageId: 1, slotId: 0))
try btreeIndex.insert("Bob", RID(pageId: 1, slotId: 1))

// Cerca per chiave esatta
let rids = try btreeIndex.searchEquals("Alice")

// Cerca per range
let rangeRids = try btreeIndex.range("A", "C")

// Crea un indice Hash
let hashIndex = try HashIndex<String>(
    name: "idx_users_email",
    tableName: "users",
    columnName: "email",
    config: IndexConfig()
)
```

## 🔄 Transaction Manager API

### `TransactionManagerProtocol`

Interfaccia per gestione transazioni.

```swift
public protocol TransactionManagerProtocol {
    func begin() throws -> UInt64
    func commit(_ tid: UInt64) throws
    func rollback(_ tid: UInt64) throws
}
```

### `MVCCManager`

Implementazione Multi-Version Concurrency Control.

```swift
public class MVCCManager {
    public enum IsolationLevel {
        case readUncommitted
        case readCommitted
        case repeatableRead
        case serializable
    }
    
    public func beginTransaction(isolation: IsolationLevel) throws -> UInt64
    public func commitTransaction(_ tid: UInt64) throws
    public func rollbackTransaction(_ tid: UInt64) throws
    
    public func isVisible(_ tid: UInt64, _ version: RowVersion) -> Bool
    public func createVersion(_ tid: UInt64, _ row: Row) -> RowVersion
    public func getVisibleVersion(_ tid: UInt64, _ rid: RID) throws -> RowVersion?
}
```

### `LockManager`

Gestione lock per controllo concorrenza.

```swift
public class LockManager {
    public enum LockMode {
        case shared
        case exclusive
    }
    
    public init(defaultTimeout: TimeInterval)
    
    @discardableResult
    public func lock(_ resource: LockTarget, mode: LockMode, tid: UInt64, timeout: TimeInterval?) throws -> LockHandle
    
    public func unlock(_ handle: LockHandle)
    public func unlockAll(for tid: UInt64)
    
    public func detectDeadlock() -> [UInt64]
}
```

### Esempio di Utilizzo Transazioni

```swift
// Inizia una transazione
let tid = try database.begin()

do {
    // Esegui operazioni
    let row1 = Row(["id": .int(1), "name": .string("Alice")])
    let rid1 = try database.insert("users", row: row1)
    
    let row2 = Row(["id": .int(2), "name": .string("Bob")])
    let rid2 = try database.insert("users", row: row2)
    
    // Conferma la transazione
    try database.commit(tid)
    
} catch {
    // Annulla la transazione in caso di errore
    try database.rollback(toSavepoint: "", tid: tid)
}
```

## 📝 WAL Manager API

### `WALManager`

Interfaccia unificata per Write-Ahead Logging.

```swift
public protocol WALManager: WALWriter, WALReader, WALCheckpointing {
    var dbId: UInt32 { get }
    var durabilityMode: DurabilityMode { get set }
    var metrics: WALMetrics { get }
    
    func close() throws
}
```

### `WALWriter`

Interfaccia per scrittura WAL.

```swift
public protocol WALWriter {
    @discardableResult func append(_ record: WALRecord) throws -> UInt64
    func groupCommitSync() throws
    var flushedLSN: UInt64 { get }
    func flush(upTo lsn: UInt64) throws
}
```

### `WALReader`

Interfaccia per lettura WAL.

```swift
public protocol WALReader {
    func iterate(from lsn: UInt64) throws -> AnyIterator<WALRecord>
    func lastLSN() throws -> UInt64
    func read(lsn: UInt64) throws -> WALRecord?
}
```

### `FileWALManager`

Implementazione WAL basata su file.

```swift
public class FileWALManager: WALManager {
    public let dbId: UInt32
    public var durabilityMode: DurabilityMode
    public var metrics: WALMetrics
    
    public init(
        dbId: UInt32,
        path: String,
        durabilityMode: DurabilityMode,
        groupCommitThreshold: Int,
        groupCommitTimeoutMs: Int,
        compressionAlgorithm: WALCompression
    ) throws
    
    // Implementa WALManager
    public func append(_ record: WALRecord) throws -> UInt64
    public func groupCommitSync() throws
    public func iterate(from lsn: UInt64) throws -> AnyIterator<WALRecord>
    public func writeCheckpoint(dpt: [UInt64: UInt64], att: [UInt64: UInt64]) throws -> UInt64
    public func close() throws
}
```

### Esempio di Utilizzo WAL

```swift
// Crea un WAL manager
let walManager = try FileWALManager(
    dbId: 1,
    path: "/path/to/wal",
    durabilityMode: .grouped,
    groupCommitThreshold: 8,
    groupCommitTimeoutMs: 100,
    compressionAlgorithm: .lz4
)

// Aggiungi record al WAL
let record = WALRecord(
    type: .insert,
    transactionId: 123,
    pageId: 1,
    data: rowData,
    checksum: 0,
    timestamp: Date().timeIntervalSince1970
)

let lsn = try walManager.append(record)

// Forza flush
try walManager.flush(upTo: lsn)
```

## 🗃️ Buffer Pool API

### `BufferPoolProtocol`

Interfaccia per gestione buffer pool.

```swift
public protocol BufferPoolProtocol {
    var sizeBytes: UInt64 { get }
    
    func getPage(_ id: PageID) throws -> Data
    func putPage(_ id: PageID, data: Data, dirty: Bool) throws
}
```

### `LRUBufferPool`

Implementazione buffer pool con algoritmo LRU.

```swift
public class LRUBufferPool: BufferPoolProtocol {
    public let sizeBytes: UInt64
    public let pageSize: Int
    
    public init(sizeBytes: UInt64, pageSize: Int)
    
    // Implementa BufferPoolProtocol
    public func getPage(_ id: PageID) throws -> Data
    public func putPage(_ id: PageID, data: Data, dirty: Bool) throws
    
    // Metodi aggiuntivi
    public func flush() throws
    public func getStatistics() -> BufferPoolStatistics
    public func setQuota(for namespace: String, pages: Int)
}
```

### `BufferNamespaceManager`

Gestione namespace per buffer pool.

```swift
public class BufferNamespaceManager {
    public static let shared = BufferNamespaceManager()
    
    public func setQuota(group: String, pages: Int)
    public func getQuota(group: String) -> Int
    public func getUsage(group: String) -> Int
    public func evictFromGroup(_ group: String, count: Int) throws
}
```

### Esempio di Utilizzo Buffer Pool

```swift
// Crea un buffer pool
let bufferPool = LRUBufferPool(
    sizeBytes: 1073741824, // 1GB
    pageSize: 8192
)

// Imposta quote per namespace
BufferNamespaceManager.shared.setQuota(group: "table", pages: 1000)
BufferNamespaceManager.shared.setQuota(group: "index", pages: 500)

// Ottieni una pagina
let pageData = try bufferPool.getPage(PageID(123))

// Modifica e salva la pagina
var modifiedData = pageData
// ... modifica i dati ...
try bufferPool.putPage(PageID(123), data: modifiedData, dirty: true)

// Flush del buffer pool
try bufferPool.flush()
```

## 🔍 SQL Interface API

### `SQLQueryInterface`

Interfaccia per esecuzione query SQL.

```swift
public class SQLQueryInterface {
    public let database: Database
    
    public init(database: Database)
    
    public func execute(_ query: String) throws -> SQLQueryResult
    public func prepare(_ query: String) throws -> SQLPreparedStatement
    public func explain(_ query: String) throws -> SQLExecutionPlan
}
```

### `SQLQueryResult`

Risultato di una query SQL.

```swift
public struct SQLQueryResult {
    public let columns: [String]
    public let rows: [[Value]]
    public let affectedRows: Int
    public let message: String
    public let executionTime: TimeInterval
}
```

### `SQLPreparedStatement`

Statement SQL preparato.

```swift
public class SQLPreparedStatement {
    public func execute(_ parameters: [Value]) throws -> SQLQueryResult
    public func explain() throws -> SQLExecutionPlan
    public func close()
}
```

### Esempio di Utilizzo SQL Interface

```swift
// Crea un'interfaccia SQL
let sqlInterface = SQLQueryInterface(database: database)

// Esegui una query semplice
let result = try sqlInterface.execute("SELECT * FROM users WHERE age > 25")

print("Columns: \(result.columns)")
print("Rows: \(result.rows.count)")
print("Execution time: \(result.executionTime)ms")

// Prepara uno statement
let stmt = try sqlInterface.prepare("INSERT INTO users (name, age) VALUES (?, ?)")

// Esegui con parametri
let insertResult = try stmt.execute([
    .string("Alice"),
    .int(25)
])

// Spiega una query
let plan = try sqlInterface.explain("SELECT * FROM users WHERE name = 'Alice'")
print("Execution plan: \(plan)")
```

## 📊 Types e Data Structures

### `Value`

Tipo di valore per i dati del database.

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    case decimal(Decimal)
    case date(Date)
}
```

### `Row`

Riga del database come dizionario di valori.

```swift
public typealias Row = [String: Value]
```

### `RID`

Record Identifier per identificare univocamente un record.

```swift
public struct RID: Hashable, Codable, CustomStringConvertible {
    public let pageId: UInt64
    public let slotId: UInt16
    
    public init(pageId: UInt64, slotId: UInt16)
}
```

### `DBConfig`

Configurazione del database.

```swift
public struct DBConfig: Codable {
    public var dataDir: String
    public var maxConnectionsLogical: Int
    public var maxConnectionsPhysical: Int
    public var bufferPoolSizeBytes: UInt64
    public var pageSizeBytes: Int
    public var walEnabled: Bool
    public var checksumEnabled: Bool
    public var cliEnabled: Bool
    public var metricsEnabled: Bool
    public var serverEnabled: Bool
    public var indexImplementation: String
    public var storageEngine: String
    
    public init(
        dataDir: String = "./data",
        maxConnectionsLogical: Int = 1000000,
        maxConnectionsPhysical: Int = 16,
        bufferPoolSizeBytes: UInt64 = 1073741824,
        pageSizeBytes: Int = 8192,
        walEnabled: Bool = true,
        checksumEnabled: Bool = true,
        cliEnabled: Bool = true,
        metricsEnabled: Bool = true,
        serverEnabled: Bool = false,
        indexImplementation: String = "Hash",
        storageEngine: String = "FileHeap"
    )
}
```

## 🚨 Error Handling

### `DBError`

Errori del database.

```swift
public enum DBError: Error, CustomStringConvertible {
    case notFound(String)
    case alreadyExists(String)
    case invalidOperation(String)
    case constraintViolation(String)
    case transactionAborted(String)
    case deadlockDetected
    case timeout
    case ioError(String)
    case corruption(String)
    case notImplemented(String)
    
    public var description: String
}
```

### Esempio di Gestione Errori

```swift
do {
    try database.createTable("users")
    let rid = try database.insert("users", row: row)
} catch DBError.notFound(let message) {
    print("Not found: \(message)")
} catch DBError.constraintViolation(let message) {
    print("Constraint violation: \(message)")
} catch DBError.deadlockDetected {
    print("Deadlock detected, retrying...")
} catch {
    print("Unexpected error: \(error)")
}
```

## 📈 Performance e Monitoring

### `DatabaseStatistics`

Statistiche del database.

```swift
public struct DatabaseStatistics {
    public let tablesCount: Int
    public let indexesCount: Int
    public let activeTransactions: Int
    public let bufferPoolHitRate: Double
    public let walSize: UInt64
    public let uptime: TimeInterval
}
```

### `BufferPoolStatistics`

Statistiche del buffer pool.

```swift
public struct BufferPoolStatistics {
    public let totalPages: Int
    public let usedPages: Int
    public let dirtyPages: Int
    public let hitRate: Double
    public let evictions: Int
    public let flushes: Int
}
```

### Esempio di Monitoring

```swift
// Ottieni statistiche del database
let stats = database.getStatistics()
print("Tables: \(stats.tablesCount)")
print("Buffer pool hit rate: \(stats.bufferPoolHitRate)%")

// Ottieni statistiche del buffer pool
let bufferStats = bufferPool.getStatistics()
print("Buffer pool usage: \(bufferStats.usedPages)/\(bufferStats.totalPages)")
print("Hit rate: \(bufferStats.hitRate)%")
```

---

<div align="center">

**📚 API Reference ColibrDB** - *Documentazione completa per sviluppatori*

[← CLI Reference]({{ site.baseurl }}/docs/wiki/CLI-Reference) • [Development Guide →]({{ site.baseurl }}/docs/wiki/Development)

</div>

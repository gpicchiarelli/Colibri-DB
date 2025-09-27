# Index Structures Internals

## Overview

ColibrìDB implements multiple index structures optimized for different access patterns and workloads. This chapter provides a detailed analysis of the B+Tree, ART (Adaptive Radix Tree), and LSM-Tree implementations, their memory layouts, algorithms, and performance characteristics.

## B+Tree Index Implementation

### Class Structure

```swift
/// Indice B+Tree persistente, page-based, con WAL dedicato e buffer pool
/// configurabile. Supporta chiavi composite multi-tipo, bulk build, check di
/// consistenza e compattazione online delle foglie. Tutte le operazioni sono
/// progettate per essere idempotenti così da integrarsi con il recovery ARIES.
public final class FileBPlusTreeIndex {
    public let path: String
    let pageSize: Int
    let fm = FileManager.default
    var fh: FileHandle
    var buf: LRUBufferPool?
    let walPath: String
    var walFH: FileHandle
    var nextLSN: UInt64 = 1
    var opsSinceCheckpoint: Int = 0
    let checkpointEvery: Int = 256
    var ioHintsEnabled: Bool
    var walFullSyncEnabled: Bool = false
}
```

**Detailed Analysis:**

#### Core Configuration
- **`path: String`**: File path for the index
- **`pageSize: Int`**: Fixed page size (typically 8KB)
- **`fm: FileManager`**: File system interface
- **`fh: FileHandle`**: Handle for index file operations

#### Buffer Management
- **`buf: LRUBufferPool?`**: Buffer pool for page caching
- **`capacityPages: Int`**: Maximum pages in buffer pool
- **`deferredWrite: Bool`**: Enable deferred writes
- **`maxDirty: Int`**: Maximum dirty pages before flush

#### WAL (Write-Ahead Logging)
- **`walPath: String`**: Path to WAL file
- **`walFH: FileHandle`**: Handle for WAL operations
- **`nextLSN: UInt64`**: Next Log Sequence Number
- **`opsSinceCheckpoint: Int`**: Operations since last checkpoint
- **`checkpointEvery: Int`**: Checkpoint frequency (256 operations)

#### I/O Optimization
- **`ioHintsEnabled: Bool`**: Enable I/O hints for performance
- **`walFullSyncEnabled: Bool`**: Enable full sync for WAL
- **`flushQoS: DispatchQoS`**: Quality of service for flushing

### Header Structure

```swift
struct Header {
    var pageSize: Int
    var root: UInt64
    var nextPage: UInt64
    var checkpointLSN: UInt64
}
var hdr: Header
```

**Detailed Analysis:**

#### Header Fields
- **`pageSize: Int`**: Page size in bytes
- **`root: UInt64`**: Root page ID
- **`nextPage: UInt64`**: Next available page ID
- **`checkpointLSN: UInt64`**: LSN of last checkpoint

#### Memory Layout
```
Header Layout (32 bytes):
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Page Size   │ Root Page   │ Next Page   │ Checkpoint  │
│ (8 bytes)   │ (8 bytes)   │ (8 bytes)   │ LSN (8 bytes)│
└─────────────┴─────────────┴─────────────┴─────────────┘
```

#### Usage
- **Root Page**: Points to root of B+Tree
- **Next Page**: Allocates new pages sequentially
- **Checkpoint LSN**: Used for WAL recovery
- **Page Size**: Validates page size consistency

### Leaf Node Flags

```swift
enum LeafFlag {
    static let prefixCompressed: UInt8 = 1 << 0
    static let prefixCompressedV2: UInt8 = 1 << 1
    static let ridDeltaEncoded: UInt8 = 1 << 2
}
```

**Detailed Analysis:**

#### Compression Flags
- **`prefixCompressed`**: Basic prefix compression
- **`prefixCompressedV2`**: Improved prefix compression
- **`ridDeltaEncoded`**: RID delta encoding for efficiency

#### Bit Manipulation
- **`1 << 0`**: Bit 0 (0x01)
- **`1 << 1`**: Bit 1 (0x02)
- **`1 << 2`**: Bit 2 (0x04)
- **Combination**: Multiple flags can be set simultaneously

#### Performance Impact
- **Prefix Compression**: Reduces storage for similar keys
- **RID Delta Encoding**: Reduces storage for sequential RIDs
- **Memory**: Saves memory at cost of CPU
- **I/O**: Reduces I/O operations

### Internal Node Flags

```swift
enum InternalFlag {
    static let prefixCompressed: UInt16 = 1 << 15
    static let countMask: UInt16 = 0x7FFF
}
```

**Detailed Analysis:**

#### Compression Flags
- **`prefixCompressed`**: Prefix compression for internal nodes
- **`countMask`**: Mask for extracting child count

#### Bit Manipulation
- **`1 << 15`**: Bit 15 (0x8000)
- **`0x7FFF`**: Lower 15 bits (0x7FFF)
- **Combination**: Count in lower 15 bits, flags in upper bit

#### Usage
- **Child Count**: Extracted using `count & countMask`
- **Compression**: Checked using `count & prefixCompressed`
- **Performance**: Efficient bit manipulation

### Initialization Process

```swift
public init(path: String,
            pageSize: Int,
            capacityPages: Int = 256,
            flushQoS: DispatchQoS = .utility,
            ioHintsEnabled: Bool = false,
            walFullSyncEnabled: Bool = false) throws {
    self.path = path
    self.pageSize = pageSize
    self.ioHintsEnabled = ioHintsEnabled
    let url = URL(fileURLWithPath: path)
    if !fm.fileExists(atPath: path) {
        fm.createFile(atPath: path, contents: nil)
    }
    self.fh = try FileHandle(forUpdating: url)
    self.walPath = path + ".wal"
    if !fm.fileExists(atPath: walPath) {
        fm.createFile(atPath: walPath, contents: nil)
    }
    self.walFH = try FileHandle(forUpdating: URL(fileURLWithPath: walPath))
    try FileBPlusTreeIndex.ensureWALHeader(handle: walFH)
    if try fh.seekToEnd() == 0 {
        self.hdr = Header(pageSize: pageSize, root: 0, nextPage: 1, checkpointLSN: 0)
        try writeHeader()
        try fh.synchronize()
    } else {
        self.hdr = try FileBPlusTreeIndex.readHeader(handle: fh, pageSize: pageSize)
    }
    setFullFSync(enabled: walFullSyncEnabled)
    try replayWAL()
    self.buf = LRUBufferPool(pageSize: pageSize, capacityPages: capacityPages, fetch: { [weak self] pid in
        guard let self = self else { return Data() }
        let off = UInt64(self.pageSize) * pid
        try self.fh.seek(toOffset: off)
        return try self.fh.read(upToCount: self.pageSize) ?? Data(repeating: 0, count: self.pageSize)
    }, flush: { [weak self] pid, data in
        guard let self = self else { return }
        let off = UInt64(self.pageSize) * pid
        try self.fh.seek(toOffset: off)
        try self.fh.write(contentsOf: data)
    }, namespace: "index:\(URL(fileURLWithPath: path).lastPathComponent)", deferredWrite: true, maxDirty: 2048, flushQoS: flushQoS)
    self.buf?.startBackgroundFlush(every: 0.5)
}
```

**Detailed Analysis:**

#### File System Setup
1. **Path Setup**: Store index file path
2. **File Creation**: Create index file if it doesn't exist
3. **File Handle**: Open file for read/write operations
4. **WAL Setup**: Create and open WAL file

#### Header Initialization
- **New Index**: Create header with default values
- **Existing Index**: Read header from file
- **Synchronization**: Sync file to ensure durability
- **WAL Recovery**: Replay WAL for crash recovery

#### Buffer Pool Setup
- **Fetch Callback**: Load page from file
- **Flush Callback**: Write page to file
- **Namespace**: Unique namespace for quota management
- **Deferred Write**: Enable deferred writes for performance
- **Background Flush**: Start background flushing every 0.5 seconds

#### Page I/O Operations
```swift
fetch: { [weak self] pid in
    guard let self = self else { return Data() }
    let off = UInt64(self.pageSize) * pid
    try self.fh.seek(toOffset: off)
    return try self.fh.read(upToCount: self.pageSize) ?? Data(repeating: 0, count: self.pageSize)
}
```

**Analysis:**
- **Page Offset**: `pageSize * pageId` for page location
- **Seek Operation**: Move file pointer to page start
- **Read Operation**: Read exactly pageSize bytes
- **Error Handling**: Return zero-filled data on read failure
- **Performance**: O(1) for seek, O(1) for read

#### Page Write Operations
```swift
flush: { [weak self] pid, data in
    guard let self = self else { return }
    let off = UInt64(self.pageSize) * pid
    try self.fh.seek(toOffset: off)
    try self.fh.write(contentsOf: data)
}
```

**Analysis:**
- **Page Offset**: `pageSize * pageId` for page location
- **Seek Operation**: Move file pointer to page start
- **Write Operation**: Write exactly pageSize bytes
- **Error Handling**: Throws errors for write failures
- **Performance**: O(1) for seek, O(1) for write

### B+Tree Node Structure

#### Leaf Node Layout

```
Leaf Node Layout:
┌─────────────────────────────────────────────────────────┐
│ Header (8 bytes)                                       │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Flags       │ Count       │ Next Page   │            │
│ │ (1 byte)    │ (2 bytes)   │ (4 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
├─────────────────────────────────────────────────────────┤
│ Key-Value Pairs                                        │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Key Length  │ Key Data    │ RID         │            │
│ │ (2 bytes)   │ (variable)  │ (8 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Key Length  │ Key Data    │ RID         │            │
│ │ (2 bytes)   │ (variable)  │ (8 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
│ ...                                                     │
└─────────────────────────────────────────────────────────┘
```

**Detailed Analysis:**

#### Header Fields
- **Flags (1 byte)**: Compression and encoding flags
- **Count (2 bytes)**: Number of key-value pairs
- **Next Page (4 bytes)**: Pointer to next leaf page

#### Key-Value Pairs
- **Key Length (2 bytes)**: Length of key data
- **Key Data (variable)**: Actual key bytes
- **RID (8 bytes)**: Record identifier

#### Memory Layout
- **Header**: Fixed 8 bytes
- **Keys**: Variable length with length prefix
- **Values**: Fixed 8 bytes (RID)
- **Total**: Variable size based on key lengths

#### Internal Node Layout

```
Internal Node Layout:
┌─────────────────────────────────────────────────────────┐
│ Header (8 bytes)                                       │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Flags       │ Count       │ Reserved    │            │
│ │ (1 byte)    │ (2 bytes)   │ (4 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
├─────────────────────────────────────────────────────────┤
│ Key-Pointer Pairs                                      │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Key Length  │ Key Data    │ Page ID     │            │
│ │ (2 bytes)   │ (variable)  │ (8 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
│ ┌─────────────┬─────────────┬─────────────┐            │
│ │ Key Length  │ Key Data    │ Page ID     │            │
│ │ (2 bytes)   │ (variable)  │ (8 bytes)   │            │
│ └─────────────┴─────────────┴─────────────┘            │
│ ...                                                     │
└─────────────────────────────────────────────────────────┘
```

**Detailed Analysis:**

#### Header Fields
- **Flags (1 byte)**: Compression and encoding flags
- **Count (2 bytes)**: Number of key-pointer pairs
- **Reserved (4 bytes)**: Reserved for future use

#### Key-Pointer Pairs
- **Key Length (2 bytes)**: Length of key data
- **Key Data (variable)**: Actual key bytes
- **Page ID (8 bytes)**: Child page identifier

#### Memory Layout
- **Header**: Fixed 8 bytes
- **Keys**: Variable length with length prefix
- **Pointers**: Fixed 8 bytes (Page ID)
- **Total**: Variable size based on key lengths

### B+Tree Operations

#### Search Operation

```swift
public func search(key: [UInt8]) -> [RID] {
    guard hdr.root != 0 else { return [] }
    
    var currentPage = hdr.root
    while true {
        let page = try! buf!.getPage(currentPage)
        let node = BPlusTreeNode(page: page, pageSize: pageSize)
        
        if node.isLeaf {
            return node.searchLeaf(key: key)
        } else {
            currentPage = node.searchInternal(key: key)
        }
    }
}
```

**Detailed Analysis:**

#### Search Process
1. **Root Check**: Ensure tree is not empty
2. **Page Load**: Load current page from buffer pool
3. **Node Creation**: Create B+Tree node from page
4. **Leaf Check**: Determine if current node is leaf
5. **Leaf Search**: Search within leaf node
6. **Internal Search**: Navigate to child page

#### Performance
- **Height**: O(log n) where n is number of records
- **Page Access**: O(log n) page reads
- **Key Comparison**: O(log n) key comparisons
- **Total Time**: O(log n) where n is number of records

#### Leaf Search
```swift
func searchLeaf(key: [UInt8]) -> [RID] {
    var results: [RID] = []
    
    for i in 0..<count {
        let keyLength = readUInt16(offset: keyOffset(i))
        let keyData = readBytes(offset: keyOffset(i) + 2, length: keyLength)
        
        if keyData == key {
            let rid = readRID(offset: valueOffset(i))
            results.append(rid)
        }
    }
    
    return results
}
```

**Analysis:**
- **Linear Scan**: Scan all keys in leaf node
- **Key Comparison**: Compare each key with search key
- **Result Collection**: Collect matching RIDs
- **Performance**: O(n) where n is keys per leaf

#### Internal Search
```swift
func searchInternal(key: [UInt8]) -> UInt64 {
    for i in 0..<count {
        let keyLength = readUInt16(offset: keyOffset(i))
        let keyData = readBytes(offset: keyOffset(i) + 2, length: keyLength)
        
        if key < keyData {
            return readPageID(offset: pointerOffset(i))
        }
    }
    
    return readPageID(offset: pointerOffset(count))
}
```

**Analysis:**
- **Linear Scan**: Scan keys to find appropriate child
- **Key Comparison**: Compare search key with node keys
- **Child Selection**: Select child page based on comparison
- **Performance**: O(n) where n is keys per internal node

#### Insert Operation

```swift
public func insert(key: [UInt8], rid: RID) throws {
    guard hdr.root != 0 else {
        // Create root leaf node
        let rootPage = try allocatePage()
        let rootNode = BPlusTreeNode(page: Data(repeating: 0, count: pageSize), pageSize: pageSize)
        rootNode.makeLeaf()
        rootNode.insert(key: key, rid: rid)
        try writeNode(rootNode, pageID: rootPage)
        hdr.root = rootPage
        try writeHeader()
        return
    }
    
    let result = try insertRecursive(key: key, rid: rid, pageID: hdr.root)
    if let newRoot = result.newRoot {
        hdr.root = newRoot
        try writeHeader()
    }
}
```

**Detailed Analysis:**

#### Insert Process
1. **Empty Tree**: Create root leaf node if tree is empty
2. **Recursive Insert**: Insert key-value pair recursively
3. **Root Split**: Handle root node splitting
4. **Header Update**: Update root page ID if needed

#### Empty Tree Handling
- **Root Creation**: Allocate new page for root
- **Leaf Node**: Create leaf node structure
- **Key Insertion**: Insert first key-value pair
- **Header Update**: Update root page ID

#### Recursive Insert
```swift
func insertRecursive(key: [UInt8], rid: RID, pageID: UInt64) throws -> (newRoot: UInt64?, split: Bool) {
    let page = try buf!.getPage(pageID)
    let node = BPlusTreeNode(page: page, pageSize: pageSize)
    
    if node.isLeaf {
        return try insertLeaf(key: key, rid: rid, node: node, pageID: pageID)
    } else {
        return try insertInternal(key: key, rid: rid, node: node, pageID: pageID)
    }
}
```

**Analysis:**
- **Page Load**: Load current page from buffer pool
- **Node Creation**: Create B+Tree node from page
- **Leaf Insert**: Handle leaf node insertion
- **Internal Insert**: Handle internal node insertion
- **Return**: Return split information and new root

#### Leaf Insertion
```swift
func insertLeaf(key: [UInt8], rid: RID, node: BPlusTreeNode, pageID: UInt64) throws -> (newRoot: UInt64?, split: Bool) {
    if node.canInsert(key: key) {
        // Insert into current node
        node.insert(key: key, rid: rid)
        try writeNode(node, pageID: pageID)
        return (nil, false)
    } else {
        // Split node
        let (leftNode, rightNode, splitKey) = node.split()
        let rightPageID = try allocatePage()
        
        // Insert into appropriate node
        if key < splitKey {
            leftNode.insert(key: key, rid: rid)
        } else {
            rightNode.insert(key: key, rid: rid)
        }
        
        try writeNode(leftNode, pageID: pageID)
        try writeNode(rightNode, pageID: rightPageID)
        
        return (nil, true)
    }
}
```

**Analysis:**
- **Space Check**: Check if node has space for new key
- **Direct Insert**: Insert key-value pair if space available
- **Node Split**: Split node if no space available
- **Key Distribution**: Distribute keys between split nodes
- **Page Allocation**: Allocate new page for right node

#### Delete Operation

```swift
public func delete(key: [UInt8], rid: RID) throws {
    guard hdr.root != 0 else { return }
    
    let result = try deleteRecursive(key: key, rid: rid, pageID: hdr.root)
    if let newRoot = result.newRoot {
        hdr.root = newRoot
        try writeHeader()
    }
}
```

**Detailed Analysis:**

#### Delete Process
1. **Empty Tree**: Return if tree is empty
2. **Recursive Delete**: Delete key-value pair recursively
3. **Root Update**: Update root page ID if needed
4. **Header Update**: Update header if root changed

#### Recursive Delete
```swift
func deleteRecursive(key: [UInt8], rid: RID, pageID: UInt64) throws -> (newRoot: UInt64?, deleted: Bool) {
    let page = try buf!.getPage(pageID)
    let node = BPlusTreeNode(page: page, pageSize: pageSize)
    
    if node.isLeaf {
        return try deleteLeaf(key: key, rid: rid, node: node, pageID: pageID)
    } else {
        return try deleteInternal(key: key, rid: rid, node: node, pageID: pageID)
    }
}
```

**Analysis:**
- **Page Load**: Load current page from buffer pool
- **Node Creation**: Create B+Tree node from page
- **Leaf Delete**: Handle leaf node deletion
- **Internal Delete**: Handle internal node deletion
- **Return**: Return deletion status and new root

## ART (Adaptive Radix Tree) Index

### Class Structure

```swift
public final class ARTIndex {
    private var root: ARTNode?
    private let maxKeyLength: Int
    private var nodeCount: Int = 0
    private var keyCount: Int = 0
    
    public init(maxKeyLength: Int = 1024) {
        self.maxKeyLength = maxKeyLength
        self.root = nil
    }
}
```

**Detailed Analysis:**

#### Core Configuration
- **`root: ARTNode?`**: Root node of the tree
- **`maxKeyLength: Int`**: Maximum key length (1024 bytes)
- **`nodeCount: Int`**: Number of nodes in tree
- **`keyCount: Int`**: Number of keys in tree

#### Memory Layout
- **Root Node**: Optional root node
- **Node Count**: Tracks tree size
- **Key Count**: Tracks number of stored keys
- **Max Key Length**: Prevents excessive memory usage

### ART Node Types

#### Node4 (4 children)
```swift
struct Node4: ARTNode {
    var partialKey: [UInt8]
    var children: [UInt8: ARTNode] = [:]
    var value: RID?
    
    init(partialKey: [UInt8] = []) {
        self.partialKey = partialKey
    }
}
```

**Analysis:**
- **Partial Key**: Common prefix of keys in subtree
- **Children**: Up to 4 child nodes
- **Value**: Optional value for leaf nodes
- **Memory**: Fixed size for small nodes

#### Node16 (16 children)
```swift
struct Node16: ARTNode {
    var partialKey: [UInt8]
    var children: [UInt8: ARTNode] = [:]
    var value: RID?
    
    init(partialKey: [UInt8] = []) {
        self.partialKey = partialKey
    }
}
```

**Analysis:**
- **Partial Key**: Common prefix of keys in subtree
- **Children**: Up to 16 child nodes
- **Value**: Optional value for leaf nodes
- **Memory**: Larger than Node4 for more children

#### Node48 (48 children)
```swift
struct Node48: ARTNode {
    var partialKey: [UInt8]
    var children: [UInt8: ARTNode] = [:]
    var value: RID?
    
    init(partialKey: [UInt8] = []) {
        self.partialKey = partialKey
    }
}
```

**Analysis:**
- **Partial Key**: Common prefix of keys in subtree
- **Children**: Up to 48 child nodes
- **Value**: Optional value for leaf nodes
- **Memory**: Larger than Node16 for more children

#### Node256 (256 children)
```swift
struct Node256: ARTNode {
    var partialKey: [UInt8]
    var children: [UInt8: ARTNode] = [:]
    var value: RID?
    
    init(partialKey: [UInt8] = []) {
        self.partialKey = partialKey
    }
}
```

**Analysis:**
- **Partial Key**: Common prefix of keys in subtree
- **Children**: Up to 256 child nodes
- **Value**: Optional value for leaf nodes
- **Memory**: Largest node type for maximum children

### ART Operations

#### Search Operation

```swift
public func search(key: [UInt8]) -> [RID] {
    guard let root = root else { return [] }
    
    var current = root
    var keyOffset = 0
    
    while true {
        // Check partial key match
        if keyOffset + current.partialKey.count > key.count {
            return [] // Key too short
        }
        
        for i in 0..<current.partialKey.count {
            if key[keyOffset + i] != current.partialKey[i] {
                return [] // Partial key mismatch
            }
        }
        
        keyOffset += current.partialKey.count
        
        if keyOffset == key.count {
            // Found complete key
            return current.value != nil ? [current.value!] : []
        }
        
        // Navigate to child
        let nextByte = key[keyOffset]
        if let child = current.children[nextByte] {
            current = child
            keyOffset += 1
        } else {
            return [] // No child found
        }
    }
}
```

**Detailed Analysis:**

#### Search Process
1. **Root Check**: Ensure tree is not empty
2. **Partial Key Match**: Check common prefix
3. **Key Length Check**: Ensure key is long enough
4. **Complete Key Check**: Check if key is complete
5. **Child Navigation**: Navigate to appropriate child
6. **Result Return**: Return value if found

#### Performance
- **Time Complexity**: O(k) where k is key length
- **Space Complexity**: O(n) where n is number of keys
- **Memory Access**: O(k) memory accesses
- **Cache Efficiency**: Good cache locality

#### Insert Operation

```swift
public func insert(key: [UInt8], rid: RID) {
    if root == nil {
        root = Node4(partialKey: key)
        root!.value = rid
        keyCount = 1
        nodeCount = 1
        return
    }
    
    root = insertRecursive(key: key, rid: rid, node: root!, keyOffset: 0)
    keyCount += 1
}
```

**Detailed Analysis:**

#### Insert Process
1. **Empty Tree**: Create root node if tree is empty
2. **Recursive Insert**: Insert key-value pair recursively
3. **Node Splitting**: Handle node splitting if needed
4. **Count Update**: Update key and node counts

#### Recursive Insert
```swift
func insertRecursive(key: [UInt8], rid: RID, node: ARTNode, keyOffset: Int) -> ARTNode {
    // Check partial key match
    if keyOffset + node.partialKey.count > key.count {
        // Key too short, need to split
        return splitNode(node: node, key: key, rid: rid, keyOffset: keyOffset)
    }
    
    for i in 0..<node.partialKey.count {
        if key[keyOffset + i] != node.partialKey[i] {
            // Partial key mismatch, need to split
            return splitNode(node: node, key: key, rid: rid, keyOffset: keyOffset)
        }
    }
    
    let newKeyOffset = keyOffset + node.partialKey.count
    
    if newKeyOffset == key.count {
        // Complete key match
        node.value = rid
        return node
    }
    
    // Navigate to child
    let nextByte = key[newKeyOffset]
    if let child = node.children[nextByte] {
        node.children[nextByte] = insertRecursive(key: key, rid: rid, node: child, keyOffset: newKeyOffset + 1)
        return node
    } else {
        // Create new child
        let childKey = Array(key[(newKeyOffset + 1)...])
        let child = Node4(partialKey: childKey)
        child.value = rid
        node.children[nextByte] = child
        nodeCount += 1
        return node
    }
}
```

**Analysis:**
- **Partial Key Check**: Verify common prefix match
- **Key Length Check**: Ensure key is long enough
- **Complete Key**: Handle complete key match
- **Child Navigation**: Navigate to existing child
- **Child Creation**: Create new child if needed
- **Node Splitting**: Handle node splitting

## LSM-Tree Index

### Class Structure

```swift
public final class LSMTreeIndex {
    private var memTable: MemTable
    private var sstables: [SSTable] = []
    private let maxMemTableSize: Int
    private let maxSSTableSize: Int
    private let mergeThreshold: Int
    
    public init(maxMemTableSize: Int = 64 * 1024 * 1024, // 64MB
                maxSSTableSize: Int = 256 * 1024 * 1024, // 256MB
                mergeThreshold: Int = 10) {
        self.maxMemTableSize = maxMemTableSize
        self.maxSSTableSize = maxSSTableSize
        self.mergeThreshold = mergeThreshold
        self.memTable = MemTable()
    }
}
```

**Detailed Analysis:**

#### Core Configuration
- **`memTable: MemTable`**: In-memory table for writes
- **`sstables: [SSTable]`**: Sorted string tables for persistence
- **`maxMemTableSize: Int`**: Maximum size before flush (64MB)
- **`maxSSTableSize: Int`**: Maximum size before merge (256MB)
- **`mergeThreshold: Int`**: Number of SSTables before merge (10)

#### Memory Management
- **MemTable**: Fast in-memory writes
- **SSTables**: Persistent sorted data
- **Size Limits**: Prevent excessive memory usage
- **Merge Threshold**: Control compaction frequency

### MemTable Implementation

```swift
struct MemTable {
    private var data: [String: RID] = [:]
    private var size: Int = 0
    
    mutating func insert(key: String, rid: RID) {
        data[key] = rid
        size += key.count + 8 // Key length + RID size
    }
    
    mutating func delete(key: String) {
        data[key] = nil
        size += key.count + 8 // Key length + RID size
    }
    
    func search(key: String) -> RID? {
        return data[key]
    }
    
    func flush() -> [SSTable] {
        let sortedKeys = data.keys.sorted()
        var sstables: [SSTable] = []
        
        for key in sortedKeys {
            if let rid = data[key] {
                sstables.append(SSTable(key: key, rid: rid))
            }
        }
        
        return sstables
    }
}
```

**Detailed Analysis:**

#### Data Structure
- **`data: [String: RID]`**: Dictionary for key-value storage
- **`size: Int`**: Current size in bytes
- **Performance**: O(1) for insert, delete, search
- **Memory**: O(n) where n is number of keys

#### Operations
- **Insert**: Add key-value pair
- **Delete**: Remove key-value pair
- **Search**: Find value for key
- **Flush**: Convert to SSTables

#### Size Tracking
- **Key Length**: Track key length for size calculation
- **RID Size**: Track RID size (8 bytes)
- **Total Size**: Sum of all key-value sizes
- **Flush Trigger**: Flush when size exceeds limit

### SSTable Implementation

```swift
struct SSTable {
    let key: String
    let rid: RID
    let timestamp: UInt64
    
    init(key: String, rid: RID) {
        self.key = key
        self.rid = rid
        self.timestamp = UInt64(Date().timeIntervalSince1970 * 1000)
    }
}
```

**Analysis:**
- **Key**: String key
- **RID**: Record identifier
- **Timestamp**: Creation timestamp
- **Purpose**: Persistent storage unit

### LSM-Tree Operations

#### Insert Operation

```swift
public func insert(key: String, rid: RID) {
    memTable.insert(key: key, rid: rid)
    
    if memTable.size > maxMemTableSize {
        flushMemTable()
    }
}
```

**Analysis:**
- **MemTable Insert**: Insert into in-memory table
- **Size Check**: Check if size exceeds limit
- **Flush**: Flush to SSTables if needed
- **Performance**: O(1) for insert, O(n) for flush

#### Search Operation

```swift
public func search(key: String) -> RID? {
    // Search memTable first
    if let rid = memTable.search(key: key) {
        return rid
    }
    
    // Search SSTables in reverse order (newest first)
    for sstable in sstables.reversed() {
        if let rid = sstable.search(key: key) {
            return rid
        }
    }
    
    return nil
}
```

**Analysis:**
- **MemTable Search**: Search in-memory table first
- **SSTable Search**: Search persistent tables
- **Reverse Order**: Search newest SSTables first
- **Performance**: O(1) for memTable, O(n) for SSTables

#### Flush Operation

```swift
private func flushMemTable() {
    let newSSTables = memTable.flush()
    sstables.append(contentsOf: newSSTables)
    memTable = MemTable()
    
    if sstables.count >= mergeThreshold {
        mergeSSTables()
    }
}
```

**Analysis:**
- **MemTable Flush**: Convert memTable to SSTables
- **SSTable Addition**: Add new SSTables to list
- **MemTable Reset**: Create new empty memTable
- **Merge Check**: Check if merge is needed

#### Merge Operation

```swift
private func mergeSSTables() {
    let sortedSSTables = sstables.sorted { $0.timestamp < $1.timestamp }
    var merged: [SSTable] = []
    var current: [SSTable] = []
    
    for sstable in sortedSSTables {
        current.append(sstable)
        
        if current.count >= mergeThreshold {
            let mergedSSTable = mergeSSTableGroup(current)
            merged.append(mergedSSTable)
            current = []
        }
    }
    
    if !current.isEmpty {
        let mergedSSTable = mergeSSTableGroup(current)
        merged.append(mergedSSTable)
    }
    
    sstables = merged
}
```

**Analysis:**
- **Sorting**: Sort SSTables by timestamp
- **Grouping**: Group SSTables for merging
- **Merging**: Merge each group
- **Replacement**: Replace old SSTables with merged ones

## Performance Characteristics

### B+Tree Performance

| Operation | Time Complexity | Space Complexity | Best For |
|-----------|----------------|------------------|----------|
| Search | O(log n) | O(n) | Range queries |
| Insert | O(log n) | O(n) | Balanced workloads |
| Delete | O(log n) | O(n) | Balanced workloads |
| Range Scan | O(log n + k) | O(n) | Range queries |

### ART Performance

| Operation | Time Complexity | Space Complexity | Best For |
|-----------|----------------|------------------|----------|
| Search | O(k) | O(n) | String prefix searches |
| Insert | O(k) | O(n) | String operations |
| Delete | O(k) | O(n) | String operations |
| Prefix Scan | O(k + m) | O(n) | String prefix queries |

### LSM-Tree Performance

| Operation | Time Complexity | Space Complexity | Best For |
|-----------|----------------|------------------|----------|
| Insert | O(1) | O(n) | Write-heavy workloads |
| Search | O(n) | O(n) | Read-light workloads |
| Delete | O(1) | O(n) | Write-heavy workloads |
| Range Scan | O(n) | O(n) | Read-light workloads |

## Design Decisions

### Why B+Tree for General Purpose?

- **Balanced**: O(log n) operations
- **Range Queries**: Excellent for range scans
- **Memory**: Good memory utilization
- **Persistence**: Easy to persist to disk

### Why ART for String Operations?

- **Prefix Compression**: Efficient for similar strings
- **Cache Friendly**: Good cache locality
- **Memory**: Efficient memory usage
- **Performance**: O(k) operations

### Why LSM-Tree for Write-Heavy Workloads?

- **Write Performance**: O(1) writes
- **Memory**: Efficient memory usage
- **Persistence**: Good for persistent storage
- **Compaction**: Automatic data compaction

## Future Optimizations

### SIMD Operations

- **Key Comparison**: Use SIMD for key comparison
- **Search**: Use SIMD for search operations
- **Performance**: Significant speedup for large keys
- **Complexity**: More complex implementation

### Compression

- **Node Compression**: Compress nodes in memory
- **Key Compression**: Compress keys for storage
- **Space**: Reduce memory usage
- **CPU**: Trade CPU for memory

### Parallel Operations

- **Parallel Search**: Search multiple nodes in parallel
- **Parallel Insert**: Insert multiple keys in parallel
- **Performance**: Better utilization of multiple cores
- **Complexity**: More complex synchronization

---

*This analysis provides a comprehensive understanding of ColibrìDB's index structures. For specific implementation details, see the corresponding source files.*

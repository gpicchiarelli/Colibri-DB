# Buffer Management Internals

## Overview

The buffer management system in ColibrìDB is responsible for caching frequently accessed pages in memory, implementing various eviction policies, and managing dirty page writes. This chapter provides a detailed analysis of the LRU buffer pool implementation, memory management strategies, and performance optimizations.

## LRU Buffer Pool Architecture

### Class Structure

```swift
public final class LRUBufferPool: BufferPoolProtocol {
    public enum EvictionPolicy { case lru, clock, lru2 }
    /// Total buffer size in bytes (`capacityPages * pageSize`).
    public var sizeBytes: UInt64 { UInt64(capacityPages * pageSize) }

    private let pageSize: Int
    private let capacityPages: Int
    private let fetch: (PageID) throws -> Data
    private let flush: (PageID, Data) throws -> Void

    private struct Entry { var data: Data }
    private var map: [PageID: Entry] = [:]
    private var order: [PageID] = [] // MRU at end
    private var dirty: Set<PageID> = []
    private var pins: [PageID: Int] = []
    private let namespace: String
    private var group: String { namespace.split(separator: ":").map(String.init).first ?? namespace }
    private var deferredWrite: Bool
    private var maxDirty: Int
    private var flusher: DispatchSourceTimer?
    private let q: DispatchQueue
    private var policy: EvictionPolicy = .lru
    // Clock policy state
    private var refBit: [PageID: Bool] = [:]
    private var hand: Int = 0
    // LRU-2 approximate state
    private var tick: UInt64 = 1
    private var last1: [PageID: UInt64] = [:]
    private var last2: [PageID: UInt64] = [:]
}
```

**Detailed Analysis:**

#### Core Configuration
- **`pageSize: Int`**: Fixed page size in bytes (typically 8KB)
- **`capacityPages: Int`**: Maximum number of pages in the pool
- **`sizeBytes: UInt64`**: Total buffer size in bytes (computed property)
- **`namespace: String`**: Quota namespace for resource management

#### I/O Callbacks
- **`fetch: (PageID) throws -> Data`**: Callback to fetch page from storage
- **`flush: (PageID, Data) throws -> Void`**: Callback to flush page to storage
- **Design**: Callbacks enable pluggable storage backends
- **Error Handling**: Throws errors for I/O failures

#### Data Structures

##### `Entry` Struct
```swift
private struct Entry { var data: Data }
```
- **Purpose**: Wraps page data for storage
- **Size**: Variable (Data is reference type)
- **Memory**: Data is stored on heap
- **Performance**: O(1) access to page data

##### `map: [PageID: Entry]`
- **Purpose**: Maps page IDs to page data
- **Key**: PageID (UInt64)
- **Value**: Entry struct
- **Performance**: O(1) average case lookup
- **Memory**: O(n) where n is number of pages

##### `order: [PageID]`
- **Purpose**: Maintains access order for LRU eviction
- **Order**: MRU (Most Recently Used) at end
- **Performance**: O(1) for append, O(n) for removal
- **Memory**: O(n) where n is number of pages

##### `dirty: Set<PageID>`
- **Purpose**: Tracks pages that have been modified
- **Type**: Set for O(1) lookup and insertion
- **Performance**: O(1) for dirty check
- **Memory**: O(n) where n is number of dirty pages

##### `pins: [PageID: Int]`
- **Purpose**: Tracks pin count for each page
- **Key**: PageID
- **Value**: Pin count (Int)
- **Performance**: O(1) for pin operations
- **Memory**: O(n) where n is number of pinned pages

#### Eviction Policies

##### LRU (Least Recently Used)
- **Default Policy**: Most common eviction policy
- **Algorithm**: Evicts least recently used page
- **Implementation**: Uses `order` array for access tracking
- **Performance**: O(1) for access, O(n) for eviction

##### Clock Policy
- **State Variables**: `refBit: [PageID: Bool]`, `hand: Int`
- **Algorithm**: Circular scan with reference bits
- **Performance**: O(1) for access, O(n) worst case for eviction
- **Memory**: O(n) for reference bits

##### LRU-2 (Least Recently Used with 2 References)
- **State Variables**: `tick: UInt64`, `last1: [PageID: UInt64]`, `last2: [PageID: UInt64]`
- **Algorithm**: Tracks two most recent access times
- **Performance**: O(1) for access, O(n) for eviction
- **Memory**: O(n) for access time tracking

### Initialization

```swift
public init(pageSize: Int,
            capacityPages: Int,
            fetch: @escaping (PageID) throws -> Data,
            flush: @escaping (PageID, Data) throws -> Void,
            namespace: String = "default",
            deferredWrite: Bool = false,
            maxDirty: Int = 1024,
            flushQoS: DispatchQoS = .utility) {
    self.pageSize = pageSize
    self.capacityPages = max(1, capacityPages)
    self.fetch = fetch
    self.flush = flush
    self.namespace = namespace
    self.deferredWrite = deferredWrite
    self.maxDirty = maxDirty
    self.q = DispatchQueue(label: "LRUBufferPool.\(UUID().uuidString)", qos: flushQoS)
    BufferNamespaceManager.shared.register(self)
}
```

**Detailed Analysis:**

#### Parameter Validation
- **`capacityPages`**: Ensures at least 1 page capacity
- **`pageSize`**: Must be positive (validated by caller)
- **`maxDirty`**: Threshold for dirty page flushing
- **`namespace`**: Used for quota management

#### Queue Creation
- **Label**: Unique label with UUID for debugging
- **QoS**: Configurable quality of service
- **Purpose**: Background flushing operations
- **Thread Safety**: Serializes buffer pool operations

#### Namespace Registration
- **`BufferNamespaceManager.shared.register(self)`**: Registers pool for quota management
- **Purpose**: Enables resource management across pools
- **Cleanup**: Automatically unregistered in deinit

### Page Access Operations

#### Get Page (Read)

```swift
/// Reads a page without pinning it.
public func getPage(_ id: PageID) throws -> Data {
    if let e = map[id] {
        hits &+= 1
        touch(id)
        return e.data
    }
    misses &+= 1
    let data = try fetch(id)
    insert(id, data)
    return data
}
```

**Detailed Analysis:**

#### Hit Path
1. **Lookup**: Check if page exists in map
2. **Hit Count**: Increment hit counter
3. **Touch**: Update access order
4. **Return**: Return cached data

#### Miss Path
1. **Miss Count**: Increment miss counter
2. **Fetch**: Load page from storage
3. **Insert**: Add page to buffer pool
4. **Return**: Return fetched data

#### Performance
- **Hit Case**: O(1) lookup + O(n) touch operation
- **Miss Case**: O(1) lookup + O(n) insert operation
- **Total Time**: O(n) where n is number of pages
- **Memory**: No additional allocations

#### Touch Operation
```swift
private func touch(_ id: PageID) {
    // Remove from current position
    if let index = order.firstIndex(of: id) {
        order.remove(at: index)
    }
    // Add to end (MRU position)
    order.append(id)
}
```

**Analysis:**
- **Removal**: O(n) linear search and removal
- **Append**: O(1) append to end
- **Total Time**: O(n) where n is number of pages
- **Memory**: No additional allocations

#### Insert Operation
```swift
private func insert(_ id: PageID, _ data: Data) {
    // Check if we need to evict
    if map.count >= capacityPages {
        evict()
    }
    
    // Insert page
    map[id] = Entry(data: data)
    order.append(id)
    
    // Update eviction policy state
    updateEvictionState(id)
}
```

**Analysis:**
- **Eviction Check**: O(1) count check
- **Eviction**: O(n) eviction operation
- **Insertion**: O(1) map insertion + O(1) order append
- **State Update**: O(1) eviction policy update
- **Total Time**: O(n) where n is number of pages

#### Put Page (Write)

```swift
/// Inserts or updates a page, optionally marking it dirty.
public func putPage(_ id: PageID, data: Data, dirty isDirty: Bool) throws {
    let existed = map[id] != nil
    map[id] = Entry(data: data)
    touchInsert(id)
    
    if isDirty {
        dirty.insert(id)
        if deferredWrite {
            scheduleFlushIfNeeded()
        } else {
            try flush(id, data)
        }
    }
}
```

**Detailed Analysis:**

#### Update Process
1. **Existence Check**: Check if page already exists
2. **Data Update**: Update page data in map
3. **Touch Insert**: Update access order
4. **Dirty Marking**: Mark page as dirty if needed
5. **Flush Decision**: Immediate or deferred flush

#### Dirty Page Management
- **`dirty.insert(id)`**: Add page to dirty set
- **`deferredWrite`**: Controls flush timing
- **`scheduleFlushIfNeeded()`**: Triggers background flush
- **Immediate Flush**: Flushes page immediately

#### Performance
- **Update**: O(1) map update + O(n) touch operation
- **Dirty Marking**: O(1) set insertion
- **Flush**: O(1) for immediate, O(1) for scheduling
- **Total Time**: O(n) where n is number of pages

### Eviction Policies

#### LRU Eviction

```swift
private func evict() {
    guard !order.isEmpty else { return }
    
    // Find unpinned page to evict
    var index = 0
    while index < order.count {
        let id = order[index]
        if pins[id] == nil || pins[id] == 0 {
            // Evict this page
            evictPage(id)
            return
        }
        index += 1
    }
    
    // No unpinned pages found
    // This is a critical error - all pages are pinned
    fatalError("All pages are pinned, cannot evict")
}
```

**Detailed Analysis:**

#### Eviction Process
1. **Order Check**: Ensure order array is not empty
2. **Pin Check**: Find first unpinned page
3. **Eviction**: Evict the selected page
4. **Error Handling**: Fatal error if all pages are pinned

#### Pin Management
- **`pins[id] == nil`**: Page is not pinned
- **`pins[id] == 0`**: Page is pinned but count is 0
- **Pin Count**: Tracks number of active references
- **Eviction**: Only evicts unpinned pages

#### Performance
- **Linear Search**: O(n) where n is number of pages
- **Pin Check**: O(1) for each page
- **Eviction**: O(n) for removal from order array
- **Total Time**: O(n) where n is number of pages

#### Evict Page
```swift
private func evictPage(_ id: PageID) {
    // Remove from map
    map.removeValue(forKey: id)
    
    // Remove from order
    if let index = order.firstIndex(of: id) {
        order.remove(at: index)
    }
    
    // Remove from dirty set
    dirty.remove(id)
    
    // Remove pin count
    pins.removeValue(forKey: id)
    
    // Update eviction policy state
    updateEvictionStateOnEvict(id)
    
    // Increment eviction counter
    evictions &+= 1
}
```

**Analysis:**
- **Map Removal**: O(1) average case
- **Order Removal**: O(n) linear search and removal
- **Dirty Removal**: O(1) set removal
- **Pin Removal**: O(1) map removal
- **State Update**: O(1) eviction policy update
- **Total Time**: O(n) where n is number of pages

#### Clock Eviction

```swift
private func evictClock() {
    guard !map.isEmpty else { return }
    
    let pageIds = Array(map.keys)
    let startIndex = hand
    
    while true {
        let id = pageIds[hand]
        
        if pins[id] == nil || pins[id] == 0 {
            // Check reference bit
            if refBit[id] == true {
                // Clear reference bit and continue
                refBit[id] = false
            } else {
                // Evict this page
                evictPage(id)
                hand = (hand + 1) % pageIds.count
                return
            }
        }
        
        hand = (hand + 1) % pageIds.count
        
        // Prevent infinite loop
        if hand == startIndex {
            // All pages are pinned or have reference bits set
            // Clear all reference bits and try again
            for pageId in pageIds {
                refBit[pageId] = false
            }
        }
    }
}
```

**Detailed Analysis:**

#### Clock Algorithm
1. **Circular Scan**: Scan pages in circular order
2. **Reference Bit Check**: Check if page was recently accessed
3. **Bit Clearing**: Clear reference bit if set
4. **Eviction**: Evict page if reference bit is clear
5. **Loop Prevention**: Prevent infinite loops

#### Reference Bit Management
- **`refBit[id] == true`**: Page was recently accessed
- **`refBit[id] == false`**: Page was not recently accessed
- **Bit Clearing**: Clears reference bit on second pass
- **Eviction**: Only evicts pages with clear reference bits

#### Performance
- **Best Case**: O(1) if first page can be evicted
- **Worst Case**: O(n) if all pages have reference bits set
- **Average Case**: O(n/2) for typical workloads
- **Memory**: O(n) for reference bit storage

#### LRU-2 Eviction

```swift
private func evictLRU2() {
    guard !map.isEmpty else { return }
    
    var bestPage: PageID?
    var bestTime: UInt64 = UInt64.max
    
    for (id, _) in map {
        if pins[id] == nil || pins[id] == 0 {
            // Calculate LRU-2 time
            let time1 = last1[id] ?? 0
            let time2 = last2[id] ?? 0
            let lru2Time = min(time1, time2)
            
            if lru2Time < bestTime {
                bestTime = lru2Time
                bestPage = id
            }
        }
    }
    
    if let pageId = bestPage {
        evictPage(pageId)
    }
}
```

**Detailed Analysis:**

#### LRU-2 Algorithm
1. **Time Calculation**: Calculate LRU-2 time for each page
2. **Best Page**: Find page with smallest LRU-2 time
3. **Eviction**: Evict the selected page
4. **Time Tracking**: Tracks two most recent access times

#### Time Tracking
- **`last1[id]`**: First most recent access time
- **`last2[id]`**: Second most recent access time
- **`lru2Time`**: Minimum of the two times
- **Eviction**: Evicts page with smallest LRU-2 time

#### Performance
- **Linear Scan**: O(n) where n is number of pages
- **Time Calculation**: O(1) for each page
- **Best Page Selection**: O(1) comparison
- **Total Time**: O(n) where n is number of pages

### Pin Management

#### Pin Page

```swift
/// Pins a page to prevent eviction.
public func pinPage(_ id: PageID) {
    pins[id] = (pins[id] ?? 0) + 1
}
```

**Analysis:**
- **Pin Count**: Increments pin count for page
- **Initialization**: Sets count to 1 if not pinned
- **Increment**: Adds 1 to existing count
- **Performance**: O(1) operation

#### Unpin Page

```swift
/// Unpins a page, allowing eviction.
public func unpinPage(_ id: PageID) {
    if let count = pins[id] {
        if count <= 1 {
            pins.removeValue(forKey: id)
        } else {
            pins[id] = count - 1
        }
    }
}
```

**Analysis:**
- **Pin Count**: Decrements pin count for page
- **Removal**: Removes pin if count reaches 0
- **Decrement**: Subtracts 1 from existing count
- **Performance**: O(1) operation

### Dirty Page Management

#### Schedule Flush

```swift
private func scheduleFlushIfNeeded() {
    guard dirty.count >= maxDirty else { return }
    
    if flusher == nil {
        flusher = DispatchSource.makeTimerSource(queue: q)
        flusher?.schedule(deadline: .now(), repeating: .milliseconds(100))
        flusher?.setEventHandler { [weak self] in
            self?.flushDirtyPages()
        }
        flusher?.resume()
    }
}
```

**Detailed Analysis:**

#### Flush Triggering
- **Threshold Check**: Triggers when dirty count >= maxDirty
- **Timer Creation**: Creates background timer
- **Schedule**: Runs every 100ms
- **Event Handler**: Calls flushDirtyPages()

#### Timer Management
- **`DispatchSource.makeTimerSource`**: Creates timer source
- **`schedule(deadline:repeating:)`**: Schedules recurring execution
- **`setEventHandler`**: Sets callback function
- **`resume()`**: Starts timer execution

#### Flush Dirty Pages

```swift
private func flushDirtyPages() {
    let dirtyPages = Array(dirty)
    
    for pageId in dirtyPages {
        if let entry = map[pageId] {
            do {
                try flush(pageId, entry.data)
                dirty.remove(pageId)
            } catch {
                // Log error but continue with other pages
                print("Failed to flush page \(pageId): \(error)")
            }
        }
    }
    
    // Stop timer if no more dirty pages
    if dirty.isEmpty {
        flusher?.cancel()
        flusher = nil
    }
}
```

**Detailed Analysis:**

#### Flush Process
1. **Dirty List**: Get list of dirty pages
2. **Flush Loop**: Flush each dirty page
3. **Error Handling**: Continue on individual page errors
4. **Cleanup**: Remove flushed pages from dirty set
5. **Timer Management**: Stop timer if no dirty pages

#### Error Handling
- **Individual Errors**: Log but continue with other pages
- **Flush Success**: Remove page from dirty set
- **Flush Failure**: Keep page in dirty set for retry
- **Timer Cleanup**: Stop timer when no dirty pages

### Metrics and Monitoring

#### Hit Rate Calculation

```swift
public var hitRate: Double {
    let total = hits + misses
    return total > 0 ? Double(hits) / Double(total) : 0.0
}
```

**Analysis:**
- **Total Requests**: hits + misses
- **Hit Rate**: hits / total
- **Zero Division**: Returns 0.0 if no requests
- **Performance**: O(1) calculation

#### Memory Usage

```swift
public var memoryUsage: UInt64 {
    UInt64(map.count * pageSize)
}
```

**Analysis:**
- **Page Count**: Number of pages in map
- **Page Size**: Size of each page
- **Total Memory**: count × pageSize
- **Performance**: O(1) calculation

#### Dirty Page Count

```swift
public var dirtyPageCount: Int {
    dirty.count
}
```

**Analysis:**
- **Dirty Count**: Number of dirty pages
- **Set Size**: O(1) count operation
- **Performance**: O(1) calculation

## Performance Characteristics

### Time Complexity

| Operation | LRU | Clock | LRU-2 |
|-----------|-----|-------|-------|
| Get Page | O(n) | O(1) | O(1) |
| Put Page | O(n) | O(1) | O(1) |
| Eviction | O(n) | O(n) | O(n) |
| Touch | O(n) | O(1) | O(1) |

### Space Complexity

| Component | Space | Purpose |
|-----------|-------|---------|
| Map | O(n) | Page storage |
| Order | O(n) | Access tracking |
| Dirty | O(n) | Dirty page tracking |
| Pins | O(n) | Pin count tracking |
| Ref Bits | O(n) | Clock policy state |
| Access Times | O(n) | LRU-2 policy state |

### Memory Usage

| Policy | Overhead | Best For |
|--------|----------|----------|
| LRU | Low | General purpose |
| Clock | Medium | High concurrency |
| LRU-2 | High | Complex access patterns |

## Design Decisions

### Why LRU as Default?

- **Simplicity**: Easy to understand and implement
- **Performance**: Good for most workloads
- **Memory**: Low overhead
- **Predictability**: Predictable eviction behavior

### Why Clock Policy?

- **Concurrency**: Better for high concurrency
- **Performance**: O(1) access operations
- **Memory**: Moderate overhead
- **Fairness**: More fair than LRU

### Why LRU-2?

- **Complexity**: Handles complex access patterns
- **Performance**: O(1) access operations
- **Memory**: High overhead
- **Accuracy**: More accurate than LRU

### Why Deferred Writes?

- **Performance**: Reduces I/O operations
- **Batching**: Batches multiple writes
- **Throughput**: Improves write throughput
- **Complexity**: Adds complexity to error handling

## Future Optimizations

### SIMD Operations

- **Search**: Use SIMD for page searching
- **Comparison**: Use SIMD for page comparison
- **Copying**: Use SIMD for page copying
- **Performance**: Significant speedup for large pages

### Memory Mapping

- **Zero Copy**: Avoid copying page data
- **Performance**: Faster page access
- **Complexity**: More complex error handling
- **Memory**: Better memory utilization

### Compression

- **Page Compression**: Compress pages in memory
- **Space**: Reduce memory usage
- **CPU**: Trade CPU for memory
- **Performance**: Slower access but less memory

### Predictive Prefetching

- **Access Patterns**: Learn from access patterns
- **Prefetching**: Prefetch likely-to-be-accessed pages
- **Performance**: Reduce miss rate
- **Complexity**: More complex implementation

---

*This analysis provides a comprehensive understanding of ColibrìDB's buffer management system. For specific implementation details, see the corresponding source files.*

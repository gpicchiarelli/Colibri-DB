# Storage Layer Internals

## Overview

The storage layer in ColibrìDB is responsible for persistent data storage, page management, and I/O operations. This chapter provides a detailed analysis of the page structure, memory layout, and storage algorithms.

## Page Structure

### Page Header

```swift
/// Page header with metadata, free space pointers and checksum.
struct PageHeader {
    var magic: UInt32 = 0x434F4C49 // 'COLI'
    var pageId: UInt64
    var pageLSN: UInt64
    var freeStart: UInt16 // offset where free space starts (grows upward)
    var freeEnd: UInt16   // offset where free space ends (grows downward)
    var slotCount: UInt16
    var checksum: UInt32 // CRC32 of the whole page with this field zeroed
}
```

**Detailed Analysis:**

#### Memory Layout
```
Page Header Layout (32 bytes):
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Magic       │ Page ID     │ Page LSN    │ Free Start  │
│ (4 bytes)   │ (8 bytes)   │ (8 bytes)   │ (2 bytes)   │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Free End    │ Slot Count  │ Padding     │ Checksum    │
│ (2 bytes)   │ (2 bytes)   │ (2 bytes)   │ (4 bytes)   │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

#### Field Analysis

##### `magic: UInt32 = 0x434F4C49`
- **Value**: 0x434F4C49 ('COLI' in ASCII)
- **Purpose**: Page format identification and corruption detection
- **Size**: 4 bytes
- **Alignment**: 4-byte aligned
- **Usage**: First field checked during page validation
- **Performance**: O(1) validation check

##### `pageId: UInt64`
- **Purpose**: Unique page identifier within the database
- **Size**: 8 bytes
- **Alignment**: 8-byte aligned
- **Range**: 0 to 18,446,744,073,709,551,615
- **Usage**: Page location and identification
- **Performance**: O(1) page lookup

##### `pageLSN: UInt64`
- **Purpose**: Log Sequence Number for WAL recovery
- **Size**: 8 bytes
- **Alignment**: 8-byte aligned
- **Range**: 0 to 18,446,744,073,709,551,615
- **Usage**: ARIES recovery algorithm
- **Performance**: O(1) LSN comparison

##### `freeStart: UInt16`
- **Purpose**: Offset where free space starts (grows upward)
- **Size**: 2 bytes
- **Alignment**: 2-byte aligned
- **Range**: 0 to 65,535
- **Usage**: Free space management
- **Performance**: O(1) free space calculation

##### `freeEnd: UInt16`
- **Purpose**: Offset where free space ends (grows downward)
- **Size**: 2 bytes
- **Alignment**: 2-byte aligned
- **Range**: 0 to 65,535
- **Usage**: Free space management
- **Performance**: O(1) free space calculation

##### `slotCount: UInt16`
- **Purpose**: Number of slots in the slot directory
- **Size**: 2 bytes
- **Alignment**: 2-byte aligned
- **Range**: 0 to 65,535
- **Usage**: Slot directory management
- **Performance**: O(1) slot count access

##### `checksum: UInt32`
- **Purpose**: CRC32 checksum for corruption detection
- **Size**: 4 bytes
- **Alignment**: 4-byte aligned
- **Algorithm**: CRC32 with zeroed checksum field
- **Usage**: Page integrity validation
- **Performance**: O(n) where n is page size

### Page Slot

```swift
struct PageSlot { // 4 bytes
    var offset: UInt16
    var length: UInt16
}
```

**Detailed Analysis:**

#### Memory Layout
```
Page Slot Layout (4 bytes):
┌─────────────┬─────────────┐
│ Offset      │ Length      │
│ (2 bytes)   │ (2 bytes)   │
└─────────────┴─────────────┘
```

#### Field Analysis

##### `offset: UInt16`
- **Purpose**: Offset within the page where the record starts
- **Size**: 2 bytes
- **Alignment**: 2-byte aligned
- **Range**: 0 to 65,535
- **Usage**: Record location within page
- **Performance**: O(1) record access

##### `length: UInt16`
- **Purpose**: Length of the record in bytes
- **Size**: 2 bytes
- **Alignment**: 2-byte aligned
- **Range**: 0 to 65,535
- **Usage**: Record size calculation
- **Performance**: O(1) record size access

### Page Structure

```swift
/// In-memory representation of a database page.
struct Page {
    static let headerSize = 32
    static let slotSize = 4

    let pageSize: Int
    var header: PageHeader
    var data: Data // always pageSize bytes
}
```

**Detailed Analysis:**

#### Constants
- **`headerSize = 32`**: Size of page header in bytes
- **`slotSize = 4`**: Size of each slot in bytes
- **`pageSize`**: Total page size (typically 8KB)

#### Fields
- **`pageSize: Int`**: Total page size in bytes
- **`header: PageHeader`**: Page header structure
- **`data: Data`**: Raw page data (always pageSize bytes)

#### Memory Layout
```
Page Layout (8KB typical):
┌─────────────────────────────────────────────────────────┐
│ Header (32 bytes)                                      │
├─────────────────────────────────────────────────────────┤
│ Slot Directory (4 bytes × slotCount)                  │
├─────────────────────────────────────────────────────────┤
│ Free Space (grows upward from freeStart)               │
├─────────────────────────────────────────────────────────┤
│ Records (grows downward from freeEnd)                  │
└─────────────────────────────────────────────────────────┘
```

## Page Operations

### Page Initialization

```swift
/// Initializes a fresh page with the given id and size.
init(pageId: UInt64, pageSize: Int) {
    self.pageSize = pageSize
    let header = PageHeader(pageId: pageId,
                            pageLSN: 0,
                            freeStart: UInt16(Page.headerSize),
                            freeEnd: UInt16(pageSize),
                            slotCount: 0,
                            checksum: 0)
    self.header = header
    self.data = Data(repeating: 0, count: pageSize)
    writeHeader()
}
```

**Detailed Analysis:**

#### Initialization Process
1. **Set Page Size**: Store the page size for later use
2. **Create Header**: Initialize header with default values
3. **Allocate Data**: Create zero-initialized data buffer
4. **Write Header**: Serialize header to data buffer

#### Header Initialization
- **`pageId`**: Set to provided page ID
- **`pageLSN`**: Set to 0 (no WAL operations yet)
- **`freeStart`**: Set to header size (32 bytes)
- **`freeEnd`**: Set to page size (end of page)
- **`slotCount`**: Set to 0 (no slots yet)
- **`checksum`**: Set to 0 (will be calculated)

#### Data Initialization
- **`Data(repeating: 0, count: pageSize)`**: Creates zero-initialized buffer
- **Size**: Always exactly pageSize bytes
- **Alignment**: Data is aligned to page boundaries
- **Performance**: O(1) allocation

### Page Deserialization

```swift
/// Initializes a page from raw bytes, validating magic and checksum.
init?(from raw: Data, pageSize: Int) {
    guard raw.count == pageSize else { return nil }
    self.pageSize = pageSize
    self.data = raw
    guard let hdr = Page.readHeader(from: raw) else { return nil }
    // verify magic and checksum
    guard hdr.magic == 0x434F4C49 else { return nil }
    if !CRC32.verify(data: data, checksumOffset: 28) { return nil }
    self.header = hdr
}
```

**Detailed Analysis:**

#### Validation Process
1. **Size Check**: Ensure raw data matches expected page size
2. **Header Read**: Deserialize header from raw data
3. **Magic Check**: Verify page format identifier
4. **Checksum Check**: Verify page integrity

#### Error Handling
- **Size Mismatch**: Returns nil if data size doesn't match page size
- **Header Read Failure**: Returns nil if header deserialization fails
- **Magic Mismatch**: Returns nil if page format is invalid
- **Checksum Failure**: Returns nil if page is corrupted

#### Performance
- **Size Check**: O(1) operation
- **Header Read**: O(1) operation
- **Magic Check**: O(1) operation
- **Checksum Check**: O(n) where n is page size

### Header Serialization

```swift
/// Encodes header fields into `data` and updates the checksum.
mutating func writeHeader() {
    // encode header fields
    data.withUnsafeMutableBytes { buf in
        var off = 0
        func put<T>(_ v: T) {
            var val = v
            let sz = MemoryLayout<T>.size
            withUnsafeBytes(of: &val) { src in
                buf.baseAddress!.advanced(by: off).copyMemory(from: src.baseAddress!, byteCount: sz)
            }
            off += sz
        }
        put(header.magic)
        put(header.pageId)
        put(header.pageLSN)
        put(header.freeStart)
        put(header.freeEnd)
        put(header.slotCount)
        put(UInt16(0)) // padding to reach 28 bytes
        put(header.checksum)
    }
    // update checksum
    header.checksum = CRC32.computeWithZeroedChecksum(data: &data, checksumOffset: 28)
    data.withUnsafeMutableBytes { buf in
        var c = header.checksum
        withUnsafeBytes(of: &c) { src in
            buf.baseAddress!.advanced(by: 28).copyMemory(from: src.baseAddress!, byteCount: 4)
        }
    }
}
```

**Detailed Analysis:**

#### Serialization Process
1. **Get Mutable Buffer**: Access raw bytes of data buffer
2. **Serialize Fields**: Write each header field in order
3. **Add Padding**: Add padding to reach 28 bytes
4. **Calculate Checksum**: Compute CRC32 checksum
5. **Write Checksum**: Write checksum to data buffer

#### Field Serialization
- **`put<T>(_ v: T)`**: Generic function for writing any type
- **`MemoryLayout<T>.size`**: Get size of type at compile time
- **`withUnsafeBytes`**: Access raw bytes of value
- **`copyMemory`**: Copy bytes to buffer
- **`off += sz`**: Advance offset by field size

#### Checksum Calculation
- **`CRC32.computeWithZeroedChecksum`**: Calculate checksum with checksum field zeroed
- **`checksumOffset: 28`**: Checksum field is at offset 28
- **Zeroed Field**: Checksum field is set to 0 during calculation
- **Final Write**: Checksum is written after calculation

#### Performance
- **Field Serialization**: O(1) for each field
- **Checksum Calculation**: O(n) where n is page size
- **Total Time**: O(n) where n is page size
- **Memory**: No additional allocations

## Page Layout Management

### Free Space Management

The page uses a two-pointer system for free space management:

```
Free Space Layout:
┌─────────────────────────────────────────────────────────┐
│ Header (32 bytes)                                      │
├─────────────────────────────────────────────────────────┤
│ Slot Directory (4 bytes × slotCount)                  │
├─────────────────────────────────────────────────────────┤
│ Free Space (grows upward from freeStart)               │
│ ↑                                                      │
│ freeStart                                              │
├─────────────────────────────────────────────────────────┤
│ Records (grows downward from freeEnd)                  │
│ ↓                                                      │
│ freeEnd                                                │
└─────────────────────────────────────────────────────────┘
```

**Analysis:**
- **`freeStart`**: Points to start of free space (grows upward)
- **`freeEnd`**: Points to end of free space (grows downward)
- **Free Space**: Area between freeStart and freeEnd
- **Records**: Stored in area from freeEnd to end of page
- **Slots**: Stored in area from header to freeStart

### Slot Directory Management

The slot directory is an array of PageSlot structures:

```
Slot Directory Layout:
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Slot 0      │ Slot 1      │ Slot 2      │ ...         │
│ (4 bytes)   │ (4 bytes)   │ (4 bytes)   │ (4 bytes)   │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

**Analysis:**
- **Slot Count**: Stored in header.slotCount
- **Slot Size**: 4 bytes per slot
- **Slot Location**: After header, before free space
- **Slot Content**: Each slot contains offset and length
- **Slot Usage**: Slots are allocated as needed

### Record Storage

Records are stored in the area from freeEnd to the end of the page:

```
Record Storage Layout:
┌─────────────────────────────────────────────────────────┐
│ Record 0 (JSON encoded)                                │
├─────────────────────────────────────────────────────────┤
│ Record 1 (JSON encoded)                                │
├─────────────────────────────────────────────────────────┤
│ Record 2 (JSON encoded)                                │
├─────────────────────────────────────────────────────────┤
│ ...                                                     │
└─────────────────────────────────────────────────────────┘
```

**Analysis:**
- **Record Format**: JSON-encoded Row objects
- **Record Order**: Stored in reverse order (newest first)
- **Record Size**: Variable size based on content
- **Record Access**: Via slot directory
- **Record Deletion**: Marked as deleted, space reclaimed later

## Page Operations

### Insert Operation

```swift
/// Inserts a row into the page, returning the slot ID.
mutating func insert(row: Row) -> UInt16? {
    // Serialize row to JSON
    guard let jsonData = try? JSONEncoder().encode(row) else { return nil }
    
    // Check if there's enough space
    let requiredSpace = jsonData.count + Page.slotSize
    if freeStart + requiredSpace > freeEnd {
        return nil // Not enough space
    }
    
    // Allocate slot
    let slotId = header.slotCount
    header.slotCount += 1
    
    // Store record
    let recordOffset = freeEnd - UInt16(jsonData.count)
    data.replaceSubrange(recordOffset..<freeEnd, with: jsonData)
    
    // Update slot directory
    let slotOffset = Page.headerSize + Int(slotId) * Page.slotSize
    data.withUnsafeMutableBytes { buf in
        var slot = PageSlot(offset: recordOffset, length: UInt16(jsonData.count))
        withUnsafeBytes(of: &slot) { src in
            buf.baseAddress!.advanced(by: slotOffset).copyMemory(from: src.baseAddress!, byteCount: Page.slotSize)
        }
    }
    
    // Update free space
    freeEnd = recordOffset
    
    return slotId
}
```

**Detailed Analysis:**

#### Insert Process
1. **Serialize Row**: Convert Row to JSON data
2. **Check Space**: Verify sufficient free space
3. **Allocate Slot**: Increment slot count
4. **Store Record**: Write JSON data to page
5. **Update Slot**: Write slot information
6. **Update Free Space**: Adjust freeEnd pointer

#### Space Calculation
- **Required Space**: JSON data size + slot size
- **Available Space**: freeEnd - freeStart
- **Check**: requiredSpace <= availableSpace
- **Performance**: O(1) space check

#### Record Storage
- **Record Offset**: freeEnd - jsonData.count
- **Record Data**: JSON-encoded row
- **Slot Information**: Offset and length
- **Free Space Update**: freeEnd = recordOffset

#### Performance
- **JSON Encoding**: O(n) where n is row size
- **Space Check**: O(1)
- **Record Storage**: O(n) where n is row size
- **Slot Update**: O(1)
- **Total Time**: O(n) where n is row size

### Read Operation

```swift
/// Reads a row from the page by slot ID.
func read(slotId: UInt16) -> Row? {
    guard slotId < header.slotCount else { return nil }
    
    // Read slot information
    let slotOffset = Page.headerSize + Int(slotId) * Page.slotSize
    let slot = data.withUnsafeBytes { buf in
        buf.load(fromByteOffset: slotOffset, as: PageSlot.self)
    }
    
    // Read record data
    let recordData = data.subdata(in: Int(slot.offset)..<Int(slot.offset + slot.length))
    
    // Deserialize JSON
    return try? JSONDecoder().decode(Row.self, from: recordData)
}
```

**Detailed Analysis:**

#### Read Process
1. **Validate Slot ID**: Check if slot exists
2. **Read Slot**: Load slot information from directory
3. **Read Record**: Extract record data from page
4. **Deserialize**: Convert JSON back to Row

#### Slot Validation
- **Bounds Check**: slotId < header.slotCount
- **Performance**: O(1) validation
- **Error Handling**: Returns nil for invalid slot

#### Record Reading
- **Slot Offset**: Page.headerSize + slotId * Page.slotSize
- **Slot Load**: Load PageSlot from memory
- **Record Data**: Extract data using offset and length
- **JSON Decode**: Convert JSON back to Row

#### Performance
- **Slot Validation**: O(1)
- **Slot Reading**: O(1)
- **Record Reading**: O(n) where n is record size
- **JSON Decoding**: O(n) where n is record size
- **Total Time**: O(n) where n is record size

### Delete Operation

```swift
/// Marks a slot as deleted (space will be reclaimed during compaction).
mutating func delete(slotId: UInt16) -> Bool {
    guard slotId < header.slotCount else { return false }
    
    // Mark slot as deleted by setting offset to 0
    let slotOffset = Page.headerSize + Int(slotId) * Page.slotSize
    data.withUnsafeMutableBytes { buf in
        var slot = PageSlot(offset: 0, length: 0)
        withUnsafeBytes(of: &slot) { src in
            buf.baseAddress!.advanced(by: slotOffset).copyMemory(from: src.baseAddress!, byteCount: Page.slotSize)
        }
    }
    
    return true
}
```

**Detailed Analysis:**

#### Delete Process
1. **Validate Slot ID**: Check if slot exists
2. **Mark Deleted**: Set slot offset to 0
3. **Return Success**: Indicate deletion completed

#### Deletion Strategy
- **Logical Deletion**: Slot is marked as deleted
- **Physical Deletion**: Space is reclaimed during compaction
- **Performance**: O(1) deletion
- **Space**: No immediate space reclamation

#### Slot Marking
- **Offset = 0**: Indicates deleted slot
- **Length = 0**: Indicates deleted slot
- **Validation**: Read operations check for offset = 0
- **Compaction**: Deleted slots are removed during compaction

## Page Compaction

### Compaction Process

```swift
/// Compacts the page by removing deleted slots and defragmenting records.
mutating func compact() {
    var newSlots: [PageSlot] = []
    var newFreeStart = Page.headerSize
    
    // Collect non-deleted slots
    for i in 0..<header.slotCount {
        let slotOffset = Page.headerSize + Int(i) * Page.slotSize
        let slot = data.withUnsafeBytes { buf in
            buf.load(fromByteOffset: slotOffset, as: PageSlot.self)
        }
        
        if slot.offset != 0 { // Not deleted
            newSlots.append(slot)
        }
    }
    
    // Sort slots by offset (descending order)
    newSlots.sort { $0.offset > $1.offset }
    
    // Rebuild page
    var newFreeEnd = pageSize
    for (index, slot) in newSlots.enumerated() {
        // Read record data
        let recordData = data.subdata(in: Int(slot.offset)..<Int(slot.offset + slot.length))
        
        // Write record to new location
        let newOffset = newFreeEnd - UInt16(recordData.count)
        data.replaceSubrange(newOffset..<newFreeEnd, with: recordData)
        
        // Update slot
        let newSlot = PageSlot(offset: newOffset, length: slot.length)
        let slotOffset = Page.headerSize + Int(index) * Page.slotSize
        data.withUnsafeMutableBytes { buf in
            withUnsafeBytes(of: &newSlot) { src in
                buf.baseAddress!.advanced(by: slotOffset).copyMemory(from: src.baseAddress!, byteCount: Page.slotSize)
            }
        }
        
        newFreeEnd = newOffset
    }
    
    // Update header
    header.slotCount = UInt16(newSlots.count)
    header.freeStart = UInt16(newFreeStart)
    header.freeEnd = newFreeEnd
}
```

**Detailed Analysis:**

#### Compaction Process
1. **Collect Valid Slots**: Find all non-deleted slots
2. **Sort by Offset**: Sort slots by record offset (descending)
3. **Rebuild Records**: Move records to new locations
4. **Update Slots**: Update slot directory with new offsets
5. **Update Header**: Update free space pointers

#### Space Reclamation
- **Deleted Slots**: Removed from slot directory
- **Fragmented Space**: Consolidated into single free area
- **Record Movement**: Records moved to eliminate gaps
- **Free Space**: Maximized available space

#### Performance
- **Slot Collection**: O(n) where n is slot count
- **Sorting**: O(n log n) where n is valid slot count
- **Record Movement**: O(n) where n is total record size
- **Total Time**: O(n log n) where n is slot count

## Error Handling and Validation

### Magic Number Validation

```swift
guard hdr.magic == 0x434F4C49 else { return nil }
```

**Analysis:**
- **Magic Value**: 0x434F4C49 ('COLI' in ASCII)
- **Purpose**: Page format identification
- **Validation**: First check during page deserialization
- **Performance**: O(1) comparison
- **Error**: Returns nil for invalid format

### Checksum Validation

```swift
if !CRC32.verify(data: data, checksumOffset: 28) { return nil }
```

**Analysis:**
- **Algorithm**: CRC32 with zeroed checksum field
- **Checksum Offset**: 28 bytes from start of page
- **Validation**: Verifies page integrity
- **Performance**: O(n) where n is page size
- **Error**: Returns nil for corrupted page

### Size Validation

```swift
guard raw.count == pageSize else { return nil }
```

**Analysis:**
- **Size Check**: Ensures data matches expected page size
- **Validation**: First check during deserialization
- **Performance**: O(1) comparison
- **Error**: Returns nil for size mismatch

## Performance Characteristics

### Memory Usage

| Component | Size | Alignment | Purpose |
|-----------|------|-----------|---------|
| Header | 32 bytes | 8-byte | Page metadata |
| Slot | 4 bytes | 2-byte | Record location |
| Record | Variable | 1-byte | Actual data |
| Free Space | Variable | 1-byte | Available space |

### Access Performance

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|------------------|
| Page Creation | O(1) | O(1) |
| Page Deserialization | O(n) | O(1) |
| Record Insert | O(n) | O(1) |
| Record Read | O(n) | O(1) |
| Record Delete | O(1) | O(1) |
| Page Compaction | O(n log n) | O(1) |

### I/O Performance

- **Page Size**: 8KB typical (configurable)
- **Alignment**: Page-aligned for optimal I/O
- **Sequential Access**: Good for range scans
- **Random Access**: Good for point lookups
- **Compression**: Can be compressed for storage

## Design Decisions

### Why 8KB Page Size?

- **Memory**: Fits in L1 cache on most systems
- **I/O**: Good balance between I/O efficiency and memory usage
- **OS**: Matches typical OS page size
- **Performance**: Optimal for most workloads

### Why Slot Directory?

- **Flexibility**: Variable-length records
- **Efficiency**: O(1) record access
- **Compaction**: Easy to remove deleted records
- **Memory**: Minimal overhead per record

### Why JSON Encoding?

- **Simplicity**: Easy to implement and debug
- **Flexibility**: Handles variable schema
- **Compatibility**: Works with external tools
- **Performance**: Reasonable for most use cases

### Why Two-Pointer Free Space?

- **Efficiency**: O(1) space allocation
- **Compaction**: Easy to defragment
- **Memory**: Minimal overhead
- **Performance**: Good for most workloads

## Future Optimizations

### Compression

- **Page-Level**: Compress entire pages
- **Record-Level**: Compress individual records
- **Algorithm**: LZ4 or ZSTD for speed
- **Performance**: Trade CPU for I/O

### SIMD Operations

- **Search**: Use SIMD for record searching
- **Comparison**: Use SIMD for record comparison
- **Copying**: Use SIMD for record copying
- **Performance**: Significant speedup for large records

### Memory Mapping

- **File Mapping**: Map pages directly to memory
- **Zero Copy**: Avoid copying data
- **Performance**: Faster I/O operations
- **Complexity**: More complex error handling

---

*This analysis provides a comprehensive understanding of ColibrìDB's storage layer. For specific implementation details, see the corresponding source files.*

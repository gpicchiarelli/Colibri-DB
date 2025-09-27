# Data Types Internals

## Overview

The data types in ColibrìDB are designed for efficiency, type safety, and performance. This chapter provides a detailed analysis of the core data structures, their memory layout, serialization, and performance characteristics.

## Core Data Structures

### Record Identifier (RID)

```swift
/// Record Identifier (pageId, slotId)
public struct RID: Hashable, Codable, CustomStringConvertible {
    public let pageId: UInt64
    public let slotId: UInt16
    public init(pageId: UInt64, slotId: UInt16) {
        self.pageId = pageId
        self.slotId = slotId
    }
    public var description: String { "RID(\(pageId),\(slotId))" }
}
```

**Detailed Analysis:**

#### Memory Layout
- **Total Size**: 10 bytes (8 bytes for pageId + 2 bytes for slotId)
- **Alignment**: 8-byte aligned due to UInt64
- **Padding**: 6 bytes of padding after slotId
- **Memory Efficiency**: Compact representation for database records

#### Field Analysis
- **`pageId: UInt64`**: 
  - **Range**: 0 to 18,446,744,073,709,551,615
  - **Purpose**: Identifies the physical page containing the record
  - **Performance**: 64-bit allows for massive databases
  - **Memory**: 8 bytes, aligned to 8-byte boundary

- **`slotId: UInt16`**:
  - **Range**: 0 to 65,535
  - **Purpose**: Identifies the slot within the page
  - **Performance**: 16-bit sufficient for page slots
  - **Memory**: 2 bytes, aligned to 2-byte boundary

#### Protocol Conformance
- **`Hashable`**: Enables use as dictionary keys
- **`Codable`**: Supports serialization for persistence
- **`CustomStringConvertible`**: Provides human-readable representation

#### Design Rationale
- **Two-Level Addressing**: Page + slot provides efficient record location
- **Fixed Size**: 10 bytes enables O(1) operations
- **Type Safety**: Struct prevents invalid RID construction
- **Performance**: Hashable enables fast lookups

### Page Identifier

```swift
/// Logical Page Identifier
public typealias PageID = UInt64
```

**Analysis:**
- **Type Alias**: Simple alias for UInt64
- **Purpose**: Identifies logical pages in the database
- **Range**: 0 to 18,446,744,073,709,551,615
- **Performance**: 64-bit enables massive databases
- **Memory**: 8 bytes, aligned to 8-byte boundary

## Value Type System

### Value Enum Definition

```swift
/// Extended value types for rows with additional data types
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    // Extended types
    case date(Date)
    case decimal(Decimal)
    case blob(Data)
    case json(Data) // JSON stored as Data for efficiency
    case enumValue(String, String) // (enumName, value)
}
```

**Detailed Analysis:**

#### Memory Layout
- **Enum Tag**: 1 byte for case discrimination
- **Associated Values**: Variable size based on type
- **Alignment**: Aligned to largest associated value
- **Total Size**: 1 byte + size of associated value + padding

#### Primitive Types

##### `case int(Int64)`
- **Size**: 1 byte (tag) + 8 bytes (Int64) = 9 bytes
- **Alignment**: 8-byte aligned
- **Range**: -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807
- **Performance**: Native 64-bit integer operations
- **Memory**: Efficient for large numbers

##### `case double(Double)`
- **Size**: 1 byte (tag) + 8 bytes (Double) = 9 bytes
- **Alignment**: 8-byte aligned
- **Precision**: 64-bit IEEE 754 double precision
- **Range**: ±1.7976931348623157e+308
- **Performance**: Native floating-point operations

##### `case bool(Bool)`
- **Size**: 1 byte (tag) + 1 byte (Bool) = 2 bytes
- **Alignment**: 1-byte aligned
- **Values**: true or false
- **Performance**: Native boolean operations
- **Memory**: Efficient for boolean flags

##### `case string(String)`
- **Size**: 1 byte (tag) + String overhead + content
- **Alignment**: 8-byte aligned (String is reference type)
- **Storage**: String is stored as reference to heap-allocated data
- **Performance**: O(1) for basic operations, O(n) for length
- **Memory**: Variable size based on content

##### `case null`
- **Size**: 1 byte (tag only)
- **Alignment**: 1-byte aligned
- **Purpose**: Represents missing or unknown values
- **Performance**: O(1) for null checks
- **Memory**: Most efficient representation

#### Extended Types

##### `case date(Date)`
- **Size**: 1 byte (tag) + 8 bytes (Date) = 9 bytes
- **Alignment**: 8-byte aligned
- **Storage**: Date is stored as TimeInterval (Double)
- **Range**: January 1, 0001 to December 31, 9999
- **Performance**: Native date operations
- **Precision**: Nanosecond precision

##### `case decimal(Decimal)`
- **Size**: 1 byte (tag) + 20 bytes (Decimal) = 21 bytes
- **Alignment**: 8-byte aligned
- **Storage**: Decimal is stored as 128-bit value
- **Precision**: 38 decimal digits
- **Performance**: Slower than primitive types
- **Use Case**: Financial calculations requiring exact precision

##### `case blob(Data)`
- **Size**: 1 byte (tag) + Data overhead + content
- **Alignment**: 8-byte aligned (Data is reference type)
- **Storage**: Data is stored as reference to heap-allocated bytes
- **Performance**: O(1) for basic operations, O(n) for content access
- **Memory**: Variable size based on content
- **Use Case**: Binary data, images, files

##### `case json(Data)`
- **Size**: 1 byte (tag) + Data overhead + JSON content
- **Alignment**: 8-byte aligned (Data is reference type)
- **Storage**: JSON is stored as Data for efficiency
- **Performance**: O(1) for storage, O(n) for parsing
- **Memory**: Variable size based on JSON content
- **Use Case**: Semi-structured data, configuration

##### `case enumValue(String, String)`
- **Size**: 1 byte (tag) + 2 × String overhead + content
- **Alignment**: 8-byte aligned (Strings are reference types)
- **Storage**: Both enum name and value are stored as String references
- **Performance**: O(1) for basic operations, O(n) for string operations
- **Memory**: Variable size based on enum name and value
- **Use Case**: User-defined enumerations

### Value Description Implementation

```swift
public var description: String {
    switch self {
    case .int(let v): return String(v)
    case .double(let v): return String(v)
    case .bool(let v): return String(v)
    case .string(let v): return v
    case .null: return "NULL"
    case .date(let v): return ISO8601DateFormatter().string(from: v)
    case .decimal(let v): return v.description
    case .blob(let v): return "<BLOB:\(v.count) bytes>"
    case .json(let v): return String(data: v, encoding: .utf8) ?? "<INVALID JSON>"
    case .enumValue(let enumName, let value): return "\(enumName).\(value)"
    }
}
```

**Analysis:**
- **Pattern Matching**: Uses switch statement for type-safe access
- **String Conversion**: Each case provides appropriate string representation
- **Error Handling**: JSON case handles invalid UTF-8 gracefully
- **Performance**: O(1) for most cases, O(n) for string operations
- **Memory**: Creates temporary strings for output

### Value Type Name Implementation

```swift
/// Returns the data type name for this value
public var typeName: String {
    switch self {
    case .int: return "INT"
    case .double: return "DOUBLE"
    case .bool: return "BOOL"
    case .string: return "TEXT"
    case .null: return "NULL"
    case .date: return "DATE"
    case .decimal: return "DECIMAL"
    case .blob: return "BLOB"
    case .json: return "JSON"
    case .enumValue(let enumName, _): return "ENUM(\(enumName))"
    }
}
```

**Analysis:**
- **SQL Compatibility**: Returns SQL-compatible type names
- **Pattern Matching**: Uses switch without associated values for efficiency
- **Enum Handling**: Special case for enum values with dynamic type name
- **Performance**: O(1) for all cases
- **Memory**: Returns string literals (no allocation)

## Row Type System

### Row Type Definition

```swift
/// Row represented as ordered dictionary (stable key order not guaranteed)
public typealias Row = [String: Value]
```

**Analysis:**
- **Type Alias**: Simple alias for dictionary
- **Key Type**: String for column names
- **Value Type**: Value enum for data
- **Ordering**: Dictionary order is not guaranteed in Swift
- **Performance**: O(1) for key lookup, O(n) for iteration
- **Memory**: Variable size based on number of columns

### Row Memory Layout

```
Row Memory Layout:
┌─────────────────┐
│ Dictionary      │
│ ┌─────────────┐ │
│ │ Key: String │ │
│ │ Value: Value│ │
│ └─────────────┘ │
│ ┌─────────────┐ │
│ │ Key: String │ │
│ │ Value: Value│ │
│ └─────────────┘ │
│ ...             │
└─────────────────┘
```

**Analysis:**
- **Dictionary Overhead**: 24 bytes for dictionary structure
- **Key Storage**: String references (8 bytes each)
- **Value Storage**: Value enum instances (variable size)
- **Total Size**: 24 + (8 + value_size) × column_count
- **Alignment**: 8-byte aligned for dictionary

## Statistics Types

### Table Statistics

```swift
/// Cached statistics about a table used by the optimizer.
public struct TableStatistics: Codable {
    public let table: String
    public let rowCount: Int
    public let deadRowCount: Int
    public let avgRowSizeBytes: Double
    public let fragmentation: HeapFragmentationStats?
    public let columnCardinality: [String: Int]
    public let sampledRowCount: Int
    public let updatedAt: Date
}
```

**Detailed Analysis:**

#### Field Analysis
- **`table: String`**: Table name (reference to heap-allocated string)
- **`rowCount: Int`**: Total number of rows (64-bit on 64-bit systems)
- **`deadRowCount: Int`**: Number of deleted rows (for vacuum planning)
- **`avgRowSizeBytes: Double`**: Average row size in bytes (64-bit floating point)
- **`fragmentation: HeapFragmentationStats?`**: Optional fragmentation statistics
- **`columnCardinality: [String: Int]`**: Dictionary of column name to unique value count
- **`sampledRowCount: Int`**: Number of rows sampled for statistics
- **`updatedAt: Date`**: Timestamp of last statistics update

#### Memory Layout
- **Total Size**: ~200+ bytes (varies with column count)
- **Alignment**: 8-byte aligned
- **Heap Allocations**: String and dictionary references
- **Performance**: O(1) for field access, O(n) for column iteration

#### Usage in Query Optimization
- **Row Count**: Used for cost estimation
- **Dead Row Count**: Used for vacuum planning
- **Average Row Size**: Used for memory estimation
- **Fragmentation**: Used for maintenance planning
- **Column Cardinality**: Used for selectivity estimation
- **Sampled Row Count**: Used for accuracy assessment
- **Updated At**: Used for statistics freshness

### Index Statistics

```swift
/// Basic index statistics surfaced to the optimizer.
public struct IndexStatistics: Codable {
    public let table: String
    public let name: String
    public let entryCount: Int
    public let height: Int
    public let leafOccupancy: Double
    public let updatedAt: Date
}
```

**Detailed Analysis:**

#### Field Analysis
- **`table: String`**: Table name (reference to heap-allocated string)
- **`name: String`**: Index name (reference to heap-allocated string)
- **`entryCount: Int`**: Number of entries in index (64-bit on 64-bit systems)
- **`height: Int`**: Height of index tree (64-bit on 64-bit systems)
- **`leafOccupancy: Double`**: Percentage of leaf pages occupied (64-bit floating point)
- **`updatedAt: Date`**: Timestamp of last statistics update

#### Memory Layout
- **Total Size**: ~80 bytes
- **Alignment**: 8-byte aligned
- **Heap Allocations**: String references
- **Performance**: O(1) for field access

#### Usage in Query Optimization
- **Entry Count**: Used for cost estimation
- **Height**: Used for tree traversal cost
- **Leaf Occupancy**: Used for page access cost
- **Updated At**: Used for statistics freshness

## Protocol Conformance

### Codable Implementation

The Value enum conforms to Codable, enabling serialization:

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    // ... cases ...
}
```

**Serialization Analysis:**
- **Binary Format**: Uses Swift's native binary encoding
- **Size**: Compact binary representation
- **Performance**: Fast serialization/deserialization
- **Compatibility**: Swift-specific format
- **Error Handling**: Throws errors for invalid data

### Hashable Implementation

The Value enum conforms to Hashable, enabling use as dictionary keys:

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    // ... cases ...
}
```

**Hashing Analysis:**
- **Algorithm**: Uses Swift's built-in hashing
- **Performance**: O(1) for primitive types, O(n) for strings
- **Distribution**: Good hash distribution for dictionary performance
- **Collision Handling**: Dictionary handles collisions internally

### Sendable Implementation

The Value enum conforms to Sendable, enabling safe concurrent access:

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    // ... cases ...
}
```

**Concurrency Analysis:**
- **Thread Safety**: All associated values are Sendable
- **Immutable**: Value instances are immutable
- **Performance**: No locking required for concurrent access
- **Memory**: Safe to pass between threads

## Performance Characteristics

### Memory Usage

| Type | Size | Alignment | Heap Allocations |
|------|------|-----------|------------------|
| `int(Int64)` | 9 bytes | 8-byte | 0 |
| `double(Double)` | 9 bytes | 8-byte | 0 |
| `bool(Bool)` | 2 bytes | 1-byte | 0 |
| `string(String)` | 9+ bytes | 8-byte | 1+ |
| `null` | 1 byte | 1-byte | 0 |
| `date(Date)` | 9 bytes | 8-byte | 0 |
| `decimal(Decimal)` | 21 bytes | 8-byte | 0 |
| `blob(Data)` | 9+ bytes | 8-byte | 1+ |
| `json(Data)` | 9+ bytes | 8-byte | 1+ |
| `enumValue(String, String)` | 17+ bytes | 8-byte | 2+ |

### Access Performance

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|------------------|
| Value creation | O(1) | O(1) |
| Value comparison | O(1) | O(1) |
| Value hashing | O(1) | O(1) |
| String conversion | O(1) | O(n) |
| Serialization | O(1) | O(1) |
| Deserialization | O(1) | O(1) |

### Memory Optimization

1. **Value Types**: Most types are value types, avoiding heap allocation
2. **Enum Tag**: Single byte tag for type discrimination
3. **Alignment**: Proper alignment for performance
4. **Reference Types**: Only used when necessary (String, Data)
5. **Immutable**: Immutable values enable safe concurrency

## Design Decisions

### Why Int64 Instead of Int?

- **Consistency**: 64-bit integers across all platforms
- **Range**: Larger range than platform-specific Int
- **Performance**: 64-bit operations are fast on modern hardware
- **Storage**: Consistent storage size across platforms

### Why Double Instead of Float?

- **Precision**: Double precision for financial calculations
- **Performance**: 64-bit floating-point is fast on modern hardware
- **Range**: Larger range than Float
- **Compatibility**: Better compatibility with external systems

### Why String Instead of Custom String Type?

- **Performance**: String is highly optimized in Swift
- **Memory**: String uses copy-on-write for efficiency
- **Compatibility**: Better compatibility with external systems
- **Features**: Rich string manipulation capabilities

### Why Data Instead of Custom Binary Type?

- **Performance**: Data is highly optimized in Swift
- **Memory**: Data uses copy-on-write for efficiency
- **Compatibility**: Better compatibility with external systems
- **Features**: Rich binary data manipulation capabilities

### Why Enum Instead of Class Hierarchy?

- **Performance**: Enums are more efficient than classes
- **Memory**: No heap allocation for value types
- **Type Safety**: Compiler ensures exhaustive handling
- **Pattern Matching**: Swift's pattern matching is powerful

## Future Extensions

### New Value Types

The Value enum can be extended with new types:

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    // ... existing cases ...
    case uuid(UUID)
    case array([Value])
    case map([String: Value])
}
```

### Custom Serialization

Custom serialization can be added for specific types:

```swift
extension Value {
    func customSerialize() -> Data {
        // Custom serialization logic
    }
}
```

### Performance Optimizations

Future optimizations could include:

1. **SIMD Operations**: Vectorized operations for arrays
2. **Compression**: Built-in compression for large values
3. **Caching**: Value caching for frequently accessed data
4. **Lazy Loading**: Lazy loading for large values

---

*This analysis provides a comprehensive understanding of ColibrìDB's data type system. For specific implementation details, see the corresponding source files.*

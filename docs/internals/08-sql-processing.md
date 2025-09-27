# SQL Processing Internals

## Overview

ColibrìDB implements a comprehensive SQL processing system that includes parsing, planning, optimization, and execution of SQL queries. This chapter provides a detailed analysis of the SQL parser, query planner, optimizer, and executor components.

## SQL Parser Architecture

### Class Structure

```swift
/// Simple SQL statement types
public enum SimpleSQLStatement {
    case createTable(name: String, columns: [String])
    case dropTable(name: String)
    case insert(table: String, values: [String: String])
    case select(table: String, columns: [String]?)
    case delete(table: String, whereClause: String?)
}

/// Simple SQL Parser
public final class SimpleSQLParser {
    private let sql: String
    
    public init(sql: String) {
        self.sql = sql.trimmingCharacters(in: .whitespacesAndNewlines)
    }
}
```

**Detailed Analysis:**

#### Statement Types

##### `SimpleSQLStatement` Enum
```swift
public enum SimpleSQLStatement {
    case createTable(name: String, columns: [String])
    case dropTable(name: String)
    case insert(table: String, values: [String: String])
    case select(table: String, columns: [String]?)
    case delete(table: String, whereClause: String?)
}
```

**Case Analysis:**
- **`createTable`**: DDL operation for table creation
  - **`name: String`**: Table name
  - **`columns: [String]`**: Column definitions
- **`dropTable`**: DDL operation for table deletion
  - **`name: String`**: Table name
- **`insert`**: DML operation for data insertion
  - **`table: String`**: Target table name
  - **`values: [String: String]`**: Column-value pairs
- **`select`**: DML operation for data retrieval
  - **`table: String`**: Source table name
  - **`columns: [String]?`**: Optional column list
- **`delete`**: DML operation for data deletion
  - **`table: String`**: Target table name
  - **`whereClause: String?`**: Optional WHERE condition

#### Parser State
- **`sql: String`**: Input SQL statement
- **Initialization**: Trims whitespace and newlines
- **Immutable**: Parser state is immutable

### Parsing Process

#### Main Parse Method

```swift
/// Parses the SQL statement
public func parse() throws -> SimpleSQLStatement {
    let tokens = sql.components(separatedBy: .whitespacesAndNewlines).filter { !$0.isEmpty }
    guard !tokens.isEmpty else {
        throw SimpleSQLParseError.emptyStatement
    }
    
    let command = tokens[0].uppercased()
    
    switch command {
    case "CREATE":
        return try parseCreate(tokens)
    case "DROP":
        return try parseDrop(tokens)
    case "INSERT":
        return try parseInsert(tokens)
    case "SELECT":
        return try parseSelect(tokens)
    case "DELETE":
        return try parseDelete(tokens)
    default:
        throw SimpleSQLParseError.unsupportedCommand(command)
    }
}
```

**Detailed Analysis:**

#### Tokenization Process
1. **Split by Whitespace**: Split SQL into tokens
2. **Filter Empty**: Remove empty tokens
3. **Empty Check**: Ensure at least one token
4. **Command Extraction**: Get first token as command
5. **Case Normalization**: Convert to uppercase
6. **Dispatch**: Route to appropriate parser

#### Error Handling
- **Empty Statement**: Throw error for empty input
- **Unsupported Command**: Throw error for unknown commands
- **Parse Errors**: Propagate errors from sub-parsers

#### Performance
- **Tokenization**: O(n) where n is SQL length
- **Command Lookup**: O(1) switch statement
- **Total Time**: O(n) where n is SQL length

#### CREATE TABLE Parsing

```swift
private func parseCreate(_ tokens: [String]) throws -> SimpleSQLStatement {
    guard tokens.count >= 3 && tokens[1].uppercased() == "TABLE" else {
        throw SimpleSQLParseError.invalidSyntax("Expected CREATE TABLE")
    }
    
    let tableName = tokens[2]
    return .createTable(name: tableName, columns: [])
}
```

**Detailed Analysis:**

#### Syntax Validation
- **Token Count**: Ensure at least 3 tokens
- **TABLE Keyword**: Verify second token is "TABLE"
- **Error Handling**: Throw error for invalid syntax

#### Table Name Extraction
- **Position**: Third token is table name
- **Validation**: No additional validation performed
- **Return**: Create statement with empty columns

#### Limitations
- **Column Parsing**: Not implemented (returns empty array)
- **Constraint Parsing**: Not implemented
- **Type Parsing**: Not implemented

#### DROP TABLE Parsing

```swift
private func parseDrop(_ tokens: [String]) throws -> SimpleSQLStatement {
    guard tokens.count >= 3 && tokens[1].uppercased() == "TABLE" else {
        throw SimpleSQLParseError.invalidSyntax("Expected DROP TABLE")
    }
    
    let tableName = tokens[2]
    return .dropTable(name: tableName)
}
```

**Detailed Analysis:**

#### Syntax Validation
- **Token Count**: Ensure at least 3 tokens
- **TABLE Keyword**: Verify second token is "TABLE"
- **Error Handling**: Throw error for invalid syntax

#### Table Name Extraction
- **Position**: Third token is table name
- **Validation**: No additional validation performed
- **Return**: Drop statement with table name

#### INSERT Parsing

```swift
private func parseInsert(_ tokens: [String]) throws -> SimpleSQLStatement {
    guard tokens.count >= 4 && tokens[1].uppercased() == "INTO" else {
        throw SimpleSQLParseError.invalidSyntax("Expected INSERT INTO")
    }
    
    let tableName = tokens[2]
    
    // Simple VALUES parsing - expects VALUES (col1=val1, col2=val2, ...)
    var values: [String: String] = [:]
    
    if tokens.count > 3 && tokens[3].uppercased() == "VALUES" {
        let valuesString = tokens.dropFirst(4).joined(separator: " ")
        let pairs = valuesString.components(separatedBy: ",")
        
        for pair in pairs {
            let trimmed = pair.trimmingCharacters(in: .whitespaces)
            if trimmed.contains("=") {
                let parts = trimmed.components(separatedBy: "=")
                if parts.count == 2 {
                    let key = parts[0].trimmingCharacters(in: .whitespaces)
                    let value = parts[1].trimmingCharacters(in: .whitespaces)
                    values[key] = value
                }
            }
        }
    }
    
    return .insert(table: tableName, values: values)
}
```

**Detailed Analysis:**

#### Syntax Validation
- **Token Count**: Ensure at least 4 tokens
- **INTO Keyword**: Verify second token is "INTO"
- **Error Handling**: Throw error for invalid syntax

#### Table Name Extraction
- **Position**: Third token is table name
- **Validation**: No additional validation performed

#### VALUES Parsing
- **VALUES Keyword**: Check for fourth token "VALUES"
- **Values String**: Join remaining tokens
- **Pair Splitting**: Split by comma separator
- **Key-Value Parsing**: Split each pair by "="
- **Whitespace Trimming**: Remove leading/trailing whitespace

#### Value Storage
- **Dictionary**: Store as [String: String] mapping
- **Key**: Column name
- **Value**: String representation of value
- **Type Conversion**: Handled by executor

#### Performance
- **Tokenization**: O(n) where n is SQL length
- **Pair Parsing**: O(m) where m is number of pairs
- **Total Time**: O(n + m) where n is SQL length, m is pairs

#### SELECT Parsing

```swift
private func parseSelect(_ tokens: [String]) throws -> SimpleSQLStatement {
    guard tokens.count >= 2 else {
        throw SimpleSQLParseError.invalidSyntax("Expected SELECT ... FROM")
    }
    
    // Find FROM keyword
    var fromIndex = -1
    for (index, token) in tokens.enumerated() {
        if token.uppercased() == "FROM" {
            fromIndex = index
            break
        }
    }
    
    guard fromIndex > 0 && fromIndex < tokens.count - 1 else {
        throw SimpleSQLParseError.invalidSyntax("Expected SELECT ... FROM table")
    }
    
    let tableName = tokens[fromIndex + 1]
    let columnTokens = Array(tokens[1..<fromIndex])
    
    // Parse columns
    var columns: [String]? = nil
    if columnTokens.count > 0 && columnTokens[0].uppercased() != "*" {
        columns = columnTokens
    }
    
    return .select(table: tableName, columns: columns)
}
```

**Detailed Analysis:**

#### Syntax Validation
- **Token Count**: Ensure at least 2 tokens
- **FROM Search**: Find FROM keyword position
- **FROM Validation**: Ensure FROM is present and has table name
- **Error Handling**: Throw error for invalid syntax

#### Column Parsing
- **Column Tokens**: Extract tokens between SELECT and FROM
- **Wildcard Check**: Check for "*" wildcard
- **Column List**: Store column names if not wildcard
- **Null Handling**: Set columns to nil for wildcard

#### Table Name Extraction
- **Position**: Token after FROM keyword
- **Validation**: No additional validation performed
- **Return**: Select statement with table and columns

#### Performance
- **FROM Search**: O(n) where n is number of tokens
- **Column Parsing**: O(m) where m is number of columns
- **Total Time**: O(n + m) where n is tokens, m is columns

#### DELETE Parsing

```swift
private func parseDelete(_ tokens: [String]) throws -> SimpleSQLStatement {
    guard tokens.count >= 2 && tokens[1].uppercased() == "FROM" else {
        throw SimpleSQLParseError.invalidSyntax("Expected DELETE FROM")
    }
    
    let tableName = tokens[2]
    
    // Simple WHERE parsing - expects WHERE condition
    var whereClause: String? = nil
    if tokens.count > 3 && tokens[3].uppercased() == "WHERE" {
        let whereTokens = Array(tokens[4...])
        whereClause = whereTokens.joined(separator: " ")
    }
    
    return .delete(table: tableName, whereClause: whereClause)
}
```

**Detailed Analysis:**

#### Syntax Validation
- **Token Count**: Ensure at least 2 tokens
- **FROM Keyword**: Verify second token is "FROM"
- **Error Handling**: Throw error for invalid syntax

#### Table Name Extraction
- **Position**: Third token is table name
- **Validation**: No additional validation performed

#### WHERE Clause Parsing
- **WHERE Keyword**: Check for fourth token "WHERE"
- **Condition Tokens**: Extract tokens after WHERE
- **Condition String**: Join tokens with spaces
- **Null Handling**: Set to nil if no WHERE clause

#### Performance
- **Tokenization**: O(n) where n is SQL length
- **WHERE Parsing**: O(m) where m is WHERE clause length
- **Total Time**: O(n + m) where n is SQL length, m is WHERE length

## SQL Executor

### Class Structure

```swift
public final class SQLExecutor {
    private let database: Database
    
    public init(database: Database) {
        self.database = database
    }
    
    public func execute(statement: SimpleSQLStatement) throws {
        switch statement {
        case .createTable(let name, let columns):
            try executeCreateTable(name: name, columns: columns)
        case .dropTable(let name):
            try executeDropTable(name: name)
        case .insert(let table, let values):
            try executeInsert(table: table, values: values)
        case .select(let table, let columns):
            try executeSelect(table: table, columns: columns)
        case .delete(let table, let whereClause):
            try executeDelete(table: table, whereClause: whereClause)
        }
    }
}
```

**Detailed Analysis:**

#### Core Configuration
- **`database: Database`**: Reference to database instance
- **Initialization**: Store database reference
- **Execution**: Route statements to appropriate handlers

#### Statement Routing
- **Switch Statement**: Route based on statement type
- **Type Safety**: Compiler ensures exhaustive handling
- **Error Propagation**: Throws errors from handlers

### CREATE TABLE Execution

```swift
private func executeCreateTable(name: String, columns: [String]) throws {
    var columnDefinitions: [CatalogColumnDefinition] = []
    for column in columns {
        let parts = column.components(separatedBy: " ")
        let columnName = parts[0]
        let columnType = parts.count > 1 ? parts[1] : "string"
        
        let dataType: DataType
        switch columnType.uppercased() {
        case "INT", "INTEGER":
            dataType = .int
        case "STRING", "TEXT", "VARCHAR":
            dataType = .string
        case "DOUBLE", "FLOAT", "REAL":
            dataType = .double
        case "BOOL", "BOOLEAN":
            dataType = .boolean
        case "DATE", "TIMESTAMP":
            dataType = .date
        case "BLOB", "BINARY":
            dataType = .blob
        case "JSON":
            dataType = .json
        case "DECIMAL", "NUMERIC":
            dataType = .decimal
        default:
            dataType = .string
        }
        
        let columnDef = CatalogColumnDefinition(
            name: columnName,
            type: dataType,
            nullable: true,
            defaultValue: nil
        )
        columnDefinitions.append(columnDef)
    }
    
    let schema = CatalogTableSchema(columns: columnDefinitions)
    try database.createTable(name, in: "default", schema: schema)
}
```

**Detailed Analysis:**

#### Column Processing
1. **Column Parsing**: Split column definition by space
2. **Name Extraction**: First part is column name
3. **Type Extraction**: Second part is column type (default: string)
4. **Type Mapping**: Map string to DataType enum
5. **Definition Creation**: Create CatalogColumnDefinition
6. **Schema Creation**: Create CatalogTableSchema
7. **Table Creation**: Call database.createTable

#### Type Mapping
- **INT/INTEGER**: Maps to .int
- **STRING/TEXT/VARCHAR**: Maps to .string
- **DOUBLE/FLOAT/REAL**: Maps to .double
- **BOOL/BOOLEAN**: Maps to .boolean
- **DATE/TIMESTAMP**: Maps to .date
- **BLOB/BINARY**: Maps to .blob
- **JSON**: Maps to .json
- **DECIMAL/NUMERIC**: Maps to .decimal
- **Default**: Maps to .string

#### Schema Creation
- **Column Definitions**: Array of column definitions
- **Table Schema**: Wraps column definitions
- **Database**: Uses "default" database
- **Error Handling**: Throws errors from database operations

#### Performance
- **Column Processing**: O(n) where n is number of columns
- **Type Mapping**: O(1) for each column
- **Schema Creation**: O(1) operation
- **Table Creation**: O(1) database operation
- **Total Time**: O(n) where n is number of columns

### DROP TABLE Execution

```swift
private func executeDropTable(name: String) throws {
    try database.dropTable(name, in: "default")
}
```

**Analysis:**
- **Simple Delegation**: Delegates to database.dropTable
- **Database**: Uses "default" database
- **Error Handling**: Throws errors from database operations
- **Performance**: O(1) database operation

### INSERT Execution

```swift
private func executeInsert(table: String, values: [String: String]) throws {
    var row: Row = [:]
    
    for (column, value) in values {
        let parsedValue = parseValue(value)
        row[column] = parsedValue
    }
    
    _ = try database.insert(into: table, row: row)
}
```

**Detailed Analysis:**

#### Value Processing
1. **Row Creation**: Create empty Row dictionary
2. **Value Iteration**: Iterate through column-value pairs
3. **Value Parsing**: Parse string values to Value types
4. **Row Population**: Add parsed values to row
5. **Database Insert**: Call database.insert

#### Value Parsing
```swift
private func parseValue(_ value: String) -> Value {
    if value.uppercased() == "NULL" {
        return .null
    }
    
    if value.hasPrefix("'") && value.hasSuffix("'") {
        let startIndex = value.index(after: value.startIndex)
        let endIndex = value.index(before: value.endIndex)
        return .string(String(value[startIndex..<endIndex]))
    }
    
    if let intValue = Int64(value) {
        return .int(intValue)
    }
    
    if let doubleValue = Double(value) {
        return .double(doubleValue)
    }
    
    if value.uppercased() == "TRUE" {
        return .bool(true)
    }
    if value.uppercased() == "FALSE" {
        return .bool(false)
    }
    
    return .string(value)
}
```

**Analysis:**
- **NULL Handling**: Check for "NULL" string
- **String Literals**: Check for quoted strings
- **Integer Parsing**: Try to parse as Int64
- **Double Parsing**: Try to parse as Double
- **Boolean Parsing**: Check for "TRUE"/"FALSE"
- **Default**: Treat as string

#### Performance
- **Value Parsing**: O(n) where n is number of values
- **Row Creation**: O(1) operation
- **Database Insert**: O(1) database operation
- **Total Time**: O(n) where n is number of values

### SELECT Execution

```swift
private func executeSelect(table: String, columns: [String]?) throws {
    print("SELECT not implemented yet")
}
```

**Analysis:**
- **Placeholder**: Not yet implemented
- **Future**: Will implement query execution
- **Complexity**: Requires query planner and optimizer

### DELETE Execution

```swift
private func executeDelete(table: String, whereClause: String?) throws {
    print("DELETE not implemented yet")
}
```

**Analysis:**
- **Placeholder**: Not yet implemented
- **Future**: Will implement delete execution
- **Complexity**: Requires WHERE clause evaluation

## Query Planner

### Class Structure

```swift
public final class QueryPlanner {
    private let database: Database
    private let costModel: CostModel
    
    public init(database: Database) {
        self.database = database
        self.costModel = CostModel()
    }
    
    public func plan(statement: SimpleSQLStatement) throws -> QueryPlan {
        switch statement {
        case .select(let table, let columns):
            return try planSelect(table: table, columns: columns)
        default:
            throw QueryPlanningError.unsupportedStatement
        }
    }
}
```

**Detailed Analysis:**

#### Core Configuration
- **`database: Database`**: Reference to database instance
- **`costModel: CostModel`**: Cost estimation model
- **Initialization**: Store database reference and create cost model

#### Planning Process
- **Statement Routing**: Route based on statement type
- **Cost Estimation**: Use cost model for optimization
- **Plan Generation**: Create optimal execution plan

### SELECT Planning

```swift
private func planSelect(table: String, columns: [String]?) throws -> QueryPlan {
    // Get table statistics
    let stats = try database.getTableStatistics(table)
    
    // Create scan operator
    let scanOp = ScanOperator(table: table, columns: columns)
    
    // Estimate cost
    let cost = costModel.estimateScanCost(stats: stats, columns: columns)
    
    // Create query plan
    return QueryPlan(operators: [scanOp], estimatedCost: cost)
}
```

**Detailed Analysis:**

#### Planning Process
1. **Statistics Retrieval**: Get table statistics
2. **Operator Creation**: Create scan operator
3. **Cost Estimation**: Estimate operation cost
4. **Plan Creation**: Create query plan

#### Statistics Usage
- **Table Statistics**: Row count, size, etc.
- **Cost Estimation**: Use statistics for cost calculation
- **Optimization**: Choose best execution strategy

#### Performance
- **Statistics Retrieval**: O(1) database operation
- **Operator Creation**: O(1) operation
- **Cost Estimation**: O(1) operation
- **Total Time**: O(1) operation

## Cost Model

### Class Structure

```swift
public final class CostModel {
    private let cpuCostPerRow: Double = 0.1
    private let ioCostPerPage: Double = 1.0
    private let memoryCostPerRow: Double = 0.01
    
    public func estimateScanCost(stats: TableStatistics, columns: [String]?) -> Double {
        let rowCount = Double(stats.rowCount)
        let avgRowSize = stats.avgRowSizeBytes
        let pages = rowCount * avgRowSize / 8192.0 // 8KB pages
        
        let cpuCost = rowCount * cpuCostPerRow
        let ioCost = pages * ioCostPerPage
        let memoryCost = rowCount * memoryCostPerRow
        
        return cpuCost + ioCost + memoryCost
    }
}
```

**Detailed Analysis:**

#### Cost Factors
- **CPU Cost**: Cost per row processed
- **I/O Cost**: Cost per page accessed
- **Memory Cost**: Cost per row in memory

#### Cost Calculation
- **Row Count**: Number of rows to process
- **Page Count**: Number of pages to access
- **Total Cost**: Sum of all cost factors

#### Performance
- **Cost Calculation**: O(1) operation
- **Memory**: O(1) memory usage
- **Accuracy**: Approximate cost estimation

## Query Operators

### Scan Operator

```swift
public struct ScanOperator: QueryOperator {
    let table: String
    let columns: [String]?
    
    public func execute(database: Database) throws -> [Row] {
        // Implementation would scan table and return rows
        return []
    }
}
```

**Analysis:**
- **Table Scan**: Scans entire table
- **Column Selection**: Selects specified columns
- **Row Return**: Returns array of rows
- **Placeholder**: Not fully implemented

### Filter Operator

```swift
public struct FilterOperator: QueryOperator {
    let condition: String
    let input: QueryOperator
    
    public func execute(database: Database) throws -> [Row] {
        // Implementation would filter rows based on condition
        return []
    }
}
```

**Analysis:**
- **Condition**: WHERE clause condition
- **Input**: Input operator
- **Filtering**: Filters rows based on condition
- **Placeholder**: Not fully implemented

## Performance Characteristics

### Time Complexity

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|------------------|
| SQL Parsing | O(n) | O(n) |
| CREATE TABLE | O(c) | O(1) |
| DROP TABLE | O(1) | O(1) |
| INSERT | O(v) | O(1) |
| SELECT | O(r) | O(r) |
| DELETE | O(r) | O(1) |

### Memory Usage

| Component | Memory | Purpose |
|-----------|--------|---------|
| Parser | O(n) | Token storage |
| Executor | O(1) | Statement execution |
| Planner | O(1) | Query planning |
| Operators | O(r) | Result storage |

## Design Decisions

### Why Simple Parser?

- **Simplicity**: Easy to understand and maintain
- **Performance**: Fast parsing for simple queries
- **Extensibility**: Easy to add new statement types
- **Limitations**: Limited to basic SQL features

### Why Enum Statements?

- **Type Safety**: Compiler ensures exhaustive handling
- **Performance**: Fast pattern matching
- **Clarity**: Clear statement representation
- **Extensibility**: Easy to add new statement types

### Why Value Parsing?

- **Flexibility**: Handles various data types
- **Error Handling**: Graceful fallback to string
- **Performance**: O(1) parsing for most types
- **Compatibility**: Works with existing Value system

## Future Optimizations

### Advanced Parser

- **Recursive Descent**: More sophisticated parsing
- **AST**: Abstract syntax tree representation
- **Error Recovery**: Better error handling
- **Performance**: More efficient parsing

### Query Optimization

- **Cost-Based**: Use cost model for optimization
- **Index Selection**: Choose optimal indexes
- **Join Optimization**: Optimize join operations
- **Performance**: Better query performance

### Parallel Execution

- **Multi-Threading**: Parallel query execution
- **Pipeline**: Pipeline operators
- **Performance**: Better utilization of resources
- **Complexity**: More complex implementation

---

*This analysis provides a comprehensive understanding of ColibrìDB's SQL processing system. For specific implementation details, see the corresponding source files.*

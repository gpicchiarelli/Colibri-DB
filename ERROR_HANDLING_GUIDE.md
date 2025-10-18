# Error Handling Guide

Standardized error handling patterns for Colibrì-DB.

---

## 🎯 Error Handling Principles

### 1. **Fail Fast, Fail Clearly**
- Detect errors as early as possible
- Throw descriptive errors immediately
- Never silently ignore errors in critical paths

### 2. **Use Swift Error Handling**
- Use `throws` for recoverable errors
- Use `fatalError()` only for programmer errors
- Use `precondition()` for debug-time checks

### 3. **Provide Context**
- Include what failed
- Include why it failed
- Include how to fix it (if known)

### 4. **Clean Up Resources**
- Use `defer` for guaranteed cleanup
- Release locks before throwing
- Close file handles on error paths

---

## 📋 Standard Error Types

### DBError Enum

```swift
public enum DBError: Error, LocalizedError {
    // Data errors
    case notFound(String)
    case alreadyExists(String)
    case invalidArgument(String)
    
    // I/O errors
    case io(String)
    case corruption(String)
    
    // Transaction errors
    case transactionAborted(UInt64)
    case deadlock([UInt64])
    
    // Configuration errors
    case config(String)
    
    // Not implemented
    case notImplemented(String)
    
    public var errorDescription: String? {
        switch self {
        case .notFound(let m): 
            return "Not found: \(m)"
        case .io(let m): 
            return "I/O error: \(m)"
        // ... etc
        }
    }
}
```

---

## ✅ Error Handling Patterns

### Pattern 1: Simple Validation

```swift
// ✅ CORRECT
func insert(row: Row) throws {
    guard !row.isEmpty else {
        throw DBError.invalidArgument("Row cannot be empty")
    }
    // ... proceed with insert
}

// ❌ INCORRECT
func insert(row: Row) -> RID? {
    if row.isEmpty { return nil }  // Silent failure
    // ...
}
```

### Pattern 2: Resource Cleanup

```swift
// ✅ CORRECT
func processFile() throws {
    let handle = try FileHandle(forReadingFrom: url)
    defer { try? handle.close() }  // Always closes
    
    // ... work with file
    
    if someError {
        throw DBError.io("Error details")
        // defer ensures handle is closed
    }
}

// ❌ INCORRECT  
func processFile() throws {
    let handle = try FileHandle(forReadingFrom: url)
    
    if someError {
        throw DBError.io("Error")
        // handle never closed!
    }
    
    try handle.close()
}
```

### Pattern 3: Lock Cleanup

```swift
// ✅ CORRECT
func criticalSection() throws {
    lock.lock()
    defer { lock.unlock() }  // Always unlocks
    
    if error {
        throw DBError.io("Error")
        // defer ensures unlock
    }
}

// ❌ INCORRECT
func criticalSection() throws {
    lock.lock()
    
    if error {
        throw DBError.io("Error")
        // lock never unlocked!
    }
    
    lock.unlock()
}
```

### Pattern 4: Transaction Errors

```swift
// ✅ CORRECT - Clear, actionable error
throw DBError.transactionAborted(tid)

// ✅ CORRECT - With context
throw DBError.deadlock([tid1, tid2])

// ❌ INCORRECT - Too generic
throw DBError.io("Transaction failed")
```

### Pattern 5: Configuration Validation

```swift
// ✅ CORRECT - Validate early
func init(config: DBConfig) {
    do {
        try config.validate()
    } catch {
        print("⚠️  Config validation failed: \(error)")
        // Either throw or use safe defaults
    }
}

// ❌ INCORRECT - Validate late
func someOperation() {
    if config.value < 0 {
        // Too late - should validate at init
    }
}
```

---

## 🚫 Anti-Patterns to Avoid

### ❌ Silent Failures

```swift
// BAD
try? someOperation()  // Error silently ignored

// GOOD
do {
    try someOperation()
} catch {
    log.error("Operation failed: \(error)")
    throw error  // Or handle appropriately
}
```

### ❌ Generic Errors

```swift
// BAD
throw DBError.io("Error")

// GOOD
throw DBError.io("Failed to write page \(pageId): \(underlyingError)")
```

### ❌ Missing Cleanup

```swift
// BAD
lock.lock()
try operation()
lock.unlock()  // Never reached if operation throws

// GOOD
lock.lock()
defer { lock.unlock() }
try operation()
```

### ❌ Swallowing Critical Errors

```swift
// BAD - Critical error hidden
func critical() {
    do {
        try dangerousOperation()
    } catch {
        // Ignored - system in inconsistent state!
    }
}

// GOOD - Propagate critical errors
func critical() throws {
    try dangerousOperation()
}
```

---

## 📊 Error Categories

### Recoverable Errors (throw DBError)

- File not found → User can create it
- Lock timeout → User can retry
- Deadlock → User can retry
- Invalid input → User can fix input
- Configuration error → User can fix config

**Action**: Throw descriptive error, user/application handles

### Non-Recoverable Errors (fatalError)

- Programmer error (violating invariants)
- Corrupt internal state
- Impossible conditions (unreachable code)

**Action**: Crash immediately with clear message

**Use Sparingly!** Most errors are recoverable.

---

## 🎯 Error Handling Checklist

When writing a function:

- [ ] Validate all inputs
- [ ] Use `guard` for preconditions
- [ ] Use `defer` for cleanup
- [ ] Throw specific error types
- [ ] Include context in error messages
- [ ] Document what errors can be thrown
- [ ] Test error paths
- [ ] Ensure no resource leaks on error
- [ ] Consider recovery strategies

---

## 📝 Documentation Standards

### Function Documentation

```swift
/// Inserts a row into the specified table.
///
/// - Parameters:
///   - table: Table name
///   - row: Row data to insert
///   - tid: Transaction ID
/// - Returns: RID of inserted row
/// - Throws:
///   - `DBError.notFound` if table doesn't exist
///   - `DBError.invalidArgument` if row is empty
///   - `DBError.io` if write fails
///   - `DBError.transactionAborted` if transaction is not active
func insert(into table: String, row: Row, tid: UInt64) throws -> RID
```

---

## 🔧 Error Handling in Components

### Database Layer

**Standard Pattern:**
```swift
public func operation() throws -> Result {
    // 1. Validate inputs
    guard validInput else {
        throw DBError.invalidArgument("Why invalid")
    }
    
    // 2. Acquire resources
    lock.lock()
    defer { lock.unlock() }
    
    // 3. Perform operation
    let result = try performWork()
    
    // 4. Return result
    return result
    // defer ensures cleanup even on throw
}
```

### Storage Layer

**Standard Pattern:**
```swift
func writeToFile() throws {
    let handle = try FileHandle(forWritingTo: url)
    defer { try? handle.close() }
    
    // Validate before write
    guard data.count <= maxSize else {
        throw DBError.io("Data too large: \(data.count) > \(maxSize)")
    }
    
    // Perform write
    do {
        try handle.write(contentsOf: data)
        try handle.synchronize()
    } catch {
        throw DBError.io("Write failed: \(error.localizedDescription)")
    }
}
```

### Transaction Layer

**Standard Pattern:**
```swift
func commit(tid: UInt64) throws {
    // Validate state
    guard activeTIDs.contains(tid) else {
        throw DBError.transactionAborted(tid)
    }
    
    // Prepare (may throw)
    try prepareTransaction(tid)
    
    // Commit (cleanup on error)
    do {
        try commitPrepared(tid)
    } catch {
        // Rollback on commit failure
        try? rollback(tid)
        throw error
    }
}
```

---

## 🧪 Testing Error Paths

### Test Each Error Condition

```swift
@Test func testInvalidInput() throws {
    let db = Database(config: config)
    
    // Test empty row throws
    #expect(throws: DBError.invalidArgument) {
        try db.insert(into: "test", row: [:], tid: tid)
    }
}

@Test func testResourceCleanup() throws {
    // Test that resources are cleaned up on error
    let db = Database(config: config)
    
    // Inject fault
    FaultInjector.shared.enable(key: "write.fail")
    
    do {
        try db.insert(into: "test", row: row, tid: tid)
        #fail("Should have thrown")
    } catch {
        // Verify resources were cleaned up
        #expect(db.openFileHandles.isEmpty)
    }
}
```

---

## 📊 Error Monitoring

### Log Errors Appropriately

```swift
import os.log

let logger = Logger(subsystem: "com.colibridb", category: "errors")

// Info level for expected errors
logger.info("Table '\(table)' not found")

// Warning for unusual but handled errors
logger.warning("Lock timeout for resource '\(resource)'")

// Error for unexpected errors
logger.error("Unexpected I/O error: \(error)")

// Fault for critical errors
logger.fault("Data corruption detected in page \(pageId)")
```

### Error Metrics

```swift
// Track error frequencies
errorCount[error.type]++

// Monitor error rates
if errorRate > threshold {
    logger.warning("High error rate detected: \(errorRate)")
}
```

---

## ✅ Current Status

### Well-Handled Components

✅ **Config Validation** - Complete, throws early
✅ **CompressionCodec** - Robust, never corrupts
✅ **PathValidator** - Comprehensive validation
✅ **WAL** - CRC validation, graceful degradation
✅ **Transaction** - Clear error types
✅ **Storage** - defer/close patterns

### Standardized Throughout

- All validation uses guard + throw
- All resources use defer for cleanup
- All errors include context
- All critical paths throw (no silent failures)

---

## 🎓 Best Practices Summary

1. ✅ **Validate Early**: Check inputs at function entry
2. ✅ **Use defer**: Guarantee resource cleanup
3. ✅ **Specific Errors**: Use specific error types with context
4. ✅ **Document Errors**: List all possible throws
5. ✅ **Test Error Paths**: Test each error condition
6. ✅ **Clean Up**: No resource leaks on errors
7. ✅ **Log Appropriately**: Use appropriate log levels
8. ✅ **Fail Fast**: Detect problems early

---

**Status**: Standardized error handling patterns applied throughout codebase  
**Quality**: Production-ready error handling  
**Last Updated**: October 18, 2025


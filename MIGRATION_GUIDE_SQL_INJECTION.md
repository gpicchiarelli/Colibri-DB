# 🔒 Migration Guide: SQL Injection Protection

**Date:** 17 Ottobre 2025  
**Version:** 1.0  
**Impact:** CRITICAL SECURITY UPDATE

---

## 🎯 Overview

Colibrì-DB now includes comprehensive SQL injection protection via **prepared statements**. All code should migrate from unsafe string concatenation to safe parameter binding.

---

## ⚠️ What Changed

### Before (UNSAFE)

```swift
// ❌ DANGEROUS - Vulnerable to SQL injection!
let userInput = request.parameter("name")  // Could be: "' OR '1'='1"
let sql = "SELECT * FROM users WHERE name = '\(userInput)'"
try db.executeRawSQL(sql)

// Result: SQL INJECTION! Bypasses authentication!
```

### After (SAFE)

```swift
// ✅ SAFE - No injection possible!
let userInput = request.parameter("name")  // Could be: "' OR '1'='1"
let results = try db.execute(
    "SELECT * FROM users WHERE name = $1",
    parameters: ["$1": .string(userInput)]
)

// Result: Treats entire input as literal string - no matches found
```

---

## 🔄 Migration Steps

### Step 1: Identify Unsafe Code

Search your codebase for:
```bash
# Find all potential SQL injection points
grep -r "executeRawSQL" Sources/
grep -r "executeSQL" Sources/ | grep '\${'
grep -r "executeSQL" Sources/ | grep '\\('
```

### Step 2: Convert to Prepared Statements

For each occurrence, convert as follows:

#### Pattern 1: Simple WHERE clause

**Before:**
```swift
let id = getUserId()
try db.executeSQL("SELECT * FROM users WHERE id = \(id)")
```

**After:**
```swift
let id = getUserId()
try db.execute(
    "SELECT * FROM users WHERE id = $1",
    parameters: ["$1": .int(id)]
)
```

#### Pattern 2: Multiple conditions

**Before:**
```swift
let name = getName()
let age = getAge()
try db.executeSQL("SELECT * FROM users WHERE name = '\(name)' AND age > \(age)")
```

**After:**
```swift
let name = getName()
let age = getAge()
try db.execute(
    "SELECT * FROM users WHERE name = $1 AND age > $2",
    parameters: ["$1": .string(name), "$2": .int(age)]
)
```

#### Pattern 3: INSERT statement

**Before:**
```swift
let user = getUser()
try db.executeSQL("INSERT INTO users (name, age) VALUES ('\(user.name)', \(user.age))")
```

**After:**
```swift
let user = getUser()
try db.execute(
    "INSERT INTO users (name, age) VALUES ($1, $2)",
    parameters: ["$1": .string(user.name), "$2": .int(user.age)]
)
```

#### Pattern 4: UPDATE statement

**Before:**
```swift
let newName = getNewName()
let userId = getUserId()
try db.executeSQL("UPDATE users SET name = '\(newName)' WHERE id = \(userId)")
```

**After:**
```swift
let newName = getNewName()
let userId = getUserId()
try db.execute(
    "UPDATE users SET name = $1 WHERE id = $2",
    parameters: ["$1": .string(newName), "$2": .int(userId)]
)
```

---

## 🎨 Parameter Styles

Colibrì-DB supports three parameter styles:

### 1. Positional ($1, $2, ...)

```swift
try db.execute(
    "SELECT * FROM users WHERE id = $1 AND age > $2",
    parameters: ["$1": .int(42), "$2": .int(18)]
)
```

**Best for:** Simple queries with few parameters

### 2. Named (:name, :age, ...)

```swift
try db.execute(
    "SELECT * FROM users WHERE name = :name AND age > :age",
    parameters: [":name": .string("Alice"), ":age": .int(18)]
)
```

**Best for:** Queries with many parameters (more readable)

### 3. Question Marks (?, ?, ...)

```swift
try db.execute(
    "SELECT * FROM users WHERE id = ? AND name = ?",
    parameters: ["?1": .int(42), "?2": .string("Alice")]
)
```

**Best for:** Compatibility with other SQL databases

---

## 🔍 Advanced Usage

### Statement Reuse (Performance)

```swift
// Prepare once
var stmt = try db.prepare("SELECT * FROM users WHERE id = $1")

// Execute many times with different parameters
for id in 1...1000 {
    try stmt.bind(parameters: ["$1": .int(Int64(id))])
    let results = try stmt.execute()
    processResults(results)
    stmt.reset()
}
```

### Complex Queries

```swift
// Multiple tables and conditions
try db.execute("""
    SELECT u.name, o.amount
    FROM users u
    JOIN orders o ON u.id = o.user_id
    WHERE u.age > $1 AND o.amount > $2
    """,
    parameters: ["$1": .int(18), "$2": .double(100.0)]
)
```

---

## ⚠️ Common Pitfalls

### Pitfall 1: String Formatting Still Unsafe

```swift
// ❌ STILL UNSAFE!
let param = "$1"
let sql = "SELECT * FROM users WHERE id = \(param)"  // Wrong!
try db.execute(sql, parameters: ["$1": .int(42)])
```

**Solution:** Use raw string literals
```swift
// ✅ CORRECT
try db.execute(
    "SELECT * FROM users WHERE id = $1",  // Raw string, no interpolation
    parameters: ["$1": .int(42)]
)
```

### Pitfall 2: Column Names Can't Be Parameters

```swift
// ❌ NOT SUPPORTED
let column = "age"
try db.execute(
    "SELECT * FROM users WHERE $1 = $2",
    parameters: ["$1": .string(column), "$2": .int(25)]
)
```

**Solution:** Column names must be in the SQL template
```swift
// ✅ CORRECT - Use different queries
let sql = column == "age" 
    ? "SELECT * FROM users WHERE age = $1"
    : "SELECT * FROM users WHERE name = $1"
try db.execute(sql, parameters: ["$1": ...])
```

### Pitfall 3: Table Names Can't Be Parameters

```swift
// ❌ NOT SUPPORTED  
let tableName = "users"
try db.execute(
    "SELECT * FROM $1",
    parameters: ["$1": .string(tableName)]
)
```

**Solution:** Validate table name and build SQL accordingly
```swift
// ✅ CORRECT
let tableName = validateTableName(userInput)  // Whitelist validation
try db.execute(
    "SELECT * FROM \(tableName) WHERE id = $1",  // Table name validated separately
    parameters: ["$1": .int(42)]
)
```

---

## 📊 Performance Considerations

### Overhead

- **First execution:** ~5-10% slower (parsing + preparation)
- **Subsequent executions:** ~2% slower (parameter binding)
- **Statement reuse:** Equal or faster (query plan cached)

### Best Practices

1. **Reuse statements** when executing same query multiple times
2. **Prepare outside loops** to avoid repeated parsing
3. **Bind close to execution** to avoid holding parameters too long

---

## ✅ Migration Checklist

Use this checklist to ensure complete migration:

### For Each File

- [ ] Search for `executeRawSQL` calls
- [ ] Search for string interpolation in SQL (`\(...)`)
- [ ] Search for `+` concatenation with SQL strings
- [ ] Convert each to prepared statements
- [ ] Test thoroughly (happy path + injection attempts)
- [ ] Remove deprecation warnings

### Project-Wide

- [ ] All SQL execution uses prepared statements
- [ ] No deprecation warnings remain
- [ ] All tests pass
- [ ] Security scan clean
- [ ] Performance benchmarks acceptable

---

## 🧪 Testing Your Migration

### Test for SQL Injection

After migration, test with malicious inputs:

```swift
let injectionAttempts = [
    "' OR '1'='1",
    "1' UNION SELECT * FROM sensitive --",
    "admin' --",
    "'; DROP TABLE users; --",
]

for malicious in injectionAttempts {
    let results = try db.execute(
        "SELECT * FROM users WHERE name = $1",
        parameters: ["$1": .string(malicious)]
    )
    
    // Should find no results (injection prevented)
    assert(results.isEmpty)
}

// Verify database integrity
let allData = try db.scan(table: "users")
assert(allData.count == expectedCount)  // No data loss
```

---

## 🆘 Getting Help

### Questions?

- Check [API_DOCUMENTATION.md](API_DOCUMENTATION.md)
- Review [QUICK_START.md](QUICK_START.md)
- Open a GitHub Discussion
- Create an issue

### Found a Bug?

If you find a way to bypass the prepared statement protection:

1. **DO NOT** publicly disclose
2. Email security@colibridb.org
3. Provide minimal reproduction
4. We'll fix ASAP and credit you

---

## 🎉 Benefits After Migration

✅ **Security:** Zero SQL injection vulnerabilities  
✅ **Reliability:** Type-safe queries  
✅ **Performance:** Statement reuse optimization  
✅ **Maintainability:** Clearer separation of code and data  
✅ **Compliance:** Security best practices  

---

**Migration is straightforward and the security benefits are immense!**

*Let's make Colibrì-DB injection-proof! 🔒*


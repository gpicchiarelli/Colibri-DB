# 🤝 Contributing to Colibrì-DB - Extended Guide

Thank you for your interest in contributing to Colibrì-DB!

---

## 🎯 How to Contribute

### 1. Code Contributions

#### Setting Up Development Environment

```bash
# Fork and clone
git clone https://github.com/YOUR_USERNAME/Colibri-DB.git
cd Colibri-DB

# Build
make build

# Run tests
make test

# Verify everything works
swift test
```

#### Development Workflow

1. **Create a branch**:
```bash
git checkout -b feature/your-feature-name
```

2. **Make changes** with clear commits:
```bash
git add .
git commit -m "Add feature: brief description

Detailed explanation of what this commit does and why.

Fixes #123"
```

3. **Run tests**:
```bash
make test
swift test --filter YourNewTests
```

4. **Push and create PR**:
```bash
git push origin feature/your-feature-name
```

---

### 2. Testing Contributions

We LOVE test contributions! Every test helps improve quality.

#### Writing Good Tests

```swift
@Suite("Your Feature Tests")
struct YourFeatureTests {
    
    @Test("Test should describe what it tests")
    func testDescriptiveName() throws {
        // Arrange
        let input = createTestInput()
        
        // Act
        let result = functionUnderTest(input)
        
        // Assert
        #expect(result == expectedValue)
    }
    
    @Test("Test edge cases")
    func testEdgeCase() throws {
        #expect(throws: Error.self) {
            try functionThatShouldFail(badInput)
        }
    }
}
```

#### Test Coverage Goals

- **Minimum**: 70% for new code
- **Target**: 80% overall
- **Critical paths**: 95%+

---

### 3. Documentation Contributions

Documentation is as important as code!

#### What to Document

- **API changes**: Update doc comments
- **New features**: Add to README and docs/
- **Examples**: Add to Examples/
- **Tutorials**: Add to docs/wiki/

#### Documentation Style

````swift
/// Brief one-line description.
///
/// Detailed explanation of what this function does,
/// when to use it, and any important considerations.
///
/// - Parameters:
///   - param1: Description of first parameter
///   - param2: Description of second parameter
/// - Returns: Description of return value
/// - Throws: Circumstances under which this throws
///
/// Example usage:
/// ```swift
/// let result = try myFunction(param1: value1, param2: value2)
/// ```
public func myFunction(param1: Type1, param2: Type2) throws -> ReturnType {
    // Implementation
}
````

---

### 4. Performance Contributions

Help make Colibrì-DB faster!

#### Benchmarking Your Changes

```bash
# Run before your changes
make benchmark > before.txt

# Make your changes

# Run after
make benchmark > after.txt

# Compare
diff before.txt after.txt
```

#### Performance Guidelines

- **No regressions**: New code shouldn't slow things down
- **Measure first**: Profile before optimizing
- **Document tradeoffs**: Note any memory/speed tradeoffs

---

## 🎨 Code Style

### Swift Style Guide

```swift
// ✅ GOOD
func calculateTotal(items: [Item], taxRate: Double) -> Double {
    let subtotal = items.reduce(0) { $0 + $1.price }
    return subtotal * (1 + taxRate)
}

// ❌ BAD
func calc(i: [Item], t: Double) -> Double {
    return i.reduce(0){$0+$1.price}*(1+t)
}
```

### Key Principles

1. **Clarity over cleverness**
2. **Descriptive names**
3. **Consistent formatting**
4. **Comment the "why", not the "what"**
5. **Keep functions small and focused**

---

## 🐛 Bug Reports

### Before Reporting

1. Check [existing issues](https://github.com/gpicchiarelli/Colibri-DB/issues)
2. Try latest version
3. Create minimal reproduction

### Bug Report Template

```markdown
**Description**
Clear description of the bug

**To Reproduce**
1. Step 1
2. Step 2
3. See error

**Expected Behavior**
What should happen

**Actual Behavior**
What actually happens

**Environment**
- OS: macOS 14.0
- Swift: 6.0
- Colibrì-DB: v0.1.0

**Code Sample**
```swift
// Minimal reproduction code
```

**Additional Context**
Any other relevant information
```

---

## 💡 Feature Requests

### Proposing Features

1. **Check roadmap**: See if it's already planned
2. **Open discussion**: Start a GitHub Discussion first
3. **Write RFC**: For major features, write a design doc

### Feature Request Template

```markdown
**Feature Description**
Brief description

**Use Case**
Why is this needed? What problem does it solve?

**Proposed Solution**
How do you envision this working?

**Alternatives**
Other ways to solve this problem

**Implementation Ideas**
(Optional) Technical approach
```

---

## 🔍 Code Review Process

### As a Contributor

- **Respond to feedback** within 48 hours
- **Be open** to suggestions
- **Ask questions** if unclear
- **Update PR** based on feedback

### As a Reviewer

- **Be respectful** and constructive
- **Explain reasoning** behind suggestions
- **Approve** when ready
- **Test locally** for important changes

---

## 🎖️ Recognition

Contributors are recognized in:
- AUTHORS.md
- Release notes
- GitHub contributors page
- Project README

---

## 📞 Getting Help

- **Questions?** Open a Discussion
- **Stuck?** Ask in your PR
- **Need guidance?** Tag a maintainer

---

## 🙏 Thank You!

Every contribution, no matter how small, makes Colibrì-DB better.

We appreciate your time and effort! 🎉


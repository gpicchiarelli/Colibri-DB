# Contributing

## Welcome Contributors!

Thank you for your interest in contributing to ColibrìDB! This guide will help you get started with contributing to the project.

## Getting Started

### Prerequisites

Before contributing, ensure you have:

- macOS 13.0 or later
- Xcode 15.0 or later
- Swift 5.9 or later
- Git
- Basic understanding of database systems
- Familiarity with Swift programming

### Development Setup

#### 1. Fork and Clone
```bash
# Fork the repository on GitHub, then clone your fork
git clone https://github.com/your-username/colibridb.git
cd colibridb

# Add upstream remote
git remote add upstream https://github.com/your-org/colibridb.git
```

#### 2. Build the Project
```bash
# Build the project
swift build

# Run tests
swift test

# Build with optimizations
swift build -c release
```

#### 3. Set Up Development Environment
```bash
# Install development dependencies
swift package resolve

# Set up pre-commit hooks
cp .githooks/pre-commit .git/hooks/
chmod +x .git/hooks/pre-commit
```

## Development Workflow

### Branch Strategy

We use a feature branch workflow:

- `main`: Production-ready code
- `develop`: Integration branch for features
- `feature/*`: Feature development branches
- `bugfix/*`: Bug fix branches
- `hotfix/*`: Critical bug fixes

### Creating a Feature

#### 1. Create Feature Branch
```bash
# Start from develop branch
git checkout develop
git pull upstream develop

# Create feature branch
git checkout -b feature/your-feature-name
```

#### 2. Develop Your Feature
```bash
# Make your changes
# ... edit files ...

# Test your changes
swift test

# Build to check for errors
swift build
```

#### 3. Commit Changes
```bash
# Stage changes
git add .

# Commit with descriptive message
git commit -m "feat: add new index type for string prefix searches

- Implement ART (Adaptive Radix Tree) index
- Add configuration options for index type selection
- Update documentation with new index type
- Add tests for ART index functionality"
```

#### 4. Push and Create Pull Request
```bash
# Push feature branch
git push origin feature/your-feature-name

# Create pull request on GitHub
```

### Commit Message Format

We follow the [Conventional Commits](https://www.conventionalcommits.org/) specification:

```
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

#### Types
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes
- `refactor`: Code refactoring
- `test`: Test changes
- `chore`: Maintenance tasks

#### Examples
```bash
# Feature
git commit -m "feat: add support for JSON data type"

# Bug fix
git commit -m "fix: resolve memory leak in buffer pool manager"

# Documentation
git commit -m "docs: update API reference for new query functions"

# Refactoring
git commit -m "refactor: extract common index operations into base class"
```

## Code Style and Standards

### Swift Style Guide

We follow the [Swift API Design Guidelines](https://swift.org/documentation/api-design-guidelines/):

#### Naming Conventions
```swift
// Types: PascalCase
public struct DatabaseConfig { }

// Functions and variables: camelCase
public func createTable(name: String) { }
let bufferPoolSize = 1024

// Constants: camelCase
public let maxConnections = 100

// Private members: camelCase with underscore prefix
private var _internalState: Int
```

#### Documentation
```swift
/// Creates a new table with the specified schema.
///
/// - Parameters:
///   - name: The name of the table to create
///   - schema: The schema definition for the table
///   - database: The database to create the table in
/// - Throws: `ColibriError.tableAlreadyExists` if table already exists
/// - Throws: `ColibriError.invalidSchema` if schema is invalid
public func createTable(_ name: String, schema: CatalogTableSchema, in database: String) throws {
    // Implementation
}
```

#### Error Handling
```swift
// Use specific error types
public enum ColibriError: Error {
    case tableNotFound(String)
    case invalidSchema(String)
    case constraintViolation(String)
}

// Provide descriptive error messages
throw ColibriError.tableNotFound("Table '\(name)' not found in database '\(database)'")
```

### Code Organization

#### File Structure
```
Sources/ColibriCore/
├── Database/           # Core database functionality
├── Storage/            # Storage layer
├── Index/              # Index implementations
├── Catalog/            # Multi-database catalog
├── SQL/                # SQL parsing and execution
├── Constraints/        # Constraint management
├── WAL/                # Write-ahead logging
├── Planner/            # Query planning
├── Integration/        # Platform integration
└── Types.swift         # Core types
```

#### Module Organization
- Keep related functionality together
- Use extensions to organize code
- Separate public API from implementation
- Use protocols for abstraction

### Testing Standards

#### Unit Tests
```swift
import XCTest
@testable import ColibriCore

class DatabaseTests: XCTestCase {
    var database: Database!
    
    override func setUp() {
        super.setUp()
        let config = DBConfig(dataDir: "/tmp/test_db")
        database = try! Database(config: config)
    }
    
    override func tearDown() {
        try? FileManager.default.removeItem(atPath: "/tmp/test_db")
        super.tearDown()
    }
    
    func testCreateTable() throws {
        // Given
        let schema = CatalogTableSchema(columns: [
            CatalogColumnDefinition(name: "id", type: .int, nullable: false)
        ])
        
        // When
        try database.createTable("test_table", schema: schema, in: "test_db")
        
        // Then
        let tables = try database.listTables(in: "test_db")
        XCTAssertTrue(tables.contains("test_table"))
    }
}
```

#### Integration Tests
```swift
class DatabaseIntegrationTests: XCTestCase {
    func testFullWorkflow() throws {
        // Test complete database workflow
        let config = DBConfig(dataDir: "/tmp/integration_test")
        let database = try Database(config: config)
        
        // Create database
        try database.createDatabase("test_db")
        
        // Create table
        let schema = CatalogTableSchema(columns: [
            CatalogColumnDefinition(name: "id", type: .int, nullable: false),
            CatalogColumnDefinition(name: "name", type: .string, nullable: false)
        ])
        try database.createTable("users", schema: schema, in: "test_db")
        
        // Insert data
        let row: Row = ["id": .int(1), "name": .string("John")]
        let rid = try database.insert(into: "users", row: row)
        
        // Query data
        let rows = try database.select(from: "users")
        XCTAssertEqual(rows.count, 1)
        XCTAssertEqual(rows[0]["name"], .string("John"))
    }
}
```

#### Performance Tests
```swift
class PerformanceTests: XCTestCase {
    func testInsertPerformance() throws {
        let config = DBConfig(dataDir: "/tmp/performance_test")
        let database = try Database(config: config)
        
        let schema = CatalogTableSchema(columns: [
            CatalogColumnDefinition(name: "id", type: .int, nullable: false),
            CatalogColumnDefinition(name: "data", type: .string, nullable: false)
        ])
        try database.createTable("test_table", schema: schema, in: "test_db")
        
        measure {
            for i in 0..<1000 {
                let row: Row = ["id": .int(Int64(i)), "data": .string("data\(i)")]
                try! database.insert(into: "test_table", row: row)
            }
        }
    }
}
```

## Documentation Standards

### Code Documentation
- Document all public APIs
- Use Swift documentation comments
- Include parameter descriptions
- Document thrown errors
- Provide usage examples

### README Updates
- Update README for new features
- Include installation instructions
- Provide usage examples
- Document configuration options

### API Documentation
- Keep API reference up to date
- Include code examples
- Document breaking changes
- Provide migration guides

## Pull Request Process

### Before Submitting

#### 1. Code Review Checklist
- [ ] Code follows style guidelines
- [ ] All tests pass
- [ ] New features have tests
- [ ] Documentation is updated
- [ ] No breaking changes (or documented)
- [ ] Performance impact considered

#### 2. Testing
```bash
# Run all tests
swift test

# Run specific test suite
swift test --filter DatabaseTests

# Run performance tests
swift test --filter PerformanceTests

# Run with coverage
swift test --enable-code-coverage
```

#### 3. Code Quality
```bash
# Check for Swift warnings
swift build 2>&1 | grep -i warning

# Run static analysis
swift build -Xswiftc -warn-long-function-bodies=100
```

### Pull Request Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
- [ ] Unit tests added/updated
- [ ] Integration tests added/updated
- [ ] Performance tests added/updated
- [ ] All tests pass

## Documentation
- [ ] API documentation updated
- [ ] README updated
- [ ] Code comments added/updated

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] No breaking changes (or documented)
- [ ] Performance impact considered
```

### Review Process

#### 1. Automated Checks
- All tests must pass
- Code coverage must not decrease
- No Swift warnings
- Documentation builds successfully

#### 2. Code Review
- At least one approval required
- Address all review comments
- Update documentation if needed
- Add tests for edge cases

#### 3. Merge Process
- Squash commits if needed
- Use conventional commit messages
- Update changelog
- Tag release if applicable

## Issue Reporting

### Bug Reports
When reporting bugs, include:

1. **Description**: Clear description of the bug
2. **Steps to Reproduce**: Detailed steps to reproduce
3. **Expected Behavior**: What should happen
4. **Actual Behavior**: What actually happens
5. **Environment**: OS, Swift version, ColibrìDB version
6. **Logs**: Relevant log output
7. **Screenshots**: If applicable

### Feature Requests
When requesting features, include:

1. **Description**: Clear description of the feature
2. **Use Case**: Why this feature is needed
3. **Proposed Solution**: How you think it should work
4. **Alternatives**: Other solutions considered
5. **Additional Context**: Any other relevant information

### Issue Templates
Use the provided issue templates:
- Bug report template
- Feature request template
- Documentation issue template
- Performance issue template

## Development Tools

### IDE Setup
- Use Xcode for development
- Install SwiftLint for code style
- Configure code formatting
- Set up debugging tools

### Debugging
```bash
# Debug build
swift build -c debug

# Run with debugger
lldb .build/debug/coldb-dev

# Profile with Instruments
instruments -t "Time Profiler" .build/debug/coldb-dev
```

### Profiling
```bash
# Profile memory usage
swift build -c debug
leaks .build/debug/coldb-dev

# Profile CPU usage
swift build -c debug
sample .build/debug/coldb-dev
```

## Release Process

### Version Numbering
We use [Semantic Versioning](https://semver.org/):
- `MAJOR`: Breaking changes
- `MINOR`: New features (backward compatible)
- `PATCH`: Bug fixes (backward compatible)

### Release Checklist
- [ ] All tests pass
- [ ] Documentation updated
- [ ] Changelog updated
- [ ] Version number updated
- [ ] Release notes prepared
- [ ] Tag created
- [ ] Release published

### Changelog
Keep a detailed changelog:
- Group changes by type
- Include breaking changes
- Document new features
- List bug fixes
- Credit contributors

## Community Guidelines

### Code of Conduct
- Be respectful and inclusive
- Welcome newcomers
- Provide constructive feedback
- Focus on the code, not the person
- Help others learn and grow

### Communication
- Use GitHub issues for discussions
- Use pull requests for code changes
- Be clear and concise
- Ask questions when unsure
- Share knowledge and experience

### Recognition
- Contributors are recognized in releases
- Significant contributions get special recognition
- All contributors are listed in CONTRIBUTORS.md
- Regular contributors may become maintainers

## Getting Help

### Resources
- [Documentation](https://colibridb.dev/docs)
- [GitHub Issues](https://github.com/your-org/colibridb/issues)
- [Discord Community](https://discord.gg/colibridb)
- [Stack Overflow](https://stackoverflow.com/questions/tagged/colibridb)

### Mentorship
- New contributors can request mentorship
- Experienced contributors can mentor others
- Pair programming sessions available
- Code review sessions for learning

## License

By contributing to ColibrìDB, you agree that your contributions will be licensed under the same license as the project (BSD 3-Clause License).

## Thank You!

Thank you for contributing to ColibrìDB! Your contributions help make the project better for everyone.

---

*For questions about contributing, please open an issue or contact the maintainers.*

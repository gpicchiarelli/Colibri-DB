# Installation & Setup

## System Requirements

### Minimum Requirements
- **Operating System**: macOS 13.0 (Ventura) or later
- **Architecture**: Apple Silicon (M1/M2/M3) or Intel x86_64
- **Memory**: 4 GB RAM (8 GB recommended)
- **Storage**: 1 GB available space
- **Xcode**: 15.0 or later
- **Swift**: 5.9 or later

### Recommended Requirements
- **Operating System**: macOS 14.0 (Sonoma) or later
- **Architecture**: Apple Silicon (M2/M3) for optimal performance
- **Memory**: 16 GB RAM or more
- **Storage**: 10 GB available space (SSD recommended)
- **Xcode**: 15.2 or later
- **Swift**: 5.10 or later

## Installation Methods

### Method 1: Build from Source (Recommended)

#### Prerequisites
```bash
# Install Xcode Command Line Tools
xcode-select --install

# Verify Swift installation
swift --version
```

#### Build Steps
```bash
# Clone the repository
git clone https://github.com/your-org/colibridb.git
cd colibridb

# Build the project
swift build

# Build with optimizations (for production)
swift build -c release

# Run tests
swift test
```

#### Verify Installation
```bash
# Check if the CLI is working
.build/debug/coldb-dev --version

# Or for release build
.build/release/coldb-dev --version
```

### Method 2: Using Swift Package Manager

#### Add to Your Project
```swift
// Package.swift
dependencies: [
    .package(url: "https://github.com/your-org/colibridb.git", from: "1.0.0")
]
```

#### Import in Your Code
```swift
import ColibriCore

// Use ColibrìDB in your application
let config = DBConfig(dataDir: "/path/to/data")
let database = try Database(config: config)
```

### Method 3: Homebrew (Coming Soon)

```bash
# Install via Homebrew (when available)
brew install colibridb

# Start the service
brew services start colibridb
```

## Configuration

### Basic Configuration

Create a configuration file at `~/.colibridb/config.json`:

```json
{
  "dataDir": "/Users/username/.colibridb/data",
  "maxConnectionsLogical": 100,
  "maxConnectionsPhysical": 10,
  "bufferPoolSize": "1GB",
  "logLevel": "INFO",
  "enableWAL": true,
  "checkpointInterval": 300
}
```

### Advanced Configuration

#### Memory Settings
```json
{
  "memory": {
    "bufferPoolSize": "2GB",
    "maxQueryMemory": "512MB",
    "sortMemory": "256MB",
    "hashJoinMemory": "128MB"
  }
}
```

#### Storage Settings
```json
{
  "storage": {
    "pageSize": 8192,
    "maxFileSize": "1GB",
    "compressionEnabled": true,
    "encryptionEnabled": false
  }
}
```

#### Performance Settings
```json
{
  "performance": {
    "parallelWorkers": 4,
    "enableSIMD": true,
    "prefetchPages": 16,
    "batchSize": 1000
  }
}
```

## Environment Setup

### Development Environment

#### 1. Create a Development Directory
```bash
mkdir -p ~/colibridb-dev
cd ~/colibridb-dev
```

#### 2. Initialize a New Project
```bash
# Create a new database project
colibridb init my-project
cd my-project

# This creates:
# ├── databases/
# ├── schemas/
# ├── scripts/
# └── config.json
```

#### 3. Start Development Server
```bash
# Start the development CLI
colibridb dev

# Or with custom config
colibridb dev --config custom-config.json
```

### Production Environment

#### 1. Create Production Directory
```bash
sudo mkdir -p /opt/colibridb
sudo chown $USER:staff /opt/colibridb
cd /opt/colibridb
```

#### 2. Install ColibrìDB
```bash
# Copy the built binary
cp /path/to/colibridb/build/release/coldb /opt/colibridb/bin/
cp /path/to/colibridb/build/release/coldb-dev /opt/colibridb/bin/

# Make executable
chmod +x /opt/colibridb/bin/*
```

#### 3. Create System Service
Create `/Library/LaunchDaemons/com.colibridb.plist`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>Label</key>
    <string>com.colibridb</string>
    <key>ProgramArguments</key>
    <array>
        <string>/opt/colibridb/bin/coldb</string>
        <string>--config</string>
        <string>/opt/colibridb/config.json</string>
    </array>
    <key>RunAtLoad</key>
    <true/>
    <key>KeepAlive</key>
    <true/>
</dict>
</plist>
```

#### 4. Start the Service
```bash
sudo launchctl load /Library/LaunchDaemons/com.colibridb.plist
sudo launchctl start com.colibridb
```

## Database Initialization

### First-Time Setup

#### 1. Create Data Directory
```bash
mkdir -p ~/.colibridb/data
```

#### 2. Initialize System Databases
```bash
# Start the CLI
.build/debug/coldb-dev

# Create system databases
\sql CREATE DATABASE system;
\sql CREATE DATABASE default;
```

#### 3. Create Initial Schema
```sql
-- Connect to default database
\sql USE default;

-- Create a sample table
\sql CREATE TABLE users (
    id INT PRIMARY KEY,
    name STRING NOT NULL,
    email STRING UNIQUE,
    created_at TIMESTAMP DEFAULT NOW()
);
```

### Database Migration

#### From Other Databases
```bash
# Export from existing database
mysqldump -u user -p database_name > export.sql

# Convert and import to ColibrìDB
colibridb migrate --from mysql --input export.sql --output colibridb-schema.sql
colibridb import --file colibridb-schema.sql
```

#### Schema Evolution
```sql
-- Add new column
\sql ALTER TABLE users ADD COLUMN age INT;

-- Modify column
\sql ALTER TABLE users MODIFY COLUMN email STRING(255);

-- Add index
\sql CREATE INDEX idx_users_email ON users(email);
```

## Troubleshooting Installation

### Common Issues

#### 1. Swift Version Mismatch
```bash
# Error: Swift version 5.8 is not supported
# Solution: Update Xcode and Swift
xcode-select --install
swift --version
```

#### 2. Build Failures
```bash
# Clean and rebuild
swift package clean
swift build --verbose

# Check for specific errors
swift build 2>&1 | grep -i error
```

#### 3. Permission Issues
```bash
# Fix data directory permissions
sudo chown -R $USER:staff ~/.colibridb
chmod -R 755 ~/.colibridb
```

#### 4. Port Conflicts
```bash
# Check if port is in use
lsof -i :8080

# Use different port
colibridb dev --port 8081
```

### Performance Issues

#### 1. Slow Startup
- Check available memory
- Verify disk space
- Review log files for errors

#### 2. High Memory Usage
- Adjust buffer pool size
- Check for memory leaks
- Monitor query patterns

#### 3. Disk I/O Issues
- Use SSD storage
- Check disk health
- Optimize configuration

## Verification

### Test Installation
```bash
# Run comprehensive tests
swift test

# Test CLI functionality
.build/debug/coldb-dev --help

# Test database operations
echo "\\sql SELECT 1;" | .build/debug/coldb-dev
```

### Performance Benchmark
```bash
# Run performance tests
.build/debug/coldb-dev
\benchmark suite
\test performance
```

## Next Steps

Now that ColibrìDB is installed and configured:

- [Core Concepts](04-core-concepts.md) - Learn the fundamental concepts
- [Database Management](05-database-management.md) - Start working with databases
- [CLI Reference](07-cli-reference.md) - Master the command-line interface

---

*Having installation issues? Check our [Troubleshooting Guide](10-troubleshooting.md) or [GitHub Issues](https://github.com/your-org/colibridb/issues).*

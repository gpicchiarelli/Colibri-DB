# Troubleshooting

## Common Issues and Solutions

This chapter covers common problems you might encounter when using ColibrìDB and provides solutions to resolve them.

## Installation Issues

### Build Failures

#### Swift Version Mismatch
**Problem**: Build fails with Swift version error.

```bash
error: Swift version 5.8 is not supported
```

**Solution**: Update Xcode and Swift to supported versions.

```bash
# Update Xcode Command Line Tools
xcode-select --install

# Verify Swift version
swift --version

# Clean and rebuild
swift package clean
swift build
```

#### Missing Dependencies
**Problem**: Build fails due to missing dependencies.

```bash
error: could not find dependency 'SomePackage'
```

**Solution**: Update package dependencies.

```bash
# Update package dependencies
swift package update

# Resolve dependencies
swift package resolve

# Clean and rebuild
swift package clean
swift build
```

#### Compilation Errors
**Problem**: Build fails with compilation errors.

```bash
error: cannot find type 'SomeType' in scope
```

**Solution**: Check for missing imports or type conflicts.

```bash
# Build with verbose output
swift build --verbose

# Check for specific errors
swift build 2>&1 | grep -i error

# Clean and rebuild
swift package clean
swift build
```

### Runtime Issues

#### Library Not Found
**Problem**: Runtime error about missing libraries.

```bash
dyld: Library not loaded: @rpath/libSomeLibrary.dylib
```

**Solution**: Check library paths and dependencies.

```bash
# Check library paths
otool -L .build/debug/coldb-dev

# Install missing dependencies
brew install some-library

# Rebuild with correct paths
swift build
```

#### Permission Denied
**Problem**: Permission errors when accessing files.

```bash
error: Permission denied: '/path/to/file'
```

**Solution**: Fix file permissions.

```bash
# Fix data directory permissions
sudo chown -R $USER:staff ~/.colibridb
chmod -R 755 ~/.colibridb

# Fix executable permissions
chmod +x .build/debug/coldb-dev
```

## Database Issues

### Connection Problems

#### Database Not Found
**Problem**: Cannot connect to database.

```bash
error: databaseNotFound("myapp")
```

**Solution**: Create the database first.

```bash
# Create database
colibridb> \sql CREATE DATABASE myapp;

# Switch to database
colibridb> \use myapp;
```

#### Connection Timeout
**Problem**: Connection times out.

```bash
error: connection timeout
```

**Solution**: Check network and configuration.

```bash
# Check connection settings
colibridb> \conf

# Increase timeout
colibridb> \config set connection_timeout 60

# Check network connectivity
ping database-host
```

#### Too Many Connections
**Problem**: Too many active connections.

```bash
error: too many connections
```

**Solution**: Increase connection limits or close unused connections.

```bash
# Check current connections
colibridb> \stats

# Increase connection limit
colibridb> \config set max_connections 200

# Close unused connections
colibridb> \close idle
```

### Data Issues

#### Corrupted Data
**Problem**: Data appears corrupted or inconsistent.

```bash
error: data corruption detected
```

**Solution**: Check data integrity and recover if possible.

```bash
# Check database integrity
colibridb> \check database myapp

# Repair if possible
colibridb> \repair database myapp

# Restore from backup if necessary
colibridb> \restore database myapp from backup
```

#### Missing Data
**Problem**: Data is missing or not visible.

```bash
# Query returns no results
colibridb> \select users
(empty)
```

**Solution**: Check for transaction issues or data isolation.

```bash
# Check transaction status
colibridb> \status

# Commit any pending transactions
colibridb> \commit

# Check for data in different database
colibridb> \use other_database
colibridb> \select users
```

#### Duplicate Data
**Problem**: Duplicate data in tables.

```bash
# Find duplicates
colibridb> \sql SELECT email, COUNT(*) FROM users GROUP BY email HAVING COUNT(*) > 1;
```

**Solution**: Remove duplicates and add constraints.

```bash
# Remove duplicates
colibridb> \sql DELETE FROM users WHERE id NOT IN (SELECT MIN(id) FROM users GROUP BY email);

# Add unique constraint
colibridb> \sql ALTER TABLE users ADD CONSTRAINT uk_users_email UNIQUE (email);
```

## Performance Issues

### Slow Queries

#### Query Timeout
**Problem**: Queries take too long to execute.

```bash
error: query timeout
```

**Solution**: Optimize query or increase timeout.

```bash
# Increase query timeout
colibridb> \config set query_timeout 300

# Analyze slow query
colibridb> \debug sql "SELECT * FROM users WHERE age > 25"

# Optimize query
colibridb> \sql CREATE INDEX idx_users_age ON users(age);
```

#### High CPU Usage
**Problem**: High CPU usage during operations.

```bash
# Check CPU usage
colibridb> \debug performance
CPU Usage: 95%
```

**Solution**: Optimize queries and check for infinite loops.

```bash
# Profile CPU usage
colibridb> \profile start
# ... run operations ...
colibridb> \profile stop

# Check for problematic queries
colibridb> \debug sql "SELECT * FROM users WHERE name LIKE '%'"
```

#### Memory Issues
**Problem**: High memory usage or out of memory.

```bash
# Check memory usage
colibridb> \debug memory
Memory Usage: 95%
```

**Solution**: Increase memory limits or optimize memory usage.

```bash
# Increase memory limits
colibridb> \config set max_memory 4GB

# Check for memory leaks
colibridb> \debug memory leak-check

# Optimize memory usage
colibridb> \config set buffer_pool_size 2GB
```

### Index Issues

#### Missing Index
**Problem**: Queries are slow due to missing indexes.

```bash
# Analyze query performance
colibridb> \debug sql "SELECT * FROM users WHERE email = 'john@example.com'"
Index Used: None (Full Table Scan)
```

**Solution**: Create appropriate indexes.

```bash
# Create index
colibridb> \sql CREATE INDEX idx_users_email ON users(email);

# Verify index usage
colibridb> \debug sql "SELECT * FROM users WHERE email = 'john@example.com'"
Index Used: idx_users_email
```

#### Index Corruption
**Problem**: Index appears corrupted or inconsistent.

```bash
error: index corruption detected
```

**Solution**: Rebuild the index.

```bash
# Rebuild index
colibridb> \sql ALTER INDEX idx_users_email ON users REBUILD;

# Validate index
colibridb> \sql ALTER INDEX idx_users_email ON users VALIDATE;
```

#### Index Not Used
**Problem**: Index exists but is not being used.

```bash
# Check index usage
colibridb> \debug sql "SELECT * FROM users WHERE email = 'john@example.com'"
Index Used: None (Full Table Scan)
```

**Solution**: Check index statistics and query conditions.

```bash
# Update statistics
colibridb> \sql UPDATE STATISTICS FOR INDEX idx_users_email ON users;

# Check index statistics
colibridb> \sql SELECT * FROM information_schema.index_stats WHERE index_name = 'idx_users_email';
```

## Transaction Issues

### Deadlocks

#### Deadlock Detection
**Problem**: Transactions are deadlocked.

```bash
error: deadlock detected
```

**Solution**: Retry the transaction or adjust lock ordering.

```bash
# Check for deadlocks
colibridb> \debug locks
Deadlocks Detected: 5

# Retry transaction
colibridb> \begin
colibridb> \sql UPDATE users SET name = 'John' WHERE id = 1;
colibridb> \commit
```

#### Lock Timeout
**Problem**: Lock acquisition times out.

```bash
error: lock timeout
```

**Solution**: Increase lock timeout or optimize locking.

```bash
# Increase lock timeout
colibridb> \config set lock_timeout 60

# Check lock usage
colibridb> \debug locks
Active Locks: 15
Lock Waits: 2
```

### Transaction Rollback

#### Unexpected Rollback
**Problem**: Transaction is rolled back unexpectedly.

```bash
error: transaction rolled back
```

**Solution**: Check for constraint violations or errors.

```bash
# Check for constraint violations
colibridb> \debug constraints users

# Check for errors
colibridb> \sql SHOW ERRORS;
```

#### Long-Running Transactions
**Problem**: Transactions run for too long.

```bash
# Check transaction duration
colibridb> \status
Transaction Duration: 300s
```

**Solution**: Break down large transactions or optimize operations.

```bash
# Break down large transaction
colibridb> \commit
colibridb> \begin
colibridb> \sql INSERT INTO users (name, email) VALUES ('John', 'john@example.com');
colibridb> \commit
```

## Storage Issues

### Disk Space

#### Out of Disk Space
**Problem**: Not enough disk space for operations.

```bash
error: no space left on device
```

**Solution**: Free up disk space or move data directory.

```bash
# Check disk space
df -h

# Clean up old data
colibridb> \sql DELETE FROM logs WHERE created_at < '2023-01-01';

# Move data directory
colibridb> \config set data_dir /path/to/larger/disk
```

#### File System Errors
**Problem**: File system errors when accessing data.

```bash
error: file system error
```

**Solution**: Check file system integrity and repair if necessary.

```bash
# Check file system
fsck /dev/disk1s1

# Repair file system
fsck -y /dev/disk1s1
```

### Data Corruption

#### Page Corruption
**Problem**: Data pages are corrupted.

```bash
error: page corruption detected
```

**Solution**: Check data integrity and recover if possible.

```bash
# Check database integrity
colibridb> \check database myapp

# Repair corrupted pages
colibridb> \repair database myapp

# Restore from backup if necessary
colibridb> \restore database myapp from backup
```

#### Index Corruption
**Problem**: Index is corrupted.

```bash
error: index corruption detected
```

**Solution**: Rebuild the corrupted index.

```bash
# Rebuild index
colibridb> \sql ALTER INDEX idx_users_email ON users REBUILD;

# Validate index
colibridb> \sql ALTER INDEX idx_users_email ON users VALIDATE;
```

## Configuration Issues

### Invalid Configuration

#### Configuration Syntax Error
**Problem**: Configuration file has syntax errors.

```bash
error: invalid configuration syntax
```

**Solution**: Check configuration file syntax.

```bash
# Validate configuration
colibridb --config-check /path/to/config.json

# Check JSON syntax
python -m json.tool /path/to/config.json
```

#### Invalid Configuration Values
**Problem**: Configuration values are invalid.

```bash
error: invalid configuration value
```

**Solution**: Check configuration values against documentation.

```bash
# Show current configuration
colibridb> \conf

# Reset to defaults
colibridb> \config reset

# Set valid values
colibridb> \config set max_connections 100
```

### Environment Issues

#### Missing Environment Variables
**Problem**: Required environment variables are missing.

```bash
error: environment variable not set
```

**Solution**: Set required environment variables.

```bash
# Set environment variables
export COLIBRIDB_DATA_DIR=/path/to/data
export COLIBRIDB_LOG_LEVEL=INFO

# Check environment variables
colibridb> \env show
```

#### Path Issues
**Problem**: Paths in configuration are invalid.

```bash
error: path not found
```

**Solution**: Check and fix paths in configuration.

```bash
# Check if path exists
ls -la /path/to/data

# Create directory if needed
mkdir -p /path/to/data

# Fix permissions
chmod 755 /path/to/data
```

## Network Issues

### Connection Problems

#### Network Timeout
**Problem**: Network operations timeout.

```bash
error: network timeout
```

**Solution**: Check network connectivity and increase timeouts.

```bash
# Check network connectivity
ping database-host

# Increase network timeout
colibridb> \config set network_timeout 60

# Check network configuration
colibridb> \config show
```

#### Connection Refused
**Problem**: Connection is refused.

```bash
error: connection refused
```

**Solution**: Check if database is running and accessible.

```bash
# Check if database is running
ps aux | grep coldb

# Check port accessibility
telnet database-host 5432

# Start database if not running
colibridb --daemon
```

### Security Issues

#### Authentication Failed
**Problem**: Authentication fails.

```bash
error: authentication failed
```

**Solution**: Check credentials and authentication configuration.

```bash
# Check user credentials
colibridb> \sql SELECT * FROM information_schema.users;

# Reset password
colibridb> \sql ALTER USER john SET PASSWORD 'newpassword';
```

#### Permission Denied
**Problem**: Permission denied for operations.

```bash
error: permission denied
```

**Solution**: Check user permissions and grant necessary privileges.

```bash
# Check user permissions
colibridb> \sql SELECT * FROM information_schema.user_privileges;

# Grant necessary privileges
colibridb> \sql GRANT SELECT, INSERT ON myapp.* TO john;
```

## Debugging Techniques

### Log Analysis

#### Enable Debug Logging
Enable detailed logging for debugging.

```bash
# Set log level to DEBUG
colibridb> \config set log_level DEBUG

# Check log files
tail -f ~/.colibridb/logs/colibridb.log
```

#### Log Filtering
Filter logs for specific issues.

```bash
# Filter for error messages
grep "ERROR" ~/.colibridb/logs/colibridb.log

# Filter for specific operations
grep "SELECT" ~/.colibridb/logs/colibridb.log
```

### Performance Debugging

#### CPU Profiling
Profile CPU usage to identify bottlenecks.

```bash
# Start CPU profiling
colibridb> \profile start

# Run operations
colibridb> \sql SELECT * FROM users WHERE age > 25;

# Stop profiling
colibridb> \profile stop
```

#### Memory Debugging
Debug memory usage and leaks.

```bash
# Check memory usage
colibridb> \debug memory

# Check for memory leaks
colibridb> \debug memory leak-check

# Monitor memory usage
colibridb> \monitor memory
```

### Query Debugging

#### Query Analysis
Analyze query performance and execution.

```bash
# Analyze query
colibridb> \debug sql "SELECT * FROM users WHERE age > 25"

# Show query plan
colibridb> \sql EXPLAIN SELECT * FROM users WHERE age > 25;

# Profile query
colibridb> \profile sql "SELECT * FROM users WHERE age > 25"
```

#### Index Analysis
Analyze index usage and performance.

```bash
# Check index usage
colibridb> \debug constraints users

# Analyze index performance
colibridb> \profile constraints

# Check index statistics
colibridb> \sql SELECT * FROM information_schema.index_stats;
```

## Recovery Procedures

### Data Recovery

#### From Backup
Restore data from backup.

```bash
# List available backups
colibridb> \backup list

# Restore from backup
colibridb> \restore database myapp from backup_20230120_150000

# Verify restoration
colibridb> \sql SELECT COUNT(*) FROM users;
```

#### From WAL
Recover data from write-ahead log.

```bash
# Check WAL status
colibridb> \sql SHOW WAL STATUS;

# Recover from WAL
colibridb> \recover from wal

# Verify recovery
colibridb> \sql SELECT COUNT(*) FROM users;
```

### System Recovery

#### Database Repair
Repair corrupted database.

```bash
# Check database integrity
colibridb> \check database myapp

# Repair database
colibridb> \repair database myapp

# Verify repair
colibridb> \check database myapp
```

#### Index Repair
Repair corrupted indexes.

```bash
# Rebuild all indexes
colibridb> \sql ALTER TABLE users REBUILD INDEXES;

# Validate indexes
colibridb> \sql ALTER TABLE users VALIDATE INDEXES;
```

## Prevention Strategies

### Monitoring

#### Set Up Monitoring
Set up continuous monitoring to detect issues early.

```bash
# Start monitoring
colibridb> \monitor stats

# Set up alerts
colibridb> \config set alerts.enabled true
colibridb> \config set alerts.response_time_threshold 100
```

#### Regular Maintenance
Perform regular maintenance to prevent issues.

```bash
# Regular maintenance tasks
colibridb> \analyze all
colibridb> \vacuum start
colibridb> \check database myapp
```

### Backup Strategy

#### Regular Backups
Set up regular backups to prevent data loss.

```bash
# Create backup
colibridb> \backup database myapp to /path/to/backup

# Schedule regular backups
crontab -e
# Add: 0 2 * * * colibridb --backup myapp
```

#### Backup Verification
Verify backups to ensure they can be restored.

```bash
# Verify backup
colibridb> \backup verify /path/to/backup

# Test restore
colibridb> \restore database test from /path/to/backup
```

## Getting Help

### Documentation
- Check this troubleshooting guide
- Review the [API Reference](11-api-reference.md)
- Consult the [Performance Tuning](09-performance-tuning.md) guide

### Community Support
- [GitHub Issues](https://github.com/your-org/colibridb/issues)
- [Discord Community](https://discord.gg/colibridb)
- [Stack Overflow](https://stackoverflow.com/questions/tagged/colibridb)

## Next Steps

Now that you can troubleshoot issues effectively:

- [Performance Tuning](09-performance-tuning.md) - Optimize performance
- [Development Tools](08-development-tools.md) - Use debugging tools
- [API Reference](11-api-reference.md) - Access programmatic interfaces

---

*For advanced troubleshooting techniques and custom solutions, see the [API Reference](11-api-reference.md).*

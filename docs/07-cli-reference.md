# CLI Reference

## Command-Line Interface

ColibrìDB provides two command-line interfaces: `coldb` for production use and `coldb-dev` for development and debugging. This reference covers all available commands and options.

## Getting Started

### Starting the CLI

#### Production CLI
```bash
# Start production CLI
.build/release/coldb

# With configuration file
.build/release/coldb --config /path/to/config.json

# Connect to specific database
.build/release/coldb --database myapp
```

#### Development CLI
```bash
# Start development CLI
.build/debug/coldb-dev

# With custom data directory
.build/debug/coldb-dev --data-dir /path/to/data

# With verbose output
.build/debug/coldb-dev --verbose
```

### CLI Options

#### Global Options
```bash
--help, -h          Show help information
--version, -v       Show version information
--config FILE       Use configuration file
--data-dir DIR      Set data directory
--verbose           Enable verbose output
--quiet             Suppress non-error output
```

#### Connection Options
```bash
--database NAME     Connect to specific database
--host HOST         Database host (for remote connections)
--port PORT         Database port (for remote connections)
--user USER         Database user
--password PASS     Database password
```

## Basic Commands

### Help Commands

#### \help
Shows all available commands.

```bash
colibridb> \help
Commands:
  \help                              Show this help
  \conf                              Show active configuration
  \dt                                List tables
  \sql <statement>                   Execute SQL statement
  ...
```

#### \conf
Shows current configuration.

```bash
colibridb> \conf
Configuration:
  Data Directory: /Users/username/.colibridb/data
  Max Connections: 100
  Buffer Pool Size: 1GB
  WAL Enabled: true
  ...
```

### Database Commands

#### \databases
Lists all databases.

```bash
colibridb> \databases
Databases:
  myapp
  analytics
  logs
```

#### \use
Switches to a specific database.

```bash
colibridb> \use myapp
Switched to database 'myapp'
```

#### \dbinfo
Shows detailed information about a database.

```bash
colibridb> \dbinfo myapp
Database: myapp
  Tables: 5
  Indexes: 12
  Size: 2.5MB
  Created: 2023-01-15 10:30:00
  Last Modified: 2023-01-20 14:45:00
```

### Table Commands

#### \dt
Lists all tables in the current database.

```bash
colibridb> \dt
Tables:
  users
  products
  orders
  categories
```

#### \d table_name
Shows detailed information about a table.

```bash
colibridb> \d users
Table: users
  Columns:
    id (INT, PRIMARY KEY)
    name (STRING, NOT NULL)
    email (STRING, UNIQUE)
    created_at (TIMESTAMP, DEFAULT NOW())
  Indexes:
    idx_users_email (UNIQUE)
    idx_users_created_at
  Rows: 1,250
  Size: 156KB
```

#### \create table
Creates a new table.

```bash
colibridb> \create table products (id INT, name STRING, price DECIMAL)
Table 'products' created successfully
```

#### \drop table
Drops a table.

```bash
colibridb> \drop table products
Table 'products' dropped successfully
```

#### \alter table
Modifies a table structure.

```bash
colibridb> \alter table users add column phone STRING
Column 'phone' added to table 'users'

colibridb> \alter table users drop column phone
Column 'phone' dropped from table 'users'
```

### Data Commands

#### \insert
Inserts data into a table.

```bash
colibridb> \insert users name=John,email=john@example.com
1 row inserted

colibridb> \insert users name=Jane,email=jane@example.com,age=25
1 row inserted
```

#### \select
Queries data from a table.

```bash
colibridb> \select users
id | name | email              | age
---|------|--------------------|----
1  | John | john@example.com   | NULL
2  | Jane | jane@example.com   | 25

colibridb> \select users where age > 20
id | name | email              | age
---|------|--------------------|----
2  | Jane | jane@example.com   | 25
```

#### \update
Updates data in a table.

```bash
colibridb> \update users set age=30 where name=John
1 row updated
```

#### \delete
Deletes data from a table.

```bash
colibridb> \delete users where age < 18
0 rows deleted
```

#### \scan
Scans all rows in a table.

```bash
colibridb> \scan users
Row 1: id=1, name=John, email=john@example.com, age=30
Row 2: id=2, name=Jane, email=jane@example.com, age=25
```

## SQL Commands

### \sql
Executes SQL statements.

```bash
colibridb> \sql CREATE TABLE products (id INT, name STRING, price DECIMAL)
SQL executed successfully

colibridb> \sql INSERT INTO products VALUES (1, 'Laptop', 999.99)
SQL executed successfully

colibridb> \sql SELECT * FROM products WHERE price > 500
id | name   | price
---|--------|-------
1  | Laptop | 999.99
```

### Multi-line SQL
Execute multi-line SQL statements.

```bash
colibridb> \sql
Enter SQL (end with ';'):
> CREATE TABLE orders (
>   id INT PRIMARY KEY,
>   user_id INT,
>   total_amount DECIMAL(10,2),
>   order_date TIMESTAMP DEFAULT NOW()
> );
SQL executed successfully
```

## Index Commands

### \indexes
Lists all indexes on a table.

```bash
colibridb> \indexes users
Indexes on table 'users':
  idx_users_email (UNIQUE, HASH)
  idx_users_created_at (BTREE)
  idx_users_name (ART)
```

### \create index
Creates an index.

```bash
colibridb> \create index idx_users_email on users(email) using hash
Index 'idx_users_email' created successfully

colibridb> \create index idx_products_category on products(category_id) using btree
Index 'idx_products_category' created successfully
```

### \drop index
Drops an index.

```bash
colibridb> \drop index idx_users_email on users
Index 'idx_users_email' dropped successfully
```

### Index Operations

#### \index search
Searches using an index.

```bash
colibridb> \index search users idx_users_email john@example.com
Found 1 row:
id=1, name=John, email=john@example.com
```

#### \index range
Performs range queries using an index.

```bash
colibridb> \index range products idx_products_price 100 500
Found 3 rows:
id=2, name=Mouse, price=25.99
id=3, name=Keyboard, price=75.50
id=4, name=Monitor, price=299.99
```

#### \index validate
Validates index integrity.

```bash
colibridb> \index validate users idx_users_email
Index 'idx_users_email' is valid
```

#### \index rebuild
Rebuilds an index.

```bash
colibridb> \index rebuild users idx_users_email
Index 'idx_users_email' rebuilt successfully
```

## Transaction Commands

### \begin
Starts a new transaction.

```bash
colibridb> \begin
Transaction started (ID: 12345)
```

### \commit
Commits the current transaction.

```bash
colibridb> \commit
Transaction 12345 committed successfully
```

### \rollback
Rolls back the current transaction.

```bash
colibridb> \rollback
Transaction 12345 rolled back successfully
```

### \status
Shows transaction status.

```bash
colibridb> \status
Current Transaction: 12345
Status: Active
Started: 2023-01-20 15:30:00
```

## Maintenance Commands

### \flush
Flushes data to disk.

```bash
colibridb> \flush all
All buffers flushed to disk

colibridb> \flush table users
Table 'users' flushed to disk

colibridb> \flush index users idx_users_email
Index 'idx_users_email' flushed to disk
```

### \checkpoint
Creates a checkpoint.

```bash
colibridb> \checkpoint
Checkpoint created successfully
```

### \vacuum
Runs database maintenance.

```bash
colibridb> \vacuum start
Vacuum started

colibridb> \vacuum stop
Vacuum stopped

colibridb> \vacuum stats
Vacuum Statistics:
  Runs: 5
  Pages Compacted: 1,250
  Bytes Reclaimed: 2.5MB
  Last Run: 2023-01-20 14:30:00
```

### \analyze
Updates table statistics.

```bash
colibridb> \analyze users
Table 'users' analyzed successfully

colibridb> \analyze all
All tables analyzed successfully
```

## Performance Commands

### \stats
Shows performance statistics.

```bash
colibridb> \stats
Performance Statistics:
  Buffer Pool Hit Rate: 95.2%
  Query Execution Time: 12.5ms avg
  Active Connections: 5
  Memory Usage: 256MB
```

### \bp
Shows buffer pool statistics.

```bash
colibridb> \bp
Buffer Pool Statistics:
  Total Pages: 1,024
  Used Pages: 856
  Free Pages: 168
  Hit Rate: 95.2%
  Evictions: 45
```

### \explain
Shows query execution plan.

```bash
colibridb> \explain SELECT * FROM users WHERE email = 'john@example.com'
Query Plan:
  Index Scan (idx_users_email)
    Filter: email = 'john@example.com'
    Cost: 0.5
    Rows: 1
```

## Development Commands

### Debug Commands

#### \debug memory
Shows memory usage information.

```bash
colibridb> \debug memory
Memory Analysis:
  Resident Size: 14.47 MB
  Virtual Size: 425.22 MB
  Peak Resident Size: 14.47 MB
  Timestamp: 2023-01-20 15:30:00
```

#### \debug performance
Shows performance metrics.

```bash
colibridb> \debug performance
Performance Analysis:
  CPU Usage: 15.2%
  Memory Usage: 256MB
  Disk I/O: 45.2MB/s
  Query Throughput: 125 queries/s
```

#### \debug constraints
Shows constraint information.

```bash
colibridb> \debug constraints users
Constraints on table 'users':
  PRIMARY KEY (id)
  UNIQUE (email)
  CHECK (age >= 0)
```

### Monitoring Commands

#### \monitor stats
Starts real-time statistics monitoring.

```bash
colibridb> \monitor stats
Monitoring started for 60.0 seconds with 1.0s interval
Press Ctrl+C to stop early

Time: 15:30:00 | Queries: 125/s | Memory: 256MB | CPU: 15.2%
Time: 15:30:01 | Queries: 130/s | Memory: 258MB | CPU: 16.1%
...
```

#### \monitor memory
Monitors memory usage.

```bash
colibridb> \monitor memory
Memory Monitoring:
  Current: 256MB
  Peak: 280MB
  Growth Rate: 2MB/min
```

### Profiling Commands

#### \profile start
Starts CPU profiling.

```bash
colibridb> \profile start
CPU profiling started
```

#### \profile stop
Stops CPU profiling.

```bash
colibridb> \profile stop
CPU profiling stopped
Results saved to profile_20230120_153000.json
```

#### \profile memory
Profiles memory operations.

```bash
colibridb> \profile memory insert
Memory profiling started for 'insert' operation
```

### Testing Commands

#### \test run
Runs all tests.

```bash
colibridb> \test run
Running all tests...
✓ Unit Tests: 45/45 passed
✓ Integration Tests: 12/12 passed
✓ Performance Tests: 8/8 passed
Total: 65/65 tests passed
```

#### \test unit
Runs unit tests only.

```bash
colibridb> \test unit
Running unit tests...
✓ Data Types: 15/15 passed
✓ Query Parser: 20/20 passed
✓ Index Manager: 10/10 passed
Total: 45/45 unit tests passed
```

#### \test performance
Runs performance tests.

```bash
colibridb> \test performance
Running performance tests...
✓ Query Performance: 8/8 passed
✓ Memory Usage: 5/5 passed
✓ Concurrency: 3/3 passed
Total: 16/16 performance tests passed
```

### Benchmark Commands

#### \benchmark sql
Benchmarks SQL operations.

```bash
colibridb> \benchmark sql
SQL Benchmark Results:
  SELECT: 1,250 ops/s
  INSERT: 850 ops/s
  UPDATE: 420 ops/s
  DELETE: 380 ops/s
```

#### \benchmark suite
Runs comprehensive benchmarks.

```bash
colibridb> \benchmark suite
Comprehensive Benchmark Suite:
  SQL Operations: 1,250 ops/s
  Index Operations: 2,100 ops/s
  Memory Allocation: 15.2ms avg
  Data Types: 8,500 ops/s
```

## Import/Export Commands

### \import
Imports data from files.

```bash
colibridb> \import users.csv into users
Importing from users.csv...
1000 rows imported successfully

colibridb> \import orders.json into orders
Importing from orders.json...
500 rows imported successfully
```

### \export
Exports data to files.

```bash
colibridb> \export users to users_backup.csv
Exporting table 'users'...
1000 rows exported to users_backup.csv

colibridb> \export orders to orders_backup.json
Exporting table 'orders'...
500 rows exported to orders_backup.json
```

## Utility Commands

### \clear
Clears the screen.

```bash
colibridb> \clear
```

### \history
Shows command history.

```bash
colibridb> \history
1. \help
2. \use myapp
3. \dt
4. \select users
5. \sql CREATE TABLE products
```

### \repeat
Repeats the last command.

```bash
colibridb> \repeat
Executing: \select users
id | name | email
---|------|-------
1  | John | john@example.com
```

### \timing
Toggles query timing.

```bash
colibridb> \timing on
Query timing enabled

colibridb> \select users
id | name | email
---|------|-------
1  | John | john@example.com
(1 row, 0.5ms)
```

## Configuration Commands

### \set
Sets configuration variables.

```bash
colibridb> \set max_rows 100
Variable 'max_rows' set to 100

colibridb> \set output_format json
Variable 'output_format' set to json
```

### \unset
Unsets configuration variables.

```bash
colibridb> \unset max_rows
Variable 'max_rows' unset
```

### \show
Shows configuration variables.

```bash
colibridb> \show
Configuration Variables:
  max_rows: 100
  output_format: table
  timing: on
```

## Exit Commands

### \exit
Exits the CLI.

```bash
colibridb> \exit
Goodbye!
```

### \quit
Alternative exit command.

```bash
colibridb> \quit
Goodbye!
```

## Command Line Options

### Production CLI Options

```bash
coldb [OPTIONS] [COMMAND]

Options:
  --help, -h              Show help information
  --version, -v           Show version information
  --config FILE           Use configuration file
  --data-dir DIR          Set data directory
  --database NAME         Connect to specific database
  --host HOST             Database host
  --port PORT             Database port
  --user USER             Database user
  --password PASS         Database password
  --verbose               Enable verbose output
  --quiet                 Suppress non-error output
  --log-level LEVEL       Set log level (DEBUG, INFO, WARN, ERROR)
  --pid-file FILE         Write PID to file
  --daemon                Run as daemon
```

### Development CLI Options

```bash
coldb-dev [OPTIONS] [COMMAND]

Options:
  --help, -h              Show help information
  --version, -v           Show version information
  --config FILE           Use configuration file
  --data-dir DIR          Set data directory
  --database NAME         Connect to specific database
  --verbose               Enable verbose output
  --debug                 Enable debug mode
  --profile               Enable profiling
  --trace                 Enable tracing
  --benchmark             Run benchmarks on startup
```

## Scripting and Automation

### Batch Mode
Execute commands from a file.

```bash
# Execute SQL file
coldb --file script.sql

# Execute command file
coldb-dev --file commands.txt
```

### Output Formats
Control output format for scripting.

```bash
# JSON output
coldb --output-format json --execute "SELECT * FROM users"

# CSV output
coldb --output-format csv --execute "SELECT * FROM users"

# Table output (default)
coldb --output-format table --execute "SELECT * FROM users"
```

### Exit Codes
CLI returns appropriate exit codes for scripting.

```bash
# Success
echo $?  # 0

# Error
echo $?  # 1

# Usage error
echo $?  # 2
```

## Next Steps

Now that you can use the CLI effectively:

- [Database Management](05-database-management.md) - Apply CLI commands to manage databases
- [Development Tools](08-development-tools.md) - Use advanced development features
- [Performance Tuning](09-performance-tuning.md) - Optimize using CLI tools

---

*For advanced CLI features and scripting, see the [API Reference](11-api-reference.md).*

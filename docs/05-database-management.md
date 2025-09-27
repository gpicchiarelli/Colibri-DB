# Database Management

## Working with Databases

ColibrìDB's multi-database architecture allows you to manage multiple independent databases within a single instance. This chapter covers creating, managing, and working with databases.

## Database Operations

### Creating Databases

#### Basic Database Creation
```sql
-- Create a new database
CREATE DATABASE myapp;

-- Create with specific options
CREATE DATABASE analytics 
    WITH (
        encoding = 'UTF8',
        collation = 'en_US.UTF8'
    );
```

#### Database Naming Rules
- **Length**: 1-64 characters
- **Characters**: Letters, numbers, underscores, hyphens
- **Case**: Case-sensitive
- **Reserved Words**: Cannot use SQL keywords

```sql
-- Valid names
CREATE DATABASE user_management;
CREATE DATABASE analytics-2024;
CREATE DATABASE AppData;

-- Invalid names
CREATE DATABASE 123database;     -- Cannot start with number
CREATE DATABASE user management; -- Cannot contain spaces
CREATE DATABASE SELECT;          -- Cannot use reserved word
```

### Switching Between Databases

#### Using the USE Statement
```sql
-- Switch to a specific database
USE myapp;

-- All subsequent operations will be performed in 'myapp'
CREATE TABLE users (id INT, name STRING);
```

#### Database Context in CLI
```bash
# Start CLI and connect to specific database
colibridb connect --database myapp

# Or switch databases within CLI
colibridb> USE analytics;
```

### Listing Databases

#### View All Databases
```sql
-- List all databases
SHOW DATABASES;

-- Or using CLI command
\databases
```

#### Database Information
```sql
-- Get detailed information about a database
DESCRIBE DATABASE myapp;

-- Or using CLI command
\dbinfo myapp
```

### Dropping Databases

#### Basic Drop
```sql
-- Drop a database (removes all data)
DROP DATABASE myapp;
```

#### Drop with Confirmation
```sql
-- Drop with explicit confirmation
DROP DATABASE myapp CASCADE;

-- CLI will ask for confirmation
\drop database myapp
```

## Table Management

### Creating Tables

#### Basic Table Creation
```sql
-- Create a simple table
CREATE TABLE users (
    id INT PRIMARY KEY,
    name STRING NOT NULL,
    email STRING UNIQUE
);
```

#### Advanced Table Creation
```sql
-- Create table with comprehensive options
CREATE TABLE products (
    id INT PRIMARY KEY,
    name STRING(255) NOT NULL,
    description TEXT,
    price DECIMAL(10,2) NOT NULL,
    category_id INT,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW(),
    
    -- Constraints
    CONSTRAINT chk_price CHECK (price >= 0),
    CONSTRAINT fk_category FOREIGN KEY (category_id) REFERENCES categories(id)
);
```

#### Table Options
```sql
-- Create table with storage options
CREATE TABLE logs (
    id INT PRIMARY KEY,
    message TEXT,
    timestamp TIMESTAMP DEFAULT NOW()
) WITH (
    storage_engine = 'LSM',
    compression = 'LZ4',
    encryption = 'AES256'
);
```

### Modifying Tables

#### Adding Columns
```sql
-- Add a single column
ALTER TABLE users ADD COLUMN phone STRING;

-- Add multiple columns
ALTER TABLE users 
    ADD COLUMN phone STRING,
    ADD COLUMN address TEXT,
    ADD COLUMN birth_date DATE;
```

#### Modifying Columns
```sql
-- Change column type
ALTER TABLE users MODIFY COLUMN email STRING(255);

-- Change column constraints
ALTER TABLE users MODIFY COLUMN name STRING(100) NOT NULL;

-- Set default value
ALTER TABLE users MODIFY COLUMN created_at TIMESTAMP DEFAULT NOW();
```

#### Dropping Columns
```sql
-- Drop a single column
ALTER TABLE users DROP COLUMN phone;

-- Drop multiple columns
ALTER TABLE users 
    DROP COLUMN address,
    DROP COLUMN birth_date;
```

#### Renaming Tables
```sql
-- Rename a table
ALTER TABLE users RENAME TO customers;

-- Or using RENAME statement
RENAME TABLE users TO customers;
```

### Dropping Tables

#### Basic Drop
```sql
-- Drop a table
DROP TABLE users;
```

#### Drop with Constraints
```sql
-- Drop table and all its constraints
DROP TABLE users CASCADE;

-- Drop only if exists
DROP TABLE IF EXISTS users;
```

## Index Management

### Creating Indexes

#### Basic Index Creation
```sql
-- Create a simple index
CREATE INDEX idx_users_email ON users(email);

-- Create unique index
CREATE UNIQUE INDEX idx_users_username ON users(username);
```

#### Index Types
```sql
-- B+Tree index (default)
CREATE INDEX idx_users_name ON users(name) USING BTREE;

-- Hash index
CREATE INDEX idx_users_id ON users(id) USING HASH;

-- ART index for string prefixes
CREATE INDEX idx_users_email_prefix ON users(email) USING ART;

-- LSM-Tree index for write-heavy workloads
CREATE INDEX idx_logs_timestamp ON logs(timestamp) USING LSM;
```

#### Composite Indexes
```sql
-- Create composite index
CREATE INDEX idx_orders_user_date ON orders(user_id, order_date);

-- Partial index
CREATE INDEX idx_active_users ON users(email) WHERE is_active = true;
```

### Managing Indexes

#### Listing Indexes
```sql
-- List all indexes on a table
SHOW INDEXES FROM users;

-- Or using CLI command
\indexes users
```

#### Dropping Indexes
```sql
-- Drop an index
DROP INDEX idx_users_email;

-- Drop index on specific table
DROP INDEX idx_users_email ON users;
```

#### Index Maintenance
```sql
-- Rebuild an index
ALTER INDEX idx_users_email ON users REBUILD;

-- Analyze index statistics
ANALYZE INDEX idx_users_email ON users;
```

## View Management

### Creating Views

#### Simple Views
```sql
-- Create a simple view
CREATE VIEW active_users AS
SELECT id, name, email
FROM users
WHERE is_active = true;
```

#### Complex Views
```sql
-- Create a complex view with joins
CREATE VIEW user_orders AS
SELECT 
    u.id as user_id,
    u.name as user_name,
    o.id as order_id,
    o.total_amount,
    o.order_date
FROM users u
JOIN orders o ON u.id = o.user_id
WHERE o.status = 'completed';
```

#### Updatable Views
```sql
-- Create an updatable view
CREATE VIEW user_contacts AS
SELECT id, name, email, phone
FROM users
WHERE email IS NOT NULL;

-- Insert through view
INSERT INTO user_contacts (id, name, email) 
VALUES (1, 'John Doe', 'john@example.com');
```

### Managing Views

#### Listing Views
```sql
-- List all views
SHOW VIEWS;

-- List views in current database
SHOW VIEWS FROM myapp;
```

#### Dropping Views
```sql
-- Drop a view
DROP VIEW active_users;

-- Drop view if exists
DROP VIEW IF EXISTS active_users;
```

## Sequence Management

### Creating Sequences

#### Basic Sequence
```sql
-- Create a simple sequence
CREATE SEQUENCE user_id_seq;

-- Use sequence in table
CREATE TABLE users (
    id INT DEFAULT NEXT VALUE FOR user_id_seq,
    name STRING
);
```

#### Advanced Sequence
```sql
-- Create sequence with options
CREATE SEQUENCE order_id_seq
    START WITH 1000
    INCREMENT BY 1
    MINVALUE 1000
    MAXVALUE 999999
    CYCLE;
```

### Managing Sequences

#### Sequence Operations
```sql
-- Get next value
SELECT NEXT VALUE FOR user_id_seq;

-- Get current value
SELECT CURRENT VALUE FOR user_id_seq;

-- Reset sequence
ALTER SEQUENCE user_id_seq RESTART WITH 1;
```

#### Dropping Sequences
```sql
-- Drop a sequence
DROP SEQUENCE user_id_seq;
```

## Data Management

### Inserting Data

#### Single Row Insert
```sql
-- Insert a single row
INSERT INTO users (id, name, email) 
VALUES (1, 'John Doe', 'john@example.com');
```

#### Multiple Row Insert
```sql
-- Insert multiple rows
INSERT INTO users (id, name, email) VALUES 
    (1, 'John Doe', 'john@example.com'),
    (2, 'Jane Smith', 'jane@example.com'),
    (3, 'Bob Johnson', 'bob@example.com');
```

#### Insert with Defaults
```sql
-- Insert using default values
INSERT INTO users (name, email) 
VALUES ('Alice Brown', 'alice@example.com');
-- id will use default value from sequence
```

### Updating Data

#### Basic Update
```sql
-- Update a single row
UPDATE users 
SET email = 'newemail@example.com' 
WHERE id = 1;
```

#### Multiple Column Update
```sql
-- Update multiple columns
UPDATE users 
SET name = 'John Smith', 
    email = 'johnsmith@example.com',
    updated_at = NOW()
WHERE id = 1;
```

#### Conditional Update
```sql
-- Update with conditions
UPDATE users 
SET is_active = false 
WHERE last_login < '2023-01-01';
```

### Deleting Data

#### Basic Delete
```sql
-- Delete specific rows
DELETE FROM users WHERE id = 1;
```

#### Conditional Delete
```sql
-- Delete with conditions
DELETE FROM users 
WHERE last_login < '2023-01-01' 
AND is_active = false;
```

#### Truncate Table
```sql
-- Remove all data from table
TRUNCATE TABLE users;

-- Truncate with reset sequence
TRUNCATE TABLE users RESTART IDENTITY;
```

## Backup and Recovery

### Database Backup

#### Full Backup
```sql
-- Create full database backup
BACKUP DATABASE myapp TO '/path/to/backup/myapp_backup.db';
```

#### Incremental Backup
```sql
-- Create incremental backup
BACKUP DATABASE myapp INCREMENTAL TO '/path/to/backup/myapp_incr.db';
```

#### Table Backup
```sql
-- Backup specific table
BACKUP TABLE users TO '/path/to/backup/users_backup.db';
```

### Database Recovery

#### Full Recovery
```sql
-- Restore from full backup
RESTORE DATABASE myapp FROM '/path/to/backup/myapp_backup.db';
```

#### Point-in-Time Recovery
```sql
-- Restore to specific point in time
RESTORE DATABASE myapp 
FROM '/path/to/backup/myapp_backup.db'
TO TIMESTAMP '2023-01-15 14:30:00';
```

## Performance Optimization

### Table Optimization

#### Analyze Tables
```sql
-- Analyze table statistics
ANALYZE TABLE users;

-- Analyze all tables in database
ANALYZE DATABASE myapp;
```

#### Rebuild Tables
```sql
-- Rebuild table to optimize storage
ALTER TABLE users REBUILD;
```

### Index Optimization

#### Rebuild Indexes
```sql
-- Rebuild specific index
ALTER INDEX idx_users_email ON users REBUILD;

-- Rebuild all indexes on table
ALTER TABLE users REBUILD INDEXES;
```

#### Update Statistics
```sql
-- Update index statistics
UPDATE STATISTICS FOR INDEX idx_users_email ON users;
```

## Monitoring and Maintenance

### Database Statistics

#### View Database Stats
```sql
-- Get database statistics
SELECT * FROM information_schema.database_stats 
WHERE database_name = 'myapp';
```

#### Table Statistics
```sql
-- Get table statistics
SELECT * FROM information_schema.table_stats 
WHERE table_name = 'users';
```

### Maintenance Tasks

#### Vacuum Database
```sql
-- Vacuum database to reclaim space
VACUUM DATABASE myapp;
```

#### Check Database Integrity
```sql
-- Check database integrity
CHECK DATABASE myapp;
```

## Best Practices

### Database Design

1. **Use Meaningful Names**: Choose clear, descriptive names for databases and tables
2. **Normalize Data**: Follow normalization rules to avoid redundancy
3. **Use Appropriate Data Types**: Choose the most efficient data type for each column
4. **Create Indexes Wisely**: Index frequently queried columns
5. **Plan for Growth**: Design schemas that can scale

### Performance Tips

1. **Use Indexes**: Create indexes on frequently queried columns
2. **Optimize Queries**: Write efficient SQL queries
3. **Monitor Performance**: Regularly check query performance
4. **Maintain Statistics**: Keep table and index statistics up to date
5. **Plan Backups**: Implement regular backup strategies

### Security Considerations

1. **Use Strong Passwords**: Implement strong password policies
2. **Limit Access**: Grant minimum necessary permissions
3. **Encrypt Sensitive Data**: Use encryption for sensitive information
4. **Audit Logging**: Enable audit logging for compliance
5. **Regular Updates**: Keep the system updated with security patches

## Next Steps

Now that you can manage databases effectively:

- [SQL Reference](06-sql-reference.md) - Master the SQL language
- [CLI Reference](07-cli-reference.md) - Use the command-line interface
- [Performance Tuning](09-performance-tuning.md) - Optimize your database

---

*For advanced database management techniques, see the [API Reference](11-api-reference.md).*

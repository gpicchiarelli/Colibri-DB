# SQL Reference

## SQL Language Support

ColibrìDB supports a comprehensive subset of SQL with extensions for modern database operations. This reference covers all supported SQL statements, functions, and operators.

## Data Definition Language (DDL)

### Database Operations

#### CREATE DATABASE
Creates a new database.

```sql
-- Basic syntax
CREATE DATABASE database_name;

-- With options
CREATE DATABASE database_name
    WITH (
        encoding = 'UTF8',
        collation = 'en_US.UTF8'
    );

-- Examples
CREATE DATABASE myapp;
CREATE DATABASE analytics WITH (encoding = 'UTF8');
```

#### DROP DATABASE
Removes a database and all its contents.

```sql
-- Basic syntax
DROP DATABASE database_name;

-- With confirmation
DROP DATABASE database_name CASCADE;

-- Examples
DROP DATABASE myapp;
DROP DATABASE old_analytics CASCADE;
```

#### USE DATABASE
Switches to a specific database.

```sql
-- Switch to database
USE database_name;

-- Examples
USE myapp;
USE analytics;
```

### Table Operations

#### CREATE TABLE
Creates a new table with specified columns and constraints.

```sql
-- Basic syntax
CREATE TABLE table_name (
    column_name data_type [constraints],
    ...
);

-- Examples
CREATE TABLE users (
    id INT PRIMARY KEY,
    name STRING NOT NULL,
    email STRING UNIQUE
);

CREATE TABLE products (
    id INT PRIMARY KEY,
    name STRING(255) NOT NULL,
    price DECIMAL(10,2) NOT NULL,
    category_id INT,
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW(),
    
    CONSTRAINT chk_price CHECK (price >= 0),
    CONSTRAINT fk_category FOREIGN KEY (category_id) REFERENCES categories(id)
);
```

#### ALTER TABLE
Modifies an existing table structure.

```sql
-- Add column
ALTER TABLE table_name ADD COLUMN column_name data_type;

-- Add multiple columns
ALTER TABLE table_name 
    ADD COLUMN column1 data_type,
    ADD COLUMN column2 data_type;

-- Modify column
ALTER TABLE table_name MODIFY COLUMN column_name new_data_type;

-- Drop column
ALTER TABLE table_name DROP COLUMN column_name;

-- Add constraint
ALTER TABLE table_name ADD CONSTRAINT constraint_name constraint_definition;

-- Drop constraint
ALTER TABLE table_name DROP CONSTRAINT constraint_name;

-- Rename table
ALTER TABLE table_name RENAME TO new_table_name;

-- Examples
ALTER TABLE users ADD COLUMN phone STRING;
ALTER TABLE users MODIFY COLUMN email STRING(255);
ALTER TABLE users DROP COLUMN phone;
ALTER TABLE users ADD CONSTRAINT chk_age CHECK (age >= 18);
```

#### DROP TABLE
Removes a table and all its data.

```sql
-- Basic syntax
DROP TABLE table_name;

-- With confirmation
DROP TABLE table_name CASCADE;

-- If exists
DROP TABLE IF EXISTS table_name;

-- Examples
DROP TABLE users;
DROP TABLE old_products CASCADE;
DROP TABLE IF EXISTS temp_table;
```

### Index Operations

#### CREATE INDEX
Creates an index on one or more columns.

```sql
-- Basic syntax
CREATE [UNIQUE] INDEX index_name ON table_name (column_name);

-- Multiple columns
CREATE INDEX index_name ON table_name (column1, column2);

-- With index type
CREATE INDEX index_name ON table_name (column_name) USING index_type;

-- Partial index
CREATE INDEX index_name ON table_name (column_name) WHERE condition;

-- Examples
CREATE INDEX idx_users_email ON users(email);
CREATE UNIQUE INDEX idx_users_username ON users(username);
CREATE INDEX idx_orders_user_date ON orders(user_id, order_date);
CREATE INDEX idx_users_email ON users(email) USING HASH;
CREATE INDEX idx_active_users ON users(email) WHERE is_active = true;
```

#### DROP INDEX
Removes an index.

```sql
-- Basic syntax
DROP INDEX index_name;

-- On specific table
DROP INDEX index_name ON table_name;

-- Examples
DROP INDEX idx_users_email;
DROP INDEX idx_users_email ON users;
```

### View Operations

#### CREATE VIEW
Creates a virtual table based on a query.

```sql
-- Basic syntax
CREATE VIEW view_name AS select_statement;

-- Examples
CREATE VIEW active_users AS
SELECT id, name, email
FROM users
WHERE is_active = true;

CREATE VIEW user_orders AS
SELECT 
    u.id as user_id,
    u.name as user_name,
    o.id as order_id,
    o.total_amount,
    o.order_date
FROM users u
JOIN orders o ON u.id = o.user_id;
```

#### DROP VIEW
Removes a view.

```sql
-- Basic syntax
DROP VIEW view_name;

-- Examples
DROP VIEW active_users;
```

### Sequence Operations

#### CREATE SEQUENCE
Creates a sequence for generating unique numbers.

```sql
-- Basic syntax
CREATE SEQUENCE sequence_name;

-- With options
CREATE SEQUENCE sequence_name
    START WITH start_value
    INCREMENT BY increment_value
    MINVALUE min_value
    MAXVALUE max_value
    CYCLE;

-- Examples
CREATE SEQUENCE user_id_seq;
CREATE SEQUENCE order_id_seq START WITH 1000 INCREMENT BY 1;
```

#### DROP SEQUENCE
Removes a sequence.

```sql
-- Basic syntax
DROP SEQUENCE sequence_name;

-- Examples
DROP SEQUENCE user_id_seq;
```

## Data Manipulation Language (DML)

### INSERT Statement
Adds new rows to a table.

```sql
-- Basic syntax
INSERT INTO table_name (column1, column2, ...) 
VALUES (value1, value2, ...);

-- Multiple rows
INSERT INTO table_name (column1, column2, ...) 
VALUES 
    (value1, value2, ...),
    (value3, value4, ...);

-- Using SELECT
INSERT INTO table_name (column1, column2, ...)
SELECT column1, column2, ...
FROM source_table
WHERE condition;

-- Examples
INSERT INTO users (id, name, email) 
VALUES (1, 'John Doe', 'john@example.com');

INSERT INTO users (id, name, email) VALUES 
    (1, 'John Doe', 'john@example.com'),
    (2, 'Jane Smith', 'jane@example.com');

INSERT INTO users (name, email)
SELECT name, email FROM temp_users WHERE is_valid = true;
```

### UPDATE Statement
Modifies existing rows in a table.

```sql
-- Basic syntax
UPDATE table_name 
SET column1 = value1, column2 = value2, ...
WHERE condition;

-- Using subquery
UPDATE table_name 
SET column1 = (SELECT value FROM other_table WHERE condition)
WHERE condition;

-- Examples
UPDATE users 
SET email = 'newemail@example.com' 
WHERE id = 1;

UPDATE users 
SET name = 'John Smith', 
    email = 'johnsmith@example.com',
    updated_at = NOW()
WHERE id = 1;

UPDATE products 
SET price = price * 1.1 
WHERE category_id = 1;
```

### DELETE Statement
Removes rows from a table.

```sql
-- Basic syntax
DELETE FROM table_name WHERE condition;

-- Delete all rows
DELETE FROM table_name;

-- Using subquery
DELETE FROM table_name 
WHERE column IN (SELECT column FROM other_table WHERE condition);

-- Examples
DELETE FROM users WHERE id = 1;
DELETE FROM users WHERE last_login < '2023-01-01';
DELETE FROM products WHERE category_id NOT IN (SELECT id FROM categories);
```

### TRUNCATE Statement
Removes all rows from a table.

```sql
-- Basic syntax
TRUNCATE TABLE table_name;

-- With reset sequence
TRUNCATE TABLE table_name RESTART IDENTITY;

-- Examples
TRUNCATE TABLE users;
TRUNCATE TABLE temp_data RESTART IDENTITY;
```

## Data Query Language (DQL)

### SELECT Statement
Retrieves data from tables.

```sql
-- Basic syntax
SELECT column1, column2, ... FROM table_name WHERE condition;

-- All columns
SELECT * FROM table_name;

-- With ordering
SELECT * FROM table_name ORDER BY column1 ASC, column2 DESC;

-- With grouping
SELECT column1, COUNT(*) FROM table_name GROUP BY column1;

-- With joins
SELECT t1.column1, t2.column2 
FROM table1 t1 
JOIN table2 t2 ON t1.id = t2.table1_id;

-- Examples
SELECT id, name, email FROM users WHERE is_active = true;
SELECT * FROM users ORDER BY created_at DESC;
SELECT category_id, COUNT(*) FROM products GROUP BY category_id;
```

### JOIN Operations

#### INNER JOIN
Returns rows that have matching values in both tables.

```sql
-- Basic syntax
SELECT columns
FROM table1
INNER JOIN table2 ON table1.column = table2.column;

-- Examples
SELECT u.name, o.order_date, o.total_amount
FROM users u
INNER JOIN orders o ON u.id = o.user_id;
```

#### LEFT JOIN
Returns all rows from the left table and matching rows from the right table.

```sql
-- Basic syntax
SELECT columns
FROM table1
LEFT JOIN table2 ON table1.column = table2.column;

-- Examples
SELECT u.name, o.order_date
FROM users u
LEFT JOIN orders o ON u.id = o.user_id;
```

#### RIGHT JOIN
Returns all rows from the right table and matching rows from the left table.

```sql
-- Basic syntax
SELECT columns
FROM table1
RIGHT JOIN table2 ON table1.column = table2.column;

-- Examples
SELECT u.name, o.order_date
FROM users u
RIGHT JOIN orders o ON u.id = o.user_id;
```

#### FULL OUTER JOIN
Returns all rows when there is a match in either table.

```sql
-- Basic syntax
SELECT columns
FROM table1
FULL OUTER JOIN table2 ON table1.column = table2.column;

-- Examples
SELECT u.name, o.order_date
FROM users u
FULL OUTER JOIN orders o ON u.id = o.user_id;
```

### WHERE Clause
Filters rows based on conditions.

```sql
-- Comparison operators
WHERE column = value
WHERE column != value
WHERE column <> value
WHERE column > value
WHERE column >= value
WHERE column < value
WHERE column <= value

-- Logical operators
WHERE condition1 AND condition2
WHERE condition1 OR condition2
WHERE NOT condition

-- Pattern matching
WHERE column LIKE 'pattern'
WHERE column NOT LIKE 'pattern'

-- Range conditions
WHERE column BETWEEN value1 AND value2
WHERE column NOT BETWEEN value1 AND value2

-- List conditions
WHERE column IN (value1, value2, value3)
WHERE column NOT IN (value1, value2, value3)

-- NULL conditions
WHERE column IS NULL
WHERE column IS NOT NULL

-- Examples
SELECT * FROM users WHERE age > 18 AND is_active = true;
SELECT * FROM users WHERE name LIKE 'J%';
SELECT * FROM users WHERE age BETWEEN 18 AND 65;
SELECT * FROM users WHERE id IN (1, 2, 3);
SELECT * FROM users WHERE email IS NOT NULL;
```

### ORDER BY Clause
Sorts the result set.

```sql
-- Basic syntax
ORDER BY column1 [ASC|DESC], column2 [ASC|DESC], ...

-- Examples
SELECT * FROM users ORDER BY name ASC;
SELECT * FROM users ORDER BY created_at DESC, name ASC;
```

### GROUP BY Clause
Groups rows that have the same values.

```sql
-- Basic syntax
GROUP BY column1, column2, ...

-- With aggregate functions
SELECT column1, COUNT(*), SUM(column2)
FROM table_name
GROUP BY column1;

-- Examples
SELECT category_id, COUNT(*) as product_count
FROM products
GROUP BY category_id;

SELECT user_id, COUNT(*) as order_count, SUM(total_amount) as total_spent
FROM orders
GROUP BY user_id;
```

### HAVING Clause
Filters groups after GROUP BY.

```sql
-- Basic syntax
GROUP BY column1
HAVING condition

-- Examples
SELECT category_id, COUNT(*) as product_count
FROM products
GROUP BY category_id
HAVING COUNT(*) > 10;
```

### LIMIT Clause
Limits the number of rows returned.

```sql
-- Basic syntax
LIMIT count

-- With offset
LIMIT count OFFSET offset

-- Examples
SELECT * FROM users LIMIT 10;
SELECT * FROM users LIMIT 10 OFFSET 20;
```

## Data Types

### Numeric Types

#### INT
64-bit signed integer.

```sql
-- Examples
id INT
age INT
count INT
```

#### DOUBLE
64-bit floating-point number.

```sql
-- Examples
price DOUBLE
rate DOUBLE
percentage DOUBLE
```

#### DECIMAL
Exact decimal number with specified precision and scale.

```sql
-- Syntax
DECIMAL(precision, scale)

-- Examples
price DECIMAL(10,2)    -- 12345678.90
rate DECIMAL(5,4)      -- 12.3456
```

### String Types

#### STRING
Variable-length character string.

```sql
-- Examples
name STRING
description STRING
email STRING
```

#### TEXT
Large text data.

```sql
-- Examples
content TEXT
description TEXT
```

### Boolean Type

#### BOOL
True or false value.

```sql
-- Examples
is_active BOOL
is_verified BOOL
```

### Temporal Types

#### DATE
Date without time.

```sql
-- Examples
birth_date DATE
created_date DATE
```

#### TIMESTAMP
Date and time with precision.

```sql
-- Examples
created_at TIMESTAMP
updated_at TIMESTAMP
```

### Complex Types

#### JSON
JSON document.

```sql
-- Examples
metadata JSON
settings JSON
```

#### BLOB
Binary large object.

```sql
-- Examples
image_data BLOB
file_content BLOB
```

#### ENUM
User-defined enumeration.

```sql
-- Examples
status ENUM('active', 'inactive', 'pending')
priority ENUM('low', 'medium', 'high')
```

## Functions

### Aggregate Functions

#### COUNT
Counts the number of rows.

```sql
-- Count all rows
COUNT(*)

-- Count non-NULL values
COUNT(column)

-- Examples
SELECT COUNT(*) FROM users;
SELECT COUNT(email) FROM users;
```

#### SUM
Sums numeric values.

```sql
-- Basic syntax
SUM(column)

-- Examples
SELECT SUM(price) FROM products;
SELECT SUM(total_amount) FROM orders WHERE user_id = 1;
```

#### AVG
Calculates the average of numeric values.

```sql
-- Basic syntax
AVG(column)

-- Examples
SELECT AVG(price) FROM products;
SELECT AVG(age) FROM users;
```

#### MIN/MAX
Finds minimum/maximum values.

```sql
-- Basic syntax
MIN(column)
MAX(column)

-- Examples
SELECT MIN(price) FROM products;
SELECT MAX(created_at) FROM users;
```

### String Functions

#### CONCAT
Concatenates strings.

```sql
-- Basic syntax
CONCAT(string1, string2, ...)

-- Examples
SELECT CONCAT(first_name, ' ', last_name) FROM users;
```

#### SUBSTRING
Extracts a substring.

```sql
-- Basic syntax
SUBSTRING(string, start, length)

-- Examples
SELECT SUBSTRING(email, 1, 5) FROM users;
```

#### UPPER/LOWER
Converts to uppercase/lowercase.

```sql
-- Basic syntax
UPPER(string)
LOWER(string)

-- Examples
SELECT UPPER(name) FROM users;
SELECT LOWER(email) FROM users;
```

### Date Functions

#### NOW
Returns current timestamp.

```sql
-- Basic syntax
NOW()

-- Examples
SELECT NOW();
INSERT INTO users (name, created_at) VALUES ('John', NOW());
```

#### DATE_ADD/DATE_SUB
Adds/subtracts time intervals.

```sql
-- Basic syntax
DATE_ADD(date, INTERVAL value unit)
DATE_SUB(date, INTERVAL value unit)

-- Examples
SELECT DATE_ADD(NOW(), INTERVAL 1 DAY);
SELECT DATE_SUB(NOW(), INTERVAL 1 MONTH);
```

## Operators

### Arithmetic Operators

```sql
-- Addition
column1 + column2

-- Subtraction
column1 - column2

-- Multiplication
column1 * column2

-- Division
column1 / column2

-- Modulo
column1 % column2

-- Examples
SELECT price * 1.1 FROM products;
SELECT age + 1 FROM users;
```

### Comparison Operators

```sql
-- Equality
column = value

-- Inequality
column != value
column <> value

-- Greater than
column > value

-- Greater than or equal
column >= value

-- Less than
column < value

-- Less than or equal
column <= value

-- Examples
SELECT * FROM users WHERE age >= 18;
SELECT * FROM products WHERE price != 0;
```

### Logical Operators

```sql
-- AND
condition1 AND condition2

-- OR
condition1 OR condition2

-- NOT
NOT condition

-- Examples
SELECT * FROM users WHERE age >= 18 AND is_active = true;
SELECT * FROM products WHERE price < 100 OR category_id = 1;
```

### Pattern Matching

#### LIKE Operator
Matches patterns in strings.

```sql
-- Basic syntax
column LIKE pattern

-- Wildcards
% -- Matches any sequence of characters
_ -- Matches any single character

-- Examples
SELECT * FROM users WHERE name LIKE 'J%';
SELECT * FROM users WHERE email LIKE '%@gmail.com';
SELECT * FROM users WHERE name LIKE 'J_n';
```

## Constraints

### Primary Key
Uniquely identifies each row.

```sql
-- Single column
id INT PRIMARY KEY

-- Multiple columns
PRIMARY KEY (column1, column2)

-- Examples
CREATE TABLE users (id INT PRIMARY KEY, name STRING);
CREATE TABLE order_items (order_id INT, product_id INT, PRIMARY KEY (order_id, product_id));
```

### Foreign Key
References a column in another table.

```sql
-- Basic syntax
FOREIGN KEY (column) REFERENCES table(column)

-- Examples
CREATE TABLE orders (
    id INT PRIMARY KEY,
    user_id INT,
    FOREIGN KEY (user_id) REFERENCES users(id)
);
```

### Unique
Ensures column values are unique.

```sql
-- Single column
email STRING UNIQUE

-- Multiple columns
UNIQUE (column1, column2)

-- Examples
CREATE TABLE users (id INT PRIMARY KEY, email STRING UNIQUE);
CREATE TABLE users (id INT PRIMARY KEY, username STRING, email STRING, UNIQUE (username, email));
```

### Check
Validates column values against a condition.

```sql
-- Basic syntax
CHECK (condition)

-- Examples
CREATE TABLE users (
    id INT PRIMARY KEY,
    age INT CHECK (age >= 0),
    email STRING CHECK (email LIKE '%@%')
);
```

### Not Null
Ensures column cannot contain NULL values.

```sql
-- Basic syntax
column data_type NOT NULL

-- Examples
CREATE TABLE users (id INT PRIMARY KEY, name STRING NOT NULL);
```

## Next Steps

Now that you understand SQL in ColibrìDB:

- [CLI Reference](07-cli-reference.md) - Master the command-line interface
- [Database Management](05-database-management.md) - Apply SQL to manage databases
- [Performance Tuning](09-performance-tuning.md) - Optimize your SQL queries

---

*For advanced SQL features and extensions, see the [API Reference](11-api-reference.md).*

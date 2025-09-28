---
layout: page
title: Esempi Pratici
description: Esempi pratici e casi d'uso per ColibrDB
---

# 📚 Esempi Pratici

Collezione di esempi pratici per utilizzare ColibrDB in scenari reali.

## 🎯 Panoramica

Questa pagina contiene esempi pratici per:

- **Applicazioni Web**: Backend per applicazioni web
- **Analytics**: Elaborazione dati e reporting
- **IoT**: Gestione dati da sensori
- **E-commerce**: Catalogo prodotti e ordini
- **Logging**: Sistema di logging centralizzato
- **Testing**: Test automatizzati

## 🌐 Applicazioni Web

### 1. Blog System

Sistema di blog con utenti, post e commenti.

```sql
-- Crea tabelle
CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    username TEXT UNIQUE NOT NULL,
    email TEXT UNIQUE NOT NULL,
    password_hash TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE posts (
    id INTEGER PRIMARY KEY,
    user_id INTEGER NOT NULL,
    title TEXT NOT NULL,
    content TEXT NOT NULL,
    published BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (user_id) REFERENCES users(id)
);

CREATE TABLE comments (
    id INTEGER PRIMARY KEY,
    post_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    content TEXT NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (post_id) REFERENCES posts(id),
    FOREIGN KEY (user_id) REFERENCES users(id)
);
```

**Crea Indici per Performance**:
```sql
-- Indici per lookups veloci
CREATE INDEX idx_users_username ON users(username) USING Hash;
CREATE INDEX idx_users_email ON users(email) USING Hash;
CREATE INDEX idx_posts_user_id ON posts(user_id) USING BTree;
CREATE INDEX idx_posts_published ON posts(published) USING BTree;
CREATE INDEX idx_comments_post_id ON comments(post_id) USING BTree;
```

**Query Tipiche**:
```sql
-- Trova post di un utente
SELECT p.*, u.username 
FROM posts p 
JOIN users u ON p.user_id = u.id 
WHERE u.username = 'alice' 
ORDER BY p.created_at DESC;

-- Conta commenti per post
SELECT p.title, COUNT(c.id) as comment_count
FROM posts p 
LEFT JOIN comments c ON p.id = c.post_id 
GROUP BY p.id, p.title
ORDER BY comment_count DESC;
```

### 2. E-commerce System

Sistema e-commerce con prodotti, ordini e inventario.

```sql
-- Crea schema e-commerce
CREATE TABLE categories (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    description TEXT,
    parent_id INTEGER,
    FOREIGN KEY (parent_id) REFERENCES categories(id)
);

CREATE TABLE products (
    id INTEGER PRIMARY KEY,
    category_id INTEGER NOT NULL,
    name TEXT NOT NULL,
    description TEXT,
    price DECIMAL(10,2) NOT NULL,
    sku TEXT UNIQUE NOT NULL,
    stock_quantity INTEGER DEFAULT 0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (category_id) REFERENCES categories(id)
);

CREATE TABLE customers (
    id INTEGER PRIMARY KEY,
    email TEXT UNIQUE NOT NULL,
    first_name TEXT NOT NULL,
    last_name TEXT NOT NULL,
    phone TEXT,
    address TEXT,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE orders (
    id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL,
    total_amount DECIMAL(10,2) NOT NULL,
    status TEXT DEFAULT 'pending',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (customer_id) REFERENCES customers(id)
);

CREATE TABLE order_items (
    id INTEGER PRIMARY KEY,
    order_id INTEGER NOT NULL,
    product_id INTEGER NOT NULL,
    quantity INTEGER NOT NULL,
    unit_price DECIMAL(10,2) NOT NULL,
    FOREIGN KEY (order_id) REFERENCES orders(id),
    FOREIGN KEY (product_id) REFERENCES products(id)
);
```

**Indici per Performance**:
```sql
-- Indici per ricerca prodotti
CREATE INDEX idx_products_category ON products(category_id) USING BTree;
CREATE INDEX idx_products_price ON products(price) USING BTree;
CREATE INDEX idx_products_sku ON products(sku) USING Hash;

-- Indici per ordini
CREATE INDEX idx_orders_customer ON orders(customer_id) USING BTree;
CREATE INDEX idx_orders_status ON orders(status) USING BTree;
CREATE INDEX idx_orders_created_at ON orders(created_at) USING BTree;

-- Indici per order items
CREATE INDEX idx_order_items_order ON order_items(order_id) USING BTree;
CREATE INDEX idx_order_items_product ON order_items(product_id) USING BTree;
```

**Query Analytics**:
```sql
-- Vendite per categoria
SELECT c.name, SUM(oi.quantity * oi.unit_price) as total_sales
FROM categories c
JOIN products p ON c.id = p.category_id
JOIN order_items oi ON p.id = oi.product_id
JOIN orders o ON oi.order_id = o.id
WHERE o.status = 'completed'
GROUP BY c.id, c.name
ORDER BY total_sales DESC;

-- Top clienti
SELECT c.email, c.first_name, c.last_name, 
       COUNT(o.id) as order_count,
       SUM(o.total_amount) as total_spent
FROM customers c
JOIN orders o ON c.id = o.customer_id
WHERE o.status = 'completed'
GROUP BY c.id, c.email, c.first_name, c.last_name
ORDER BY total_spent DESC
LIMIT 10;
```

## 📊 Analytics e Reporting

### 1. Sistema di Metriche

Sistema per raccogliere e analizzare metriche applicazione.

```sql
-- Schema per metriche
CREATE TABLE metrics (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    value DOUBLE NOT NULL,
    tags TEXT, -- JSON string
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE metric_aggregations (
    id INTEGER PRIMARY KEY,
    metric_name TEXT NOT NULL,
    aggregation_type TEXT NOT NULL, -- 'avg', 'sum', 'count', 'max', 'min'
    time_bucket TEXT NOT NULL, -- '1m', '5m', '1h', '1d'
    value DOUBLE NOT NULL,
    bucket_start TIMESTAMP NOT NULL,
    bucket_end TIMESTAMP NOT NULL
);
```

**Inserimento Metriche**:
```sql
-- Inserisci metriche di performance
INSERT INTO metrics (name, value, tags) VALUES 
('response_time', 150.5, '{"endpoint": "/api/users", "method": "GET"}'),
('response_time', 200.3, '{"endpoint": "/api/posts", "method": "POST"}'),
('cpu_usage', 75.2, '{"host": "web-01", "service": "api"}'),
('memory_usage', 85.1, '{"host": "web-01", "service": "api"}');
```

**Query Analytics**:
```sql
-- Media response time per endpoint
SELECT 
    JSON_EXTRACT(tags, '$.endpoint') as endpoint,
    AVG(value) as avg_response_time,
    COUNT(*) as request_count
FROM metrics 
WHERE name = 'response_time' 
    AND timestamp >= datetime('now', '-1 hour')
GROUP BY JSON_EXTRACT(tags, '$.endpoint')
ORDER BY avg_response_time DESC;

-- Trend CPU usage
SELECT 
    datetime(timestamp, 'start of hour') as hour,
    AVG(value) as avg_cpu_usage
FROM metrics 
WHERE name = 'cpu_usage' 
    AND timestamp >= datetime('now', '-24 hours')
GROUP BY datetime(timestamp, 'start of hour')
ORDER BY hour;
```

### 2. Data Warehouse

Sistema di data warehouse per analisi business.

```sql
-- Schema data warehouse
CREATE TABLE dim_customers (
    customer_id INTEGER PRIMARY KEY,
    email TEXT NOT NULL,
    first_name TEXT NOT NULL,
    last_name TEXT NOT NULL,
    city TEXT,
    country TEXT,
    customer_segment TEXT,
    created_at TIMESTAMP
);

CREATE TABLE dim_products (
    product_id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    category TEXT NOT NULL,
    brand TEXT,
    price DECIMAL(10,2),
    created_at TIMESTAMP
);

CREATE TABLE fact_sales (
    id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL,
    product_id INTEGER NOT NULL,
    order_date DATE NOT NULL,
    quantity INTEGER NOT NULL,
    unit_price DECIMAL(10,2) NOT NULL,
    total_amount DECIMAL(10,2) NOT NULL,
    FOREIGN KEY (customer_id) REFERENCES dim_customers(customer_id),
    FOREIGN KEY (product_id) REFERENCES dim_products(product_id)
);
```

**Indici per Analytics**:
```sql
-- Indici per aggregazioni
CREATE INDEX idx_sales_date ON fact_sales(order_date) USING BTree;
CREATE INDEX idx_sales_customer ON fact_sales(customer_id) USING BTree;
CREATE INDEX idx_sales_product ON fact_sales(product_id) USING BTree;
CREATE INDEX idx_sales_amount ON fact_sales(total_amount) USING BTree;
```

**Query Business Intelligence**:
```sql
-- Vendite mensili per categoria
SELECT 
    p.category,
    strftime('%Y-%m', s.order_date) as month,
    SUM(s.total_amount) as total_sales,
    COUNT(*) as order_count,
    AVG(s.total_amount) as avg_order_value
FROM fact_sales s
JOIN dim_products p ON s.product_id = p.product_id
WHERE s.order_date >= date('now', '-12 months')
GROUP BY p.category, strftime('%Y-%m', s.order_date)
ORDER BY month DESC, total_sales DESC;

-- Top clienti per segmento
SELECT 
    c.customer_segment,
    c.email,
    SUM(s.total_amount) as total_spent,
    COUNT(DISTINCT s.order_date) as order_days
FROM fact_sales s
JOIN dim_customers c ON s.customer_id = c.customer_id
WHERE s.order_date >= date('now', '-6 months')
GROUP BY c.customer_segment, c.customer_id, c.email
ORDER BY c.customer_segment, total_spent DESC;
```

## 🔌 IoT e Sensori

### 1. Sistema di Monitoraggio

Sistema per raccogliere dati da sensori IoT.

```sql
-- Schema per sensori IoT
CREATE TABLE sensors (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    type TEXT NOT NULL, -- 'temperature', 'humidity', 'pressure'
    location TEXT NOT NULL,
    unit TEXT NOT NULL, -- 'celsius', 'percent', 'hPa'
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE sensor_readings (
    id INTEGER PRIMARY KEY,
    sensor_id INTEGER NOT NULL,
    value DOUBLE NOT NULL,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    quality_score DOUBLE DEFAULT 1.0, -- 0-1, 1 = perfect quality
    FOREIGN KEY (sensor_id) REFERENCES sensors(id)
);

CREATE TABLE sensor_alerts (
    id INTEGER PRIMARY KEY,
    sensor_id INTEGER NOT NULL,
    alert_type TEXT NOT NULL, -- 'high', 'low', 'anomaly'
    threshold_value DOUBLE,
    actual_value DOUBLE,
    message TEXT,
    resolved BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (sensor_id) REFERENCES sensors(id)
);
```

**Inserimento Dati Sensori**:
```sql
-- Registra sensori
INSERT INTO sensors (name, type, location, unit) VALUES 
('temp_01', 'temperature', 'server_room', 'celsius'),
('hum_01', 'humidity', 'server_room', 'percent'),
('press_01', 'pressure', 'outdoor', 'hPa');

-- Inserisci letture sensori
INSERT INTO sensor_readings (sensor_id, value, quality_score) VALUES 
(1, 22.5, 0.95),
(1, 23.1, 0.98),
(2, 45.2, 0.92),
(2, 44.8, 0.94),
(3, 1013.25, 0.99);
```

**Query per Monitoraggio**:
```sql
-- Letture recenti per sensore
SELECT s.name, s.type, sr.value, sr.timestamp, sr.quality_score
FROM sensor_readings sr
JOIN sensors s ON sr.sensor_id = s.id
WHERE s.name = 'temp_01'
    AND sr.timestamp >= datetime('now', '-1 hour')
ORDER BY sr.timestamp DESC;

-- Rilevamento anomalie
SELECT s.name, s.type, sr.value, sr.timestamp
FROM sensor_readings sr
JOIN sensors s ON sr.sensor_id = s.id
WHERE s.type = 'temperature'
    AND sr.value > 30  -- Soglia temperatura alta
    AND sr.timestamp >= datetime('now', '-24 hours')
ORDER BY sr.timestamp DESC;

-- Statistiche per sensore
SELECT 
    s.name,
    s.type,
    COUNT(*) as reading_count,
    AVG(sr.value) as avg_value,
    MIN(sr.value) as min_value,
    MAX(sr.value) as max_value,
    AVG(sr.quality_score) as avg_quality
FROM sensor_readings sr
JOIN sensors s ON sr.sensor_id = s.id
WHERE sr.timestamp >= datetime('now', '-24 hours')
GROUP BY s.id, s.name, s.type
ORDER BY s.name;
```

## 📝 Sistema di Logging

### 1. Centralized Logging

Sistema di logging centralizzato per applicazioni.

```sql
-- Schema per logging
CREATE TABLE log_entries (
    id INTEGER PRIMARY KEY,
    level TEXT NOT NULL, -- 'DEBUG', 'INFO', 'WARN', 'ERROR', 'FATAL'
    logger TEXT NOT NULL, -- 'com.example.api', 'com.example.service'
    message TEXT NOT NULL,
    exception TEXT, -- Stack trace se presente
    thread_name TEXT,
    user_id INTEGER,
    request_id TEXT,
    tags TEXT, -- JSON string
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE log_metrics (
    id INTEGER PRIMARY KEY,
    level TEXT NOT NULL,
    logger TEXT NOT NULL,
    count INTEGER NOT NULL,
    time_bucket TEXT NOT NULL, -- '1m', '5m', '1h'
    bucket_start TIMESTAMP NOT NULL,
    bucket_end TIMESTAMP NOT NULL
);
```

**Inserimento Log**:
```sql
-- Inserisci log entries
INSERT INTO log_entries (level, logger, message, user_id, request_id, tags) VALUES 
('INFO', 'com.example.api', 'User login successful', 123, 'req_001', '{"endpoint": "/login"}'),
('ERROR', 'com.example.service', 'Database connection failed', NULL, 'req_002', '{"error_code": "DB_CONN_001"}'),
('WARN', 'com.example.api', 'Rate limit exceeded', 456, 'req_003', '{"endpoint": "/api/data", "limit": 100}'),
('DEBUG', 'com.example.service', 'Cache miss for key: user_123', 123, 'req_001', '{"cache_key": "user_123"}');
```

**Query per Analisi Log**:
```sql
-- Errori per logger
SELECT 
    logger,
    COUNT(*) as error_count,
    COUNT(DISTINCT user_id) as affected_users
FROM log_entries 
WHERE level = 'ERROR' 
    AND timestamp >= datetime('now', '-24 hours')
GROUP BY logger
ORDER BY error_count DESC;

-- Trend errori nel tempo
SELECT 
    datetime(timestamp, 'start of hour') as hour,
    level,
    COUNT(*) as count
FROM log_entries 
WHERE timestamp >= datetime('now', '-7 days')
GROUP BY datetime(timestamp, 'start of hour'), level
ORDER BY hour DESC, level;

-- Top errori per utente
SELECT 
    user_id,
    COUNT(*) as error_count,
    COUNT(DISTINCT logger) as affected_services
FROM log_entries 
WHERE level = 'ERROR' 
    AND user_id IS NOT NULL
    AND timestamp >= datetime('now', '-7 days')
GROUP BY user_id
ORDER BY error_count DESC
LIMIT 10;
```

## 🧪 Testing

### 1. Test Database Setup

Setup per test automatizzati.

```swift
import Testing
import ColibriCore

@Test func testUserCRUD() async throws {
    // Setup test database
    let config = DBConfig(
        dataDir: "./test_data",
        walEnabled: false, // Disabilita WAL per test
        cliEnabled: false
    )
    
    let database = Database(config: config)
    
    // Crea tabella test
    try database.createTable("test_users")
    
    // Test inserimento
    let user = Row([
        "id": .int(1),
        "name": .string("Alice"),
        "email": .string("alice@example.com")
    ])
    
    let rid = try database.insert("test_users", row: user)
    #expect(rid.pageId > 0)
    
    // Test lettura
    let users = try database.select("test_users", predicate: nil)
    #expect(users.count == 1)
    #expect(users[0]["name"] == .string("Alice"))
    
    // Test aggiornamento
    let updatedUser = Row([
        "id": .int(1),
        "name": .string("Alice Updated"),
        "email": .string("alice@example.com")
    ])
    
    try database.update("test_users", rid: rid, row: updatedUser)
    
    // Test eliminazione
    try database.delete("test_users", rid: rid)
    
    let finalUsers = try database.select("test_users", predicate: nil)
    #expect(finalUsers.count == 0)
}

@Test func testTransactionRollback() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("test_transactions")
    
    // Inizia transazione
    let tid = try database.begin()
    
    do {
        // Inserisci dati
        let row1 = Row(["id": .int(1), "name": .string("Alice")])
        let row2 = Row(["id": .int(2), "name": .string("Bob")])
        
        try database.insert("test_transactions", row: row1)
        try database.insert("test_transactions", row: row2)
        
        // Simula errore
        throw DBError.invalidOperation("Test error")
        
    } catch {
        // Rollback transazione
        try database.rollback(toSavepoint: "", tid: tid)
    }
    
    // Verifica che i dati non siano stati committati
    let users = try database.select("test_transactions", predicate: nil)
    #expect(users.count == 0)
}
```

### 2. Performance Testing

Test di performance per identificare regressioni.

```swift
@Test func testInsertPerformance() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("perf_test")
    
    let startTime = Date()
    
    // Inserisci 10,000 record
    for i in 0..<10000 {
        let row = Row([
            "id": .int(Int64(i)),
            "data": .string("Test data \(i)"),
            "timestamp": .date(Date())
        ])
        try database.insert("perf_test", row: row)
    }
    
    let endTime = Date()
    let duration = endTime.timeIntervalSince(startTime)
    
    // Verifica che l'inserimento sia completato in meno di 5 secondi
    #expect(duration < 5.0)
    
    // Verifica che tutti i record siano stati inseriti
    let count = try database.select("perf_test", predicate: nil).count
    #expect(count == 10000)
}

@Test func testQueryPerformance() async throws {
    let config = DBConfig(dataDir: "./test_data")
    let database = Database(config: config)
    
    try database.createTable("query_test")
    
    // Inserisci dati di test
    for i in 0..<1000 {
        let row = Row([
            "id": .int(Int64(i)),
            "category": .string(i % 10 == 0 ? "premium" : "standard"),
            "value": .double(Double(i) * 1.5)
        ])
        try database.insert("query_test", row: row)
    }
    
    // Crea indice per performance
    try database.createIndex("idx_category", on: "query_test", columns: ["category"], type: .hash)
    
    let startTime = Date()
    
    // Esegui query con indice
    let results = try database.select("query_test", predicate: .equals("category", .string("premium")))
    
    let endTime = Date()
    let duration = endTime.timeIntervalSince(startTime)
    
    // Verifica che la query sia completata in meno di 100ms
    #expect(duration < 0.1)
    #expect(results.count == 100) // 10% dei record sono premium
}
```

## 🚀 Deployment Examples

### 1. Docker Deployment

```dockerfile
# Dockerfile per ColibrDB
FROM swift:6.2-focal

WORKDIR /app

# Copia sorgenti
COPY . .

# Compila in modalità release
RUN swift build -c release

# Crea utente non-root
RUN useradd -m -u 1000 colibridb

# Crea directory dati
RUN mkdir -p /data && chown colibridb:colibridb /data

# Switch a utente non-root
USER colibridb

# Esponi porta
EXPOSE 5432

# Avvia server
CMD [".build/release/coldb-server", "--config", "colibridb.conf.json"]
```

**Docker Compose**:
```yaml
version: '3.8'

services:
  colibridb:
    build: .
    ports:
      - "5432:5432"
    volumes:
      - colibridb_data:/data
      - ./colibridb.conf.json:/app/colibridb.conf.json
    environment:
      - COLIBRIDB_DATA_DIR=/data
    restart: unless-stopped

volumes:
  colibridb_data:
```

### 2. Kubernetes Deployment

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: colibridb
spec:
  replicas: 1
  selector:
    matchLabels:
      app: colibridb
  template:
    metadata:
      labels:
        app: colibridb
    spec:
      containers:
      - name: colibridb
        image: colibridb:latest
        ports:
        - containerPort: 5432
        env:
        - name: COLIBRIDB_DATA_DIR
          value: "/data"
        volumeMounts:
        - name: data
          mountPath: /data
        resources:
          requests:
            memory: "1Gi"
            cpu: "500m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
      volumes:
      - name: data
        persistentVolumeClaim:
          claimName: colibridb-pvc
---
apiVersion: v1
kind: Service
metadata:
  name: colibridb-service
spec:
  selector:
    app: colibridb
  ports:
  - port: 5432
    targetPort: 5432
  type: ClusterIP
```

---

<div align="center">

**📚 Examples ColibrDB** - *Esempi pratici per ogni scenario d'uso*

[← Performance Guide]({{ site.baseurl }}/wiki/Performance) • [Home →]({{ site.baseurl }}/wiki/Home)

</div>

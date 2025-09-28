# 🔧 CLI Reference

Guida completa ai comandi della CLI `coldb` di ColibrìDB.

## 🚀 Avvio della CLI

### Sintassi Base

```bash
# Avvio con configurazione predefinita
.build/debug/coldb

# Avvio con file di configurazione specifico
.build/debug/coldb --config /path/to/config.json

# Avvio con opzioni
.build/debug/coldb -c colibridb.conf.json
```

### Opzioni di Avvio

| Opzione | Descrizione | Esempio |
|---------|-------------|---------|
| `--config`, `-c` | File di configurazione | `-c myconfig.json` |
| `--help`, `-h` | Mostra aiuto | `-h` |
| `--version`, `-v` | Mostra versione | `-v` |

## 📋 Comandi Meta

### `\help`, `\h`, `\?`
Mostra l'aiuto con tutti i comandi disponibili.

```bash
colibridb> \help
```

**Output**:
```
📚 ColibrìDB Commands:

Meta Commands:
  \help, \h, \?         Show this help
  \quit, \q, \exit      Exit ColibrìDB
  \version, \v          Show version information
  \status, \s           Show database status
  \timing               Toggle timing display

Database Exploration:
  \dt                   List all tables
  \di                   List all indexes
  \d <table>            Describe table structure

SQL Commands:
  CREATE TABLE ...      Create a new table
  DROP TABLE ...        Drop an existing table
  INSERT INTO ...       Insert data into table
  SELECT ...            Query data from tables
  UPDATE ...            Update existing data
  DELETE FROM ...       Delete data from tables

Transaction Commands:
  BEGIN                 Start a transaction
  COMMIT                Commit current transaction
  ROLLBACK              Rollback current transaction
```

### `\quit`, `\q`, `\exit`
Esce dalla CLI.

```bash
colibridb> \exit
```

### `\version`, `\v`
Mostra informazioni sulla versione.

```bash
colibridb> \version
```

**Output**:
```
ColibrìDB Version Information:
  Version: 1.0.0
  Platform: macOS 13.0
  Swift: 6.2.0
  Build: Production
```

### `\status`, `\s`
Mostra lo stato del database.

```bash
colibridb> \status
```

**Output**:
```
Database Status:
  Tables: 3
  Indexes: 5
  Active Transactions: 0
  Buffer Pool Hit Rate: 95.2%
  WAL Size: 1.2MB
  Uptime: 2h 15m
```

### `\timing`
Attiva/disattiva la visualizzazione dei tempi di esecuzione.

```bash
colibridb> \timing
Timing is now ON
```

## 🗄️ Comandi Database

### `\dt`
Lista tutte le tabelle nel database.

```bash
colibridb> \dt
```

**Output**:
```
📋 Tables:
┌─────────────────────────────────────┐
│ Table Name                          │
├─────────────────────────────────────┤
│ users                               │
│ products                            │
│ orders                              │
└─────────────────────────────────────┘
(3 tables)
```

### `\di`
Lista tutti gli indici nel database.

```bash
colibridb> \di
```

**Output**:
```
🔍 Indexes:
┌─────────────────────────────────────┐
│ Index Name        │ Table  │ Type   │
├─────────────────────────────────────┤
│ idx_users_name    │ users  │ BTree  │
│ idx_users_email   │ users  │ Hash   │
│ idx_products_id   │ products│ BTree │
└─────────────────────────────────────┘
(3 indexes)
```

### `\d <table>`
Descrive la struttura di una tabella.

```bash
colibridb> \d users
```

**Output**:
```
Table: users
┌─────────────┬──────────┬─────────┬─────────┐
│ Column      │ Type     │ Null    │ Default │
├─────────────┼──────────┼─────────┼─────────┤
│ id          │ INTEGER  │ NO      │         │
│ name        │ TEXT     │ YES     │         │
│ email       │ TEXT     │ YES     │         │
│ age         │ INTEGER  │ YES     │         │
└─────────────┴──────────┴─────────┴─────────┘

Indexes:
  • idx_users_name (BTree) ON name
  • idx_users_email (Hash) ON email
```

## 🏗️ Comandi DDL (Data Definition Language)

### `\create table <name>`
Crea una nuova tabella.

```bash
# Crea una tabella semplice
colibridb> \create table users

# Crea una tabella con schema specifico
colibridb> \create table products (id INTEGER, name TEXT, price DECIMAL)
```

**Output**:
```
Table 'users' created successfully
```

### `CREATE TABLE` (SQL)
Crea una tabella usando sintassi SQL standard.

```bash
colibridb> \sql CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    email TEXT UNIQUE,
    age INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
)
```

### `DROP TABLE` (SQL)
Elimina una tabella esistente.

```bash
colibridb> \sql DROP TABLE users
```

**Output**:
```
Table 'users' dropped successfully
```

## 📊 Comandi DML (Data Manipulation Language)

### `\insert <table> col=val,...`
Inserisce dati in una tabella.

```bash
# Inserisci un singolo record
colibridb> \insert users id=1,name=Alice,email=alice@example.com,age=25

# Inserisci più record
colibridb> \insert users id=2,name=Bob,email=bob@example.com,age=30
colibridb> \insert users id=3,name=Charlie,email=charlie@example.com,age=35
```

**Output**:
```
1 row inserted
```

### `INSERT INTO` (SQL)
Inserisce dati usando sintassi SQL standard.

```bash
colibridb> \sql INSERT INTO users (id, name, email, age) VALUES (4, 'David', 'david@example.com', 28)
```

### `\scan <table>`
Scansiona tutti i record di una tabella.

```bash
colibridb> \scan users
```

**Output**:
```
Scanning table 'users':
┌────┬─────────┬─────────────────────┬─────┐
│ id │ name    │ email               │ age │
├────┼─────────┼─────────────────────┼─────┤
│ 1  │ Alice   │ alice@example.com   │ 25  │
│ 2  │ Bob     │ bob@example.com     │ 30  │
│ 3  │ Charlie │ charlie@example.com │ 35  │
└────┴─────────┴─────────────────────┴─────┘
(3 rows)
```

### `SELECT` (SQL)
Esegue query di selezione.

```bash
# Seleziona tutti i record
colibridb> \sql SELECT * FROM users

# Seleziona con condizioni
colibridb> \sql SELECT name, email FROM users WHERE age > 25

# Seleziona con ordinamento
colibridb> \sql SELECT * FROM users ORDER BY name ASC

# Seleziona con limitazione
colibridb> \sql SELECT * FROM users LIMIT 10
```

**Output**:
```
Columns: id, name, email, age
Rows (3):
  1: 1, Alice, alice@example.com, 25
  2: 2, Bob, bob@example.com, 30
  3: 3, Charlie, charlie@example.com, 35
```

### `UPDATE` (SQL)
Aggiorna record esistenti.

```bash
colibridb> \sql UPDATE users SET age = 26 WHERE name = 'Alice'
```

**Output**:
```
1 row updated
```

### `DELETE FROM` (SQL)
Elimina record da una tabella.

```bash
colibridb> \sql DELETE FROM users WHERE age > 30
```

**Output**:
```
1 row deleted
```

### `\delete <table> col=val`
Elimina record usando sintassi semplificata.

```bash
colibridb> \delete users age=35
```

**Output**:
```
1 row deleted
```

## 🔄 Comandi Transazioni

### `\begin`
Inizia una nuova transazione.

```bash
colibridb> \begin
```

**Output**:
```
Transaction started: 12345
```

### `\commit`
Conferma la transazione corrente.

```bash
colibridb> \commit
```

**Output**:
```
Transaction committed: 12345
```

### `\rollback`
Annulla la transazione corrente.

```bash
colibridb> \rollback
```

**Output**:
```
Transaction rolled back: 12345
```

### `BEGIN` (SQL)
Inizia una transazione usando sintassi SQL.

```bash
colibridb> \sql BEGIN
```

### `COMMIT` (SQL)
Conferma la transazione usando sintassi SQL.

```bash
colibridb> \sql COMMIT
```

### `ROLLBACK` (SQL)
Annulla la transazione usando sintassi SQL.

```bash
colibridb> \sql ROLLBACK
```

## 🔍 Comandi Indici

### `\create index <name> ON <table>(<column>) USING <type>`
Crea un nuovo indice.

```bash
# Crea un indice B+Tree
colibridb> \create index idx_users_name ON users(name) USING BTree

# Crea un indice Hash
colibridb> \create index idx_users_email ON users(email) USING Hash

# Crea un indice ART
colibridb> \create index idx_users_name ON users(name) USING ART
```

**Output**:
```
Index 'idx_users_name' created successfully
```

### `\drop index <name>`
Elimina un indice esistente.

```bash
colibridb> \drop index idx_users_name
```

**Output**:
```
Index 'idx_users_name' dropped successfully
```

### `\index search <table> <index> <value>`
Cerca usando un indice specifico.

```bash
colibridb> \index search users idx_users_name Alice
```

**Output**:
```
Search results using index 'idx_users_name':
┌────┬───────┬─────────────────────┬─────┐
│ id │ name  │ email               │ age │
├────┼───────┼─────────────────────┼─────┤
│ 1  │ Alice │ alice@example.com   │ 25  │
└────┴───────┴─────────────────────┴─────┘
(1 row)
```

## ⚙️ Comandi Configurazione

### `\config`
Mostra la configurazione corrente.

```bash
colibridb> \config
```

**Output**:
```
Configuration:
  Page size: 8192 bytes
  Buffer pool: 1073741824 bytes
  Lock timeout: 30 seconds
  WAL enabled: true
  Data directory: ./data
```

### `\config get <parameter>`
Mostra un parametro di configurazione specifico.

```bash
colibridb> \config get bufferPoolSizeBytes
```

**Output**:
```
bufferPoolSizeBytes: 1073741824
```

### `\config set <parameter> <value>`
Modifica un parametro di configurazione.

```bash
colibridb> \config set bufferPoolSizeBytes 2147483648
```

**Output**:
```
Configuration updated: bufferPoolSizeBytes = 2147483648
```

### `\config save`
Salva la configurazione corrente.

```bash
colibridb> \config save
```

**Output**:
```
Configuration saved to colibridb.conf.json
```

### `\config reload`
Ricarica la configurazione dal file.

```bash
colibridb> \config reload
```

**Output**:
```
Configuration reloaded from colibridb.conf.json
```

## 🧪 Comandi Test e Debug

### `\check database`
Verifica l'integrità del database.

```bash
colibridb> \check database
```

**Output**:
```
Database integrity check:
  ✓ Tables: 3/3 valid
  ✓ Indexes: 5/5 valid
  ✓ WAL: 1/1 valid
  ✓ Buffer pool: 95.2% hit rate
Database is healthy
```

### `\check indexes`
Verifica l'integrità degli indici.

```bash
colibridb> \check indexes
```

**Output**:
```
Index integrity check:
  ✓ idx_users_name: valid
  ✓ idx_users_email: valid
  ✓ idx_products_id: valid
All indexes are valid
```

### `\check wal`
Verifica l'integrità del WAL.

```bash
colibridb> \check wal
```

**Output**:
```
WAL integrity check:
  ✓ WAL file: valid
  ✓ Checksums: 100% valid
  ✓ Recovery: ready
WAL is healthy
```

### `\explain <query>`
Mostra il piano di esecuzione di una query.

```bash
colibridb> \explain SELECT * FROM users WHERE name = 'Alice'
```

**Output**:
```
Query Plan:
  ┌─────────────────────────────────────┐
  │ Index Scan (idx_users_name)         │
  │   Filter: name = 'Alice'            │
  │   Cost: 0.1                         │
  │   Rows: 1                           │
  └─────────────────────────────────────┘
```

## 📊 Comandi Performance

### `\stats`
Mostra statistiche di performance.

```bash
colibridb> \stats
```

**Output**:
```
Performance Statistics:
  Queries executed: 1,234
  Average query time: 2.5ms
  Buffer pool hit rate: 95.2%
  WAL throughput: 8,500 ops/sec
  Index usage: 78.5%
  Memory usage: 512MB / 1GB
```

### `\stats reset`
Azzera le statistiche di performance.

```bash
colibridb> \stats reset
```

**Output**:
```
Performance statistics reset
```

## 🔄 Comandi Import/Export

### `\export <table> TO <file>`
Esporta una tabella in CSV.

```bash
colibridb> \export users TO users.csv
```

**Output**:
```
Table 'users' exported to users.csv (3 rows)
```

### `\import <table> FROM <file>`
Importa dati da CSV.

```bash
colibridb> \import users FROM users_backup.csv
```

**Output**:
```
Table 'users' imported from users_backup.csv (3 rows)
```

### `\export <query> TO <file>`
Esporta il risultato di una query.

```bash
colibridb> \export "SELECT name, email FROM users WHERE age > 25" TO active_users.csv
```

**Output**:
```
Query result exported to active_users.csv (2 rows)
```

## 🚨 Comandi di Emergenza

### `\shutdown`
Spegne il database in modo sicuro.

```bash
colibridb> \shutdown
```

**Output**:
```
Database shutdown initiated...
  ✓ WAL flushed
  ✓ Buffer pool flushed
  ✓ Checkpoint completed
Database shutdown complete
```

### `\force checkpoint`
Forza un checkpoint immediato.

```bash
colibridb> \force checkpoint
```

**Output**:
```
Checkpoint forced:
  ✓ WAL flushed
  ✓ Dirty pages written
  ✓ Checkpoint completed
```

### `\recovery`
Avvia il recovery del database.

```bash
colibridb> \recovery
```

**Output**:
```
Recovery started:
  ✓ WAL analysis completed
  ✓ Redo phase completed
  ✓ Undo phase completed
  ✓ Database recovered successfully
```

## 📝 Esempi Pratici

### Esempio 1: Creazione di un Database Completo

```bash
# Avvia la CLI
colibridb> .build/debug/coldb

# Crea tabelle
colibridb> \create table users
colibridb> \create table products
colibridb> \create table orders

# Inserisci dati
colibridb> \insert users id=1,name=Alice,email=alice@example.com,age=25
colibridb> \insert users id=2,name=Bob,email=bob@example.com,age=30

# Crea indici
colibridb> \create index idx_users_name ON users(name) USING BTree
colibridb> \create index idx_users_email ON users(email) USING Hash

# Interroga i dati
colibridb> \sql SELECT * FROM users WHERE age > 25
```

### Esempio 2: Gestione Transazioni

```bash
# Inizia una transazione
colibridb> \begin

# Esegui operazioni
colibridb> \insert users id=3,name=Charlie,email=charlie@example.com,age=35
colibridb> \insert users id=4,name=David,email=david@example.com,age=28

# Verifica i dati
colibridb> \scan users

# Conferma la transazione
colibridb> \commit
```

### Esempio 3: Analisi Performance

```bash
# Mostra statistiche
colibridb> \stats

# Spiega una query
colibridb> \explain SELECT * FROM users WHERE name = 'Alice'

# Verifica integrità
colibridb> \check database
```

## 🚨 Troubleshooting

### Problema: Comando Non Riconosciuto

**Errore**:
```
Unknown command: \unknown
```

**Soluzione**:
```bash
colibridb> \help
```

### Problema: Errore di Sintassi SQL

**Errore**:
```
SQL Error: syntax error at position 15
```

**Soluzione**:
```bash
# Verifica la sintassi
colibridb> \explain SELECT * FROM users WHERE name = 'Alice'
```

### Problema: Transazione Non Attiva

**Errore**:
```
No active transaction
```

**Soluzione**:
```bash
colibridb> \begin
colibridb> \commit
```

---

<div align="center">

**🔧 CLI Reference ColibrìDB** - *Comandi completi per gestire il database*

[← Configurazione](Configuration) • [API Reference →](API-Reference)

</div>

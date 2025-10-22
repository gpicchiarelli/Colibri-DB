---
layout: doc
title: Quick Start
description: Inizia subito con Colibrì DB - installazione, configurazione e primi passi
---

# Quick Start

Benvenuto in Colibrì DB! Questa guida ti aiuterà a iniziare rapidamente con il nostro RDBMS sperimentale in Swift.

## Installazione

### Prerequisiti

- macOS 12.0 o superiore
- Xcode 15.0 o superiore
- Swift 6.2

### Installazione tramite Swift Package Manager

```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB

# Compila il progetto
swift build

# Esegui i test
swift test
```

## Primi Passi

### 1. Avvia il Server

```bash
# Avvia il server Colibrì DB
swift run coldb-server
```

Il server sarà disponibile su `http://localhost:8080`

### 2. Connettiti con il CLI

```bash
# Usa il client da riga di comando
swift run coldb
```

### 3. Crea il tuo primo database

```sql
-- Crea un database
CREATE DATABASE myapp;

-- Usa il database
USE myapp;

-- Crea una tabella
CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(255) UNIQUE
);

-- Inserisci alcuni dati
INSERT INTO users (name, email) VALUES 
    ('Alice', 'alice@example.com'),
    ('Bob', 'bob@example.com');

-- Esegui una query
SELECT * FROM users WHERE name LIKE 'A%';
```

## Caratteristiche Principali

### 🚀 Performance
- Buffer pool con algoritmo clock-sweep
- WAL (Write-Ahead Log) con ARIES
- Ottimizzatore di query cost-based

### 🔒 Concorrenza
- MVCC (Multi-Version Concurrency Control)
- Lock manager con deadlock detection
- Snapshot isolation

### 🌐 Distribuzione
- Consenso Raft integrato
- Sharding automatico
- Replica sincrona e asincrona

### 📊 Monitoring
- Metriche in tempo reale
- Health check automatici
- Dashboard di performance

## Esempi Avanzati

### Transazioni Distribuite

```sql
-- Inizia una transazione distribuita
BEGIN DISTRIBUTED TRANSACTION;

-- Operazioni su shard diversi
INSERT INTO users_shard1 (name) VALUES ('Alice');
INSERT INTO orders_shard2 (user_id, amount) VALUES (1, 99.99);

-- Commit atomico
COMMIT;
```

### Backup e Recovery

```bash
# Crea un backup
swift run coldb backup --database myapp --output backup.sql

# Ripristina da backup
swift run coldb restore --input backup.sql --database myapp_restored
```

## Configurazione

### File di Configurazione

Crea un file `colibridb.conf.json`:

```json
{
  "server": {
    "host": "localhost",
    "port": 8080,
    "max_connections": 100
  },
  "storage": {
    "data_directory": "./data",
    "buffer_pool_size": "256MB",
    "wal_buffer_size": "64MB"
  },
  "replication": {
    "enabled": true,
    "replicas": 3
  }
}
```

### Variabili d'Ambiente

```bash
export COLIBRI_DB_HOST=localhost
export COLIBRI_DB_PORT=8080
export COLIBRI_DB_DATA_DIR=./data
```

## Troubleshooting

### Problemi Comuni

**Errore: "Port already in use"**
```bash
# Trova il processo che usa la porta
lsof -i :8080

# Termina il processo
kill -9 <PID>
```

**Errore: "Database locked"**
```bash
# Verifica i processi attivi
swift run coldb status

# Forza la chiusura delle connessioni
swift run coldb kill-connections
```

### Log e Debug

```bash
# Abilita logging dettagliato
swift run coldb-server --log-level debug

# Visualizza i log
tail -f logs/colibri.log
```

## Prossimi Passi

1. **Leggi l'Architettura**: Scopri come funziona internamente Colibrì DB
2. **Esplora le Specifiche TLA+**: Comprendi le verifiche formali
3. **Contribuisci**: Partecipa allo sviluppo del progetto

## Supporto

- 📖 [Documentazione Completa](/wiki/)
- 🐛 [Segnala Bug](https://github.com/gpicchiarelli/Colibri-DB/issues)
- 💬 [Discussioni](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- 📧 [Email](mailto:support@colibridb.dev)

---

*Hai domande? Controlla la [sezione FAQ](/wiki/Troubleshooting.html) o apri una discussione su GitHub!*
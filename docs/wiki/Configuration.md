---
layout: page
title: Guida alla Configurazione
description: Guida completa alla configurazione di ColibrDB
---

# ⚙️ Guida alla Configurazione

Questa guida completa ti aiuterà a configurare ColibrDB per le tue esigenze specifiche.

## 📁 File di Configurazione

### Configurazione Principale

Il file `colibridb.conf.json` è il punto centrale per tutte le impostazioni:

```json
{
  "dataDir": "./data",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 1073741824,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": false,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap"
}
```

## 🔧 Parametri di Configurazione

### 1. Directory e Storage

#### `dataDir`
- **Tipo**: String
- **Default**: `"./data"`
- **Descrizione**: Directory dove vengono memorizzati i file del database
- **Esempio**: `"/var/lib/colibridb"`

```json
{
  "dataDir": "/var/lib/colibridb"
}
```

#### `storageEngine`
- **Tipo**: String
- **Default**: `"FileHeap"`
- **Opzioni**: `"FileHeap"`, `"Memory"`, `"Compressed"`
- **Descrizione**: Tipo di storage engine da utilizzare

```json
{
  "storageEngine": "FileHeap"
}
```

### 2. Connessioni e Concorrenza

#### `maxConnectionsLogical`
- **Tipo**: Integer
- **Default**: `1000000`
- **Range**: `1` - `10000000`
- **Descrizione**: Numero massimo di connessioni logiche simultanee

```json
{
  "maxConnectionsLogical": 1000000
}
```

#### `maxConnectionsPhysical`
- **Tipo**: Integer
- **Default**: `16`
- **Range**: `1` - `1024`
- **Descrizione**: Numero massimo di connessioni fisiche (thread)

```json
{
  "maxConnectionsPhysical": 16
}
```

### 3. Buffer Pool e Memoria

#### `bufferPoolSizeBytes`
- **Tipo**: Integer
- **Default**: `1073741824` (1GB)
- **Range**: `134217728` (128MB) - `8589934592` (8GB)
- **Descrizione**: Dimensione del buffer pool in byte

```json
{
  "bufferPoolSizeBytes": 2147483648  // 2GB
}
```

#### `pageSizeBytes`
- **Tipo**: Integer
- **Default**: `8192` (8KB)
- **Opzioni**: `4096`, `8192`, `16384`, `32768`
- **Descrizione**: Dimensione delle pagine in byte

```json
{
  "pageSizeBytes": 8192
}
```

### 4. Write-Ahead Logging (WAL)

#### `walEnabled`
- **Tipo**: Boolean
- **Default**: `true`
- **Descrizione**: Abilita il Write-Ahead Logging per durabilità

```json
{
  "walEnabled": true
}
```

#### `walBufferSizeBytes`
- **Tipo**: Integer
- **Default**: `16777216` (16MB)
- **Range**: `1048576` (1MB) - `134217728` (128MB)
- **Descrizione**: Dimensione del buffer WAL

```json
{
  "walBufferSizeBytes": 33554432  // 32MB
}
```

#### `walCheckpointInterval`
- **Tipo**: Integer
- **Default**: `300` (5 minuti)
- **Range**: `60` - `3600`
- **Descrizione**: Intervallo di checkpoint in secondi

```json
{
  "walCheckpointInterval": 300
}
```

### 5. Sicurezza e Integrità

#### `checksumEnabled`
- **Tipo**: Boolean
- **Default**: `true`
- **Descrizione**: Abilita checksum CRC32 per verifica integrità

```json
{
  "checksumEnabled": true
}
```

#### `encryptionEnabled`
- **Tipo**: Boolean
- **Default**: `false`
- **Descrizione**: Abilita crittografia dei dati su disco

```json
{
  "encryptionEnabled": false
}
```

#### `encryptionKey`
- **Tipo**: String
- **Default**: `null`
- **Descrizione**: Chiave di crittografia (se encryptionEnabled = true)

```json
{
  "encryptionEnabled": true,
  "encryptionKey": "your-encryption-key-here"
}
```

### 6. Indicizzazione

#### `indexImplementation`
- **Tipo**: String
- **Default**: `"Hash"`
- **Opzioni**: `"Hash"`, `"BTree"`, `"ART"`, `"SkipList"`, `"LSM"`
- **Descrizione**: Tipo di indice predefinito

```json
{
  "indexImplementation": "BTree"
}
```

#### `indexCacheSizeBytes`
- **Tipo**: Integer
- **Default**: `134217728` (128MB)
- **Range**: `16777216` (16MB) - `1073741824` (1GB)
- **Descrizione**: Dimensione cache per indici

```json
{
  "indexCacheSizeBytes": 268435456  // 256MB
}
```

### 7. Server e Rete

#### `serverEnabled`
- **Tipo**: Boolean
- **Default**: `false`
- **Descrizione**: Abilita il server di rete

```json
{
  "serverEnabled": true
}
```

#### `serverPort`
- **Tipo**: Integer
- **Default**: `5432`
- **Range**: `1024` - `65535`
- **Descrizione**: Porta del server

```json
{
  "serverEnabled": true,
  "serverPort": 5432
}
```

#### `serverHost`
- **Tipo**: String
- **Default**: `"localhost"`
- **Descrizione**: Indirizzo IP del server

```json
{
  "serverEnabled": true,
  "serverHost": "0.0.0.0"
}
```

### 8. Monitoring e Metriche

#### `metricsEnabled`
- **Tipo**: Boolean
- **Default**: `true`
- **Descrizione**: Abilita raccolta metriche

```json
{
  "metricsEnabled": true
}
```

#### `metricsPort`
- **Tipo**: Integer
- **Default**: `9090`
- **Range**: `1024` - `65535`
- **Descrizione**: Porta per metriche Prometheus

```json
{
  "metricsEnabled": true,
  "metricsPort": 9090
}
```

#### `logLevel`
- **Tipo**: String
- **Default**: `"INFO"`
- **Opzioni**: `"DEBUG"`, `"INFO"`, `"WARN"`, `"ERROR"`
- **Descrizione**: Livello di logging

```json
{
  "logLevel": "INFO"
}
```

### 9. CLI e Interfaccia

#### `cliEnabled`
- **Tipo**: Boolean
- **Default**: `true`
- **Descrizione**: Abilita interfaccia CLI

```json
{
  "cliEnabled": true
}
```

#### `cliPrompt`
- **Tipo**: String
- **Default**: `"colibridb> "`
- **Descrizione**: Prompt della CLI

```json
{
  "cliPrompt": "colibridb> "
}
```

## 🎯 Configurazioni Predefinite

### Configurazione Sviluppo

```json
{
  "dataDir": "./data",
  "maxConnectionsLogical": 100,
  "maxConnectionsPhysical": 4,
  "bufferPoolSizeBytes": 134217728,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": false,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap",
  "logLevel": "DEBUG"
}
```

### Configurazione Produzione

```json
{
  "dataDir": "/var/lib/colibridb",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 4294967296,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": false,
  "metricsEnabled": true,
  "serverEnabled": true,
  "serverPort": 5432,
  "serverHost": "0.0.0.0",
  "indexImplementation": "BTree",
  "storageEngine": "FileHeap",
  "logLevel": "WARN",
  "encryptionEnabled": true
}
```

### Configurazione Performance

```json
{
  "dataDir": "/var/lib/colibridb",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 32,
  "bufferPoolSizeBytes": 8589934592,
  "pageSizeBytes": 16384,
  "walEnabled": true,
  "walBufferSizeBytes": 134217728,
  "walCheckpointInterval": 600,
  "checksumEnabled": true,
  "cliEnabled": false,
  "metricsEnabled": true,
  "serverEnabled": true,
  "indexImplementation": "BTree",
  "storageEngine": "FileHeap",
  "indexCacheSizeBytes": 1073741824
}
```

## 🔄 Gestione Configurazione

### Modifica Configurazione da CLI

```bash
# Mostra configurazione corrente
\config

# Mostra un parametro specifico
\config get bufferPoolSizeBytes

# Modifica un parametro
\config set bufferPoolSizeBytes 2147483648

# Salva configurazione
\config save

# Ricarica configurazione
\config reload
```

### Validazione Configurazione

```bash
# Valida configurazione
\config validate

# Test configurazione
\config test
```

## 📊 Tuning Performance

### 1. Buffer Pool Sizing

**Regola generale**: 25-50% della RAM disponibile

```bash
# Calcola dimensione ottimale
total_ram=$(sysctl -n hw.memsize)
buffer_pool_size=$((total_ram / 4))  # 25% della RAM
echo "Buffer pool size: $buffer_pool_size bytes"
```

### 2. Page Size Selection

- **8KB**: Workload generali, OLTP
- **16KB**: Analytics, reporting
- **32KB**: Data warehousing

```json
{
  "pageSizeBytes": 8192   // OLTP
  "pageSizeBytes": 16384  // Analytics
  "pageSizeBytes": 32768  // Data Warehouse
}
```

### 3. WAL Configuration

```json
{
  "walBufferSizeBytes": 134217728,    // 128MB per write-heavy
  "walCheckpointInterval": 300,       // 5 minuti per durabilità
  "walEnabled": true
}
```

### 4. Index Configuration

```json
{
  "indexImplementation": "Hash",      // Lookups veloci
  "indexImplementation": "BTree",     // Range queries
  "indexCacheSizeBytes": 268435456    // 256MB cache indici
}
```

## 🚨 Configurazioni Critiche

### Parametri da Non Modificare

- **`pageSizeBytes`**: Cambiare richiede ricostruzione database
- **`dataDir`**: Cambiare richiede migrazione dati
- **`encryptionKey`**: Perdere la chiave = perdita dati

### Parametri da Monitorare

- **`bufferPoolSizeBytes`**: Monitora hit rate
- **`maxConnectionsPhysical`**: Monitora utilizzo CPU
- **`walBufferSizeBytes`**: Monitora throughput WAL

## 🔍 Troubleshooting Configurazione

### Problema: Buffer Pool Troppo Piccolo

**Sintomi**:
- Hit rate < 90%
- I/O elevato
- Performance degradate

**Soluzione**:
```json
{
  "bufferPoolSizeBytes": 4294967296  // Aumenta a 4GB
}
```

### Problema: WAL Buffer Overflow

**Sintomi**:
- Errori WAL
- Transazioni lente
- Checkpoint frequenti

**Soluzione**:
```json
{
  "walBufferSizeBytes": 134217728,    // Aumenta a 128MB
  "walCheckpointInterval": 600        // Checkpoint ogni 10 min
}
```

### Problema: Connessioni Esaurite

**Sintomi**:
- Errori di connessione
- Timeout
- Performance degradate

**Soluzione**:
```json
{
  "maxConnectionsPhysical": 32,       // Aumenta connessioni fisiche
  "maxConnectionsLogical": 2000000    // Aumenta connessioni logiche
}
```

## 📚 Configurazioni Avanzate

### Configurazione Multi-Tenant

```json
{
  "dataDir": "/var/lib/colibridb",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 4294967296,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "serverEnabled": true,
  "serverPort": 5432,
  "serverHost": "0.0.0.0",
  "indexImplementation": "BTree",
  "storageEngine": "FileHeap",
  "encryptionEnabled": true,
  "metricsEnabled": true,
  "metricsPort": 9090
}
```

### Configurazione High Availability

```json
{
  "dataDir": "/var/lib/colibridb",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 32,
  "bufferPoolSizeBytes": 8589934592,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "walBufferSizeBytes": 134217728,
  "walCheckpointInterval": 300,
  "checksumEnabled": true,
  "serverEnabled": true,
  "serverPort": 5432,
  "serverHost": "0.0.0.0",
  "indexImplementation": "BTree",
  "storageEngine": "FileHeap",
  "encryptionEnabled": true,
  "metricsEnabled": true,
  "metricsPort": 9090,
  "logLevel": "WARN"
}
```

---

<div align="center">

**⚙️ Configurazione ColibrDB** - *Ottimizza le performance per le tue esigenze*

[← Architettura]({{ site.baseurl }}/docs/wiki/Architecture) • [CLI Reference →]({{ site.baseurl }}/docs/wiki/CLI-Reference)

</div>

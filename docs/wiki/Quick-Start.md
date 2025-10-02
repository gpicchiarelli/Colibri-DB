---
layout: doc
title: Quick Start Guide
description: Inizia con Colibrì DB in meno di 5 minuti. Installazione, configurazione e primi passi con il database.
category: Getting Started
difficulty: Beginner
version: 0.1.0
---

# 🚀 Quick Start Guide

Benvenuto in Colibrì DB! Questa guida ti aiuterà a installare e configurare il database in meno di 5 minuti.

## 📋 Prerequisiti

Prima di iniziare, assicurati di avere:

- **macOS 13.0+** (Ventura o successivo)
- **Swift 6.2** o toolchain compatibile
- **Xcode 15.0+** (opzionale, per sviluppo)
- **Git** per clonare il repository
- **Almeno 2GB** di spazio libero su disco

<div class="alert alert-info">
<strong>💡 Suggerimento:</strong> Colibrì DB è ottimizzato per Apple Silicon (M1/M2/M3), ma funziona anche su Intel Mac.
</div>

## ⚡ Installazione Rapida

### 1. Clona il Repository

```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB

# Verifica la versione Swift
swift --version
```

### 2. Compila il Progetto

```bash
# Compila in modalità release per performance ottimali
swift build -c release

# Oppure in modalità debug per sviluppo
swift build
```

<div class="alert alert-success">
<strong>✅ Compilazione riuscita!</strong> Se tutto è andato bene, dovresti vedere il messaggio di successo.
</div>

### 3. Verifica l'Installazione

```bash
# Testa la CLI
.build/release/coldb --version

# Output atteso:
# Colibrì DB v0.1.0-alpha
# Swift 6.2 - macOS 13.0+
```

## 🎯 Prima Sessione

### Avvia la CLI Interattiva

```bash
# Avvia Colibrì DB in modalità interattiva
.build/release/coldb

# Vedrai il prompt:
# coldb> 
```

### Comandi Base

Una volta nella CLI, prova questi comandi:

```sql
-- Visualizza informazioni sul database
\info

-- Crea la tua prima tabella
\create table users

-- Inserisci alcuni dati
\insert users id=1,name="Alice",age=25,email="alice@example.com"
\insert users id=2,name="Bob",age=30,email="bob@example.com"
\insert users id=3,name="Charlie",age=35,email="charlie@example.com"

-- Visualizza tutti i dati
\select * FROM users

-- Crea un indice per performance
\create index idx_users_name ON users(name) USING BTree

-- Cerca usando l'indice
\index search users idx_users_name "Alice"

-- Query con filtri
\select * FROM users WHERE age > 25
```

### Operazioni Avanzate

```sql
-- Inizia una transazione
\begin

-- Aggiorna un record
\update users SET age=26 WHERE id=1

-- Elimina un record
\delete FROM users WHERE id=3

-- Conferma le modifiche
\commit

-- Visualizza statistiche performance
\stats

-- Esegui manutenzione
\vacuum
```

## 📁 Configurazione

### File di Configurazione

Colibrì DB usa il file `colibridb.conf.json` per la configurazione:

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
  "indexImplementation": "BTree",
  "storageEngine": "FileHeap"
}
```

### Parametri Principali

| Parametro | Descrizione | Valore Consigliato |
|-----------|-------------|-------------------|
| `dataDir` | Directory per i file del database | `./data` |
| `bufferPoolSizeBytes` | Dimensione buffer pool in bytes | `1GB` per sviluppo |
| `pageSizeBytes` | Dimensione pagina | `8192` (8KB) |
| `walEnabled` | Abilita Write-Ahead Logging | `true` |
| `checksumEnabled` | Abilita checksum CRC32 | `true` |

### Configurazione per Sviluppo

```json
{
  "dataDir": "./dev-data",
  "bufferPoolSizeBytes": 268435456,
  "pageSizeBytes": 4096,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true
}
```

### Configurazione per Produzione

```json
{
  "dataDir": "/var/lib/colibridb",
  "bufferPoolSizeBytes": 4294967296,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": false,
  "serverEnabled": true,
  "metricsEnabled": true
}
```

## 🔧 Comandi CLI Essenziali

### Gestione Database

```bash
# Avvia con configurazione specifica
.build/release/coldb --config custom.conf.json

# Modalità sviluppo con debug
.build/debug/coldb-dev

# Avvia server di rete
.build/release/coldb-server --port 5432
```

### Comandi Interattivi

| Comando | Descrizione | Esempio |
|---------|-------------|---------|
| `\help` | Mostra aiuto | `\help` |
| `\info` | Info database | `\info` |
| `\tables` | Lista tabelle | `\tables` |
| `\indexes` | Lista indici | `\indexes` |
| `\stats` | Statistiche | `\stats` |
| `\vacuum` | Manutenzione | `\vacuum` |
| `\checkpoint` | Forza checkpoint | `\checkpoint` |
| `\quit` | Esci | `\quit` |

### Import/Export

```bash
# Esporta dati in CSV
\export users users.csv

# Importa dati da CSV
\import users users.csv

# Backup completo
\backup backup.sql

# Ripristino
\restore backup.sql
```

## 🚨 Risoluzione Problemi

### Errori Comuni

**Errore: "Swift compiler not found"**
```bash
# Installa Xcode Command Line Tools
xcode-select --install

# Oppure scarica Swift da swift.org
```

**Errore: "Permission denied"**
```bash
# Assicurati di avere i permessi
chmod +x .build/release/coldb

# Oppure usa sudo per directory di sistema
sudo mkdir -p /var/lib/colibridb
sudo chown $(whoami) /var/lib/colibridb
```

**Errore: "Database corrupted"**
```bash
# Ripara il database
.build/release/coldb --repair

# Oppure ricrea da backup
.build/release/coldb --restore backup.sql
```

### Performance Issues

**Database lento?**
- Aumenta `bufferPoolSizeBytes`
- Crea indici sulle colonne più usate
- Esegui `\vacuum` periodicamente
- Monitora con `\stats`

**Memoria insufficiente?**
- Riduci `bufferPoolSizeBytes`
- Usa `pageSizeBytes` più piccole
- Chiudi connessioni non utilizzate

## 📚 Prossimi Passi

Ora che hai Colibrì DB funzionante, esplora:

1. **[Architettura]({{ '/wiki/Architecture' | relative_url }})** - Comprendi come funziona internamente
2. **[API Reference]({{ '/wiki/API-Reference' | relative_url }})** - Integra nelle tue applicazioni
3. **[Performance]({{ '/wiki/Performance' | relative_url }})** - Ottimizza per il tuo caso d'uso
4. **[Examples]({{ '/wiki/Examples' | relative_url }})** - Esempi pratici e casi d'uso

## 🤝 Supporto

Hai bisogno di aiuto?

- 📖 [Documentazione completa]({{ '/wiki/' | relative_url }})
- 🐛 [Segnala bug](https://github.com/gpicchiarelli/Colibri-DB/issues)
- 💬 [Discussioni](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- 📧 [Contatta il team](mailto:support@colibridb.org)

<div class="alert alert-success">
<strong>🎉 Congratulazioni!</strong> Hai completato il setup di Colibrì DB. Sei pronto per esplorare tutte le funzionalità del database!
</div>
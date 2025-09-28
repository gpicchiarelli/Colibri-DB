---
layout: page
title: Quick Start Guide
description: Guida rapida per installare e utilizzare ColibrìDB
---

# 🚀 Quick Start Guide

Questa guida ti aiuterà a installare e utilizzare ColibrìDB in pochi minuti.

## 📋 Prerequisiti

### Sistema Operativo
- **macOS 13.0+** (Ventura o superiore)
- **Apple Silicon** (M1/M2/M3) consigliato per performance ottimali
- **Intel Mac** supportato ma con performance ridotte

### Software Richiesto
- **Swift 6.2+** (o toolchain compatibile)
- **Xcode 15.0+** (per sviluppo)
- **Git** (per clonare il repository)

### Verifica Prerequisiti

```bash
# Verifica versione Swift
swift --version
# Output atteso: Swift version 6.2.x

# Verifica versione macOS
sw_vers
# Output atteso: ProductVersion: 13.x o superiore

# Verifica architettura
uname -m
# Output atteso: arm64 (Apple Silicon) o x86_64 (Intel)
```

## ⚡ Installazione Rapida

### 1. Clona il Repository

```bash
git clone https://github.com/gpicchiarelli/Colibr-DB.git
cd Colibr-DB
```

### 2. Compila il Progetto

```bash
# Compila tutti i target
swift build

# Compila in modalità release per performance ottimali
swift build -c release
```

### 3. Verifica l'Installazione

```bash
# Testa la CLI
.build/debug/coldb --version

# Testa il server (opzionale)
.build/debug/coldb-server --version
```

## 🎯 Prima Sessione

### Avvio della CLI

```bash
# Avvia la CLI con configurazione predefinita
.build/debug/coldb --config colibridb.conf.json

# Oppure avvia in modalità interattiva
.build/debug/coldb
```

### Comandi Base

```bash
# Mostra aiuto
\help

# Mostra stato del database
\status

# Mostra configurazione corrente
\config

# Mostra tabelle esistenti
\list tables

# Mostra indici esistenti
\list indexes
```

## 📊 Creazione di una Tabella

### 1. Crea una Tabella

```bash
# Crea una tabella semplice
\create table users

# Crea una tabella con schema specifico
\create table products (id INTEGER, name TEXT, price DECIMAL, category TEXT)
```

### 2. Inserisci Dati

```bash
# Inserisci un singolo record
\insert users id=1,name=Alice,age=25,email=alice@example.com

# Inserisci più record
\insert users id=2,name=Bob,age=30,email=bob@example.com
\insert users id=3,name=Charlie,age=35,email=charlie@example.com
```

### 3. Interroga i Dati

```bash
# Seleziona tutti i record
\select * FROM users

# Seleziona con condizioni
\select * FROM users WHERE age > 25

# Seleziona colonne specifiche
\select name, email FROM users WHERE age BETWEEN 25 AND 35
```

## 🔍 Creazione di Indici

### 1. Crea un Indice

```bash
# Crea un indice B+Tree su una colonna
\create index idx_users_name ON users(name) USING BTree

# Crea un indice Hash per lookups veloci
\create index idx_users_email ON users(email) USING Hash
```

### 2. Usa l'Indice

```bash
# Cerca usando l'indice
\index search users idx_users_name Alice

# Verifica l'utilizzo dell'indice
\explain \select * FROM users WHERE name = 'Alice'
```

## 🔄 Gestione delle Transazioni

### 1. Inizia una Transazione

```bash
# Inizia una transazione
\begin

# Esegui operazioni
\insert users id=4,name=David,age=28,email=david@example.com
\insert users id=5,name=Eve,age=32,email=eve@example.com

# Conferma la transazione
\commit
```

### 2. Rollback delle Modifiche

```bash
# Inizia una transazione
\begin

# Esegui operazioni
\insert users id=6,name=Frank,age=40,email=frank@example.com

# Annulla le modifiche
\rollback
```

## 📁 Import/Export Dati

### 1. Export in CSV

```bash
# Esporta una tabella in CSV
\export users TO users.csv

# Esporta con query specifica
\export \select name, email FROM users WHERE age > 25 TO active_users.csv
```

### 2. Import da CSV

```bash
# Importa da CSV
\import users FROM users_backup.csv

# Importa con mapping colonne
\import users (name, email, age) FROM users_data.csv
```

## ⚙️ Configurazione Base

### File di Configurazione

Il file `colibridb.conf.json` controlla il comportamento del database:

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

### Modifica Configurazione

```bash
# Mostra configurazione corrente
\config

# Modifica una impostazione
\config set bufferPoolSizeBytes 2147483648

# Salva configurazione
\config save
```

## 🧪 Test delle Funzionalità

### 1. Test di Performance

```bash
# Esegui benchmark WAL
swift run benchmarks --wal-throughput --duration 30s

# Esegui benchmark B+Tree
swift run benchmarks --btree-lookups --keys 1000000

# Esegui benchmark transazioni
swift run benchmarks --transaction-throughput --duration 30s
```

### 2. Test di Integrità

```bash
# Verifica integrità del database
\check database

# Verifica integrità degli indici
\check indexes

# Verifica integrità del WAL
\check wal
```

## 🚨 Risoluzione Problemi Comuni

### Problema: Errore di Compilazione

```bash
# Soluzione: Aggiorna Swift
swift --version

# Se necessario, installa Xcode Command Line Tools
xcode-select --install
```

### Problema: Errore di Permessi

```bash
# Soluzione: Verifica permessi directory
ls -la data/
chmod 755 data/
```

### Problema: Porta Occupata (Server)

```bash
# Soluzione: Cambia porta nel config
\config set serverPort 5433
```

## 📚 Prossimi Passi

Ora che hai completato il Quick Start, esplora:

1. **[Architettura del Sistema]({{ site.baseurl }}/wiki/Architecture)** - Comprendi i componenti interni
2. **[CLI Reference]({{ site.baseurl }}/wiki/CLI-Reference)** - Impara tutti i comandi disponibili
3. **[Configurazione]({{ site.baseurl }}/wiki/Configuration)** - Personalizza il database per le tue esigenze
4. **[Esempi Pratici]({{ site.baseurl }}/wiki/Examples)** - Casi d'uso avanzati e pattern comuni
5. **[Performance Guide]({{ site.baseurl }}/wiki/Performance)** - Ottimizza le performance del database

## 🆘 Supporto

Se incontri problemi:

1. **Consulta la [documentazione completa](https://github.com/gpicchiarelli/Colibr-DB/blob/main/docs/README.md)**
2. **Cerca nelle [issue esistenti](https://github.com/gpicchiarelli/Colibr-DB/issues)**
3. **Apri una [nuova issue](https://github.com/gpicchiarelli/Colibr-DB/issues/new)**
4. **Partecipa alle [discussioni](https://github.com/gpicchiarelli/Colibr-DB/discussions)**

---

<div align="center">

**🎉 Congratulazioni!** Hai completato il Quick Start di ColibrìDB.

[← Torna alla Home]({{ site.baseurl }}/wiki/Home) • [Architettura del Sistema →]({{ site.baseurl }}/wiki/Architecture)

</div>

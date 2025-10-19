---
layout: doc
title: Troubleshooting Guide
description: Guida alla risoluzione dei problemi comuni con Colibrì DB
---

# 🚨 Troubleshooting Guide

Guida completa per risolvere i problemi più comuni con Colibrì DB.

## 🎯 Panoramica

Questa guida ti aiuterà a:

- Diagnosticare problemi comuni
- Risolvere errori di configurazione
- Ottimizzare le performance
- Recuperare da situazioni critiche

## 🔍 Diagnostica Problemi

### 1. Verifica Stato Sistema

```bash
# Controlla lo stato del database
colibridb> \status

# Verifica integrità
colibridb> \check database

# Mostra statistiche
colibridb> \stats
```

### 2. Log e Debugging

```bash
# Abilita logging dettagliato
colibridb> \config set logLevel DEBUG

# Mostra log recenti
colibridb> \log show

# Verifica errori WAL
colibridb> \check wal
```

### 3. Monitoraggio Risorse

```bash
# Controlla utilizzo memoria
colibridb> \stats memory

# Verifica I/O disco
colibridb> \stats io

# Monitora connessioni
colibridb> \stats connections
```

## 🚨 Problemi Comuni

### Problema: Database Non Si Avvia

#### Sintomi
```
fatal: Failed to initialize database
Error: Could not open data directory
```

#### Cause Possibili
1. Directory dati non esiste
2. Permessi insufficienti
3. File di configurazione corrotto
4. Porta già in uso (server mode)

#### Soluzioni

**1. Verifica Directory Dati**
```bash
# Controlla se la directory esiste
ls -la ./data

# Crea la directory se mancante
mkdir -p ./data
chmod 755 ./data
```

**2. Verifica Permessi**
```bash
# Controlla permessi directory
ls -ld ./data

# Corregge permessi
chmod 755 ./data
chown -R $(whoami) ./data
```

**3. Verifica Configurazione**
```bash
# Valida file di configurazione
colibridb> \config validate

# Ricarica configurazione
colibridb> \config reload
```

**4. Verifica Porta Server**
```bash
# Controlla se la porta è in uso
lsof -i :5432

# Cambia porta nel config
colibridb> \config set serverPort 5433
```

### Problema: Errore di Compilazione

#### Sintomi
```
error: Swift 6.2 required
error: Package resolution failed
error: Build failed
```

#### Soluzioni

**1. Aggiorna Swift**
```bash
# Verifica versione Swift
swift --version

# Installa Xcode Command Line Tools
xcode-select --install

# Aggiorna Xcode se necessario
```

**2. Risolvi Dipendenze**
```bash
# Pulisci cache
swift package clean

# Risolvi dipendenze
swift package resolve

# Ricompila
swift build
```

**3. Verifica Architettura**
```bash
# Verifica architettura
uname -m

# Compila per architettura specifica
swift build -Xswiftc -target -Xswiftc arm64-apple-macos13.0
```

### Problema: Performance Degradate

#### Sintomi
- Query lente
- Alto utilizzo CPU
- Memoria esaurita
- I/O disco elevato

#### Diagnostica

**1. Analizza Performance**
```bash
# Mostra statistiche dettagliate
colibridb> \stats detailed

# Verifica hit rate buffer pool
colibridb> \stats buffer

# Controlla utilizzo indici
colibridb> \stats indexes
```

**2. Identifica Query Lente**
```bash
# Abilita timing
colibridb> \timing

# Spiega query
colibridb> \explain SELECT * FROM users WHERE name = 'Alice'

# Mostra piano di esecuzione
colibridb> \explain plan SELECT * FROM users WHERE age > 25
```

#### Soluzioni

**1. Ottimizza Buffer Pool**
```bash
# Aumenta dimensione buffer pool
colibridb> \config set bufferPoolSizeBytes 2147483648

# Verifica hit rate
colibridb> \stats buffer
```

**2. Crea Indici Mancanti**
```bash
# Analizza query per indici mancanti
colibridb> \analyze query "SELECT * FROM users WHERE name = 'Alice'"

# Crea indice suggerito
colibridb> \create index idx_users_name ON users(name) USING BTree
```

**3. Ottimizza Configurazione**
```bash
# Aumenta page size per workload analytics
colibridb> \config set pageSizeBytes 16384

# Ottimizza WAL per write-heavy
colibridb> \config set walBufferSizeBytes 134217728
```

### Problema: Transazioni Bloccate

#### Sintomi
- Query che non completano
- Timeout su operazioni
- Deadlock rilevati
- Connessioni bloccate

#### Diagnostica

**1. Identifica Transazioni Attive**
```bash
# Mostra transazioni attive
colibridb> \transactions

# Verifica lock
colibridb> \locks

# Controlla deadlock
colibridb> \deadlocks
```

**2. Analizza Blocchi**
```bash
# Mostra lock per risorsa
colibridb> \locks table users

# Verifica timeout
colibridb> \config get lockTimeoutSeconds
```

#### Soluzioni

**1. Termina Transazioni Bloccate**
```bash
# Lista transazioni attive
colibridb> \transactions

# Termina transazione specifica
colibridb> \kill transaction 12345

# Rollback forzato
colibridb> \rollback force 12345
```

**2. Risolvi Deadlock**
```bash
# Rileva deadlock
colibridb> \deadlock detect

# Risolvi automaticamente
colibridb> \deadlock resolve

# Aumenta timeout
colibridb> \config set lockTimeoutSeconds 60
```

**3. Ottimizza Isolamento**
```bash
# Usa isolamento meno restrittivo
colibridb> \config set defaultIsolationLevel READ_COMMITTED

# Abilita snapshot isolation
colibridb> \config set snapshotIsolation true
```

### Problema: Corruzione Dati

#### Sintomi
- Errori di checksum
- Dati inconsistenti
- Crash durante operazioni
- WAL corrotto

#### Diagnostica

**1. Verifica Integrità**
```bash
# Controlla integrità database
colibridb> \check database

# Verifica checksum
colibridb> \check checksums

# Controlla WAL
colibridb> \check wal
```

**2. Identifica Corruzione**
```bash
# Verifica tabelle specifiche
colibridb> \check table users

# Controlla indici
colibridb> \check indexes

# Verifica pagine
colibridb> \check pages
```

#### Soluzioni

**1. Recovery Automatico**
```bash
# Avvia recovery
colibridb> \recovery

# Verifica dopo recovery
colibridb> \check database
```

**2. Recovery Manuale**
```bash
# Backup dati esistenti
colibridb> \backup TO backup_$(date +%Y%m%d).sql

# Ripristina da WAL
colibridb> \recovery from_wal

# Verifica integrità
colibridb> \check database
```

**3. Riparazione Avanzata**
```bash
# Modalità recovery
colibridb> \start recovery_mode

# Ripara tabelle corrotte
colibridb> \repair table users

# Ricostruisci indici
colibridb> \rebuild indexes
```

### Problema: Memoria Esaurita

#### Sintomi
- Errori "out of memory"
- Swap elevato
- Performance degradate
- Crash del sistema

#### Diagnostica

**1. Monitora Utilizzo Memoria**
```bash
# Mostra utilizzo memoria
colibridb> \stats memory

# Verifica buffer pool
colibridb> \stats buffer

# Controlla connessioni
colibridb> \stats connections
```

**2. Identifica Cause**
```bash
# Verifica query con molti risultati
colibridb> \query stats

# Controlla indici grandi
colibridb> \index stats

# Monitora WAL
colibridb> \wal stats
```

#### Soluzioni

**1. Riduci Buffer Pool**
```bash
# Riduci dimensione buffer pool
colibridb> \config set bufferPoolSizeBytes 536870912

# Riavvia per applicare modifiche
colibridb> \restart
```

**2. Ottimizza Query**
```bash
# Aggiungi LIMIT alle query
colibridb> \sql SELECT * FROM users LIMIT 1000

# Usa indici per ridurre scansioni
colibridb> \create index idx_users_name ON users(name)
```

**3. Gestisci Connessioni**
```bash
# Riduci connessioni massime
colibridb> \config set maxConnectionsPhysical 8

# Timeout connessioni inattive
colibridb> \config set connectionTimeoutSeconds 300
```

## 🔧 Strumenti di Diagnostica

### 1. Health Check Completo

```bash
#!/bin/bash
# Script di health check completo

echo "=== Colibrì DB Health Check ==="

# Verifica stato database
echo "1. Database Status:"
colibridb> \status

# Verifica integrità
echo "2. Database Integrity:"
colibridb> \check database

# Verifica performance
echo "3. Performance Stats:"
colibridb> \stats

# Verifica configurazione
echo "4. Configuration:"
colibridb> \config

# Verifica log errori
echo "5. Recent Errors:"
colibridb> \log errors

echo "=== Health Check Complete ==="
```

### 2. Monitoraggio Continuo

```bash
#!/bin/bash
# Script di monitoraggio continuo

while true; do
    echo "$(date): Checking database health..."
    
    # Verifica stato
    if ! colibridb> \status > /dev/null 2>&1; then
        echo "ERROR: Database not responding"
        # Invia alert
    fi
    
    # Verifica memoria
    memory_usage=$(colibridb> \stats memory | grep "Usage" | awk '{print $3}')
    if [ "$memory_usage" -gt 90 ]; then
        echo "WARNING: High memory usage: $memory_usage%"
    fi
    
    # Verifica hit rate
    hit_rate=$(colibridb> \stats buffer | grep "Hit Rate" | awk '{print $3}')
    if [ "$hit_rate" -lt 90 ]; then
        echo "WARNING: Low buffer hit rate: $hit_rate%"
    fi
    
    sleep 60
done
```

### 3. Backup e Recovery

```bash
#!/bin/bash
# Script di backup automatico

BACKUP_DIR="./backups"
DATE=$(date +%Y%m%d_%H%M%S)

# Crea directory backup
mkdir -p "$BACKUP_DIR"

# Backup database
echo "Creating backup: $DATE"
colibridb> \backup TO "$BACKUP_DIR/backup_$DATE.sql"

# Backup configurazione
cp colibridb.conf.json "$BACKUP_DIR/config_$DATE.json"

# Backup WAL
cp data/global.wal "$BACKUP_DIR/wal_$DATE.wal"

# Pulisci backup vecchi (più di 7 giorni)
find "$BACKUP_DIR" -name "backup_*" -mtime +7 -delete

echo "Backup completed: $DATE"
```

## 📊 Performance Troubleshooting

### 1. Query Lente

**Identifica Query Problematiche**
```bash
# Abilita query logging
colibridb> \config set queryLogging true

# Mostra query lente
colibridb> \slow queries

# Analizza query specifica
colibridb> \analyze query "SELECT * FROM users WHERE age > 25"
```

**Ottimizza Query**
```bash
# Crea indici appropriati
colibridb> \create index idx_users_age ON users(age) USING BTree

# Usa LIMIT per query grandi
colibridb> \sql SELECT * FROM users LIMIT 1000

# Evita SELECT * quando possibile
colibridb> \sql SELECT id, name FROM users WHERE age > 25
```

### 2. I/O Elevato

**Identifica Cause I/O**
```bash
# Mostra statistiche I/O
colibridb> \stats io

# Verifica hit rate buffer pool
colibridb> \stats buffer

# Controlla WAL throughput
colibridb> \stats wal
```

**Riduci I/O**
```bash
# Aumenta buffer pool
colibridb> \config set bufferPoolSizeBytes 2147483648

# Ottimizza WAL
colibridb> \config set walBufferSizeBytes 134217728

# Usa indici per ridurre scansioni
colibridb> \create index idx_users_name ON users(name)
```

### 3. Concorrenza Problemi

**Identifica Contention**
```bash
# Mostra lock attivi
colibridb> \locks

# Verifica deadlock
colibridb> \deadlocks

# Controlla transazioni lunghe
colibridb> \transactions long
```

**Migliora Concorrenza**
```bash
# Riduci isolamento
colibridb> \config set defaultIsolationLevel READ_COMMITTED

# Aumenta timeout
colibridb> \config set lockTimeoutSeconds 60

# Ottimizza locking
colibridb> \config set lockGranularity ROW
```

## 🆘 Situazioni di Emergenza

### 1. Database Corrotto

**Recovery Immediato**
```bash
# Stop database
colibridb> \shutdown

# Modalità recovery
colibridb> \start recovery_mode

# Recovery da WAL
colibridb> \recovery from_wal

# Verifica integrità
colibridb> \check database
```

### 2. Perdita Dati

**Recovery da Backup**
```bash
# Lista backup disponibili
ls -la ./backups/

# Ripristina da backup
colibridb> \restore FROM ./backups/backup_20241201_120000.sql

# Verifica dati ripristinati
colibridb> \check database
```

### 3. Sistema Bloccato

**Recovery Forzato**
```bash
# Kill tutte le connessioni
colibridb> \kill all_connections

# Forza checkpoint
colibridb> \force checkpoint

# Riavvia database
colibridb> \restart
```

## 📞 Supporto

### 1. Raccogli Informazioni

Prima di chiedere aiuto, raccogli:

```bash
# Informazioni sistema
sw_vers
swift --version
uname -a

# Stato database
colibridb> \status
colibridb> \config
colibridb> \stats

# Log errori
colibridb> \log errors

# Informazioni problema
colibridb> \diagnose
```

### 2. Crea Issue

Quando crei un'issue su GitHub, includi:

1. **Descrizione del problema**
2. **Passi per riprodurre**
3. **Output dei comandi di diagnostica**
4. **Configurazione sistema**
5. **Log errori**
6. **Screenshot se applicabile**

### 3. Community Support

- **GitHub Issues**: Per bug e problemi tecnici
- **GitHub Discussions**: Per domande e discussioni
- **Discord**: Per supporto in tempo reale (se disponibile)

---

<div align="center">

**🚨 Troubleshooting Colibrì DB** - *Risolvi problemi e ottimizza le performance*

[← Development Guide]({{ site.baseurl }}/wiki/Development) • [Performance Guide →]({{ site.baseurl }}/wiki/Performance)

</div>

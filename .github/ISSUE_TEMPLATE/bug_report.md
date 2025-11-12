---
name: 🐛 Bug Report
about: Crea un report per aiutarci a migliorare ColibrDB
title: '[BUG] '
labels: ['bug', 'needs-triage']
assignees: ''

---

## 🐛 Descrizione del Bug
<!-- Fornisci una descrizione chiara e concisa del bug -->

## 🔄 Passi per Riprodurre
<!-- Descrivi i passi per riprodurre il comportamento -->
1. Vai a '...'
2. Clicca su '....'
3. Scorri fino a '....'
4. Vedi l'errore

## ✅ Comportamento Atteso
<!-- Descrivi cosa ti aspettavi che succedesse -->

## ❌ Comportamento Attuale
<!-- Descrivi cosa succede invece -->

## 📸 Screenshots
<!-- Se applicabile, aggiungi screenshot per aiutare a spiegare il problema -->

## 🖥️ Ambiente
<!-- Compila le informazioni sul tuo ambiente -->
- **OS**: [es. macOS 14.0, Linux Ubuntu 22.04]
- **Swift Version**: [es. 6.0]
- **ColibrDB Version**: [es. v0.1.0-alpha]
- **Architecture**: [es. ARM64, x86_64]

## 📋 Configurazione
<!-- Se applicabile, condividi la tua configurazione -->
```json
{
  "dataDir": "./data",
  "maxConnectionsLogical": 1000000,
  "bufferPoolSizeBytes": 1073741824,
  "pageSizeBytes": 8192,
  "walEnabled": true
}
```

## 📝 Log e Output
<!-- Inserisci qui i log di errore o output rilevanti -->
```
Inserisci qui i log di errore
```

## 🔍 Informazioni Aggiuntive
<!-- Aggiungi qualsiasi altra informazione sul problema -->

## 🏷️ Etichette Suggerite
<!-- Suggerisci etichette per categorizzare il bug -->
- `component:storage` - Problemi con storage engine
- `component:wal` - Problemi con Write-Ahead Logging
- `component:index` - Problemi con indici
- `component:mvcc` - Problemi con MVCC
- `component:cli` - Problemi con CLI
- `component:server` - Problemi con server
- `severity:critical` - Bug critico che blocca l'uso
- `severity:high` - Bug importante che limita funzionalità
- `severity:medium` - Bug che causa problemi minori
- `severity:low` - Bug cosmetico o di usabilità

---

## 🏗️ Architettura ColibrDB - Riferimento Rapido

### Componenti Principali
- **ColibriCore**: Motore database core
- **coldb**: CLI amministrativa
- **coldb-server**: Server di rete
- **benchmarks**: Test di performance

### Moduli Core
- **Storage**: Heap file con slot directory
- **WAL**: Write-Ahead Logging ARIES-compliant
- **Buffer Pool**: Eviction LRU/Clock
- **Indici**: B+Tree, Hash, ART, LSM
- **MVCC**: Multi-Version Concurrency Control
- **Catalog**: Gestione metadati

### Comandi di Debug Utili
```bash
# Esegui test specifici
swift test --filter [NomeModulo]

# Esegui benchmark
swift run benchmarks --help

# Debug con verbose logging
swift run coldb --verbose

# Controlla stato WAL
swift run coldb-dev --wal-status
```
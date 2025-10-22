# ColibrìDB Test Suite

Questa è la suite completa di test per ColibrìDB, un database relazionale moderno scritto in Swift. La suite include test per tutti i moduli e funzionalità del sistema.

## 📋 Panoramica

La suite di test è organizzata in diverse categorie:

### 🏗️ Test Core
- **DatabaseTests**: Test per il motore database principale
- **TransactionManagerTests**: Test per la gestione delle transazioni e proprietà ACID
- **BufferPoolTests**: Test per il buffer pool e gestione della memoria
- **WALTests**: Test per il Write-Ahead Log e recovery
- **BTreeIndexTests**: Test per gli indici B+Tree e operazioni di ricerca

### 🔍 Test Query
- **SQLParserTests**: Test per il parser SQL e tokenizzazione

### 🌐 Test Distribuiti
- **DistributedTests**: Test per consenso Raft, replicazione e sharding
- **RecoveryTests**: Test per recovery, fault tolerance e error handling

### 🔒 Test Sicurezza
- **SecurityTests**: Test per autenticazione, autorizzazione e sicurezza

### 🔗 Test Integrazione
- **IntegrationTests**: Test end-to-end per verificare il funzionamento completo del sistema

### ⚡ Test Performance
- **PerformanceTests**: Test per performance, benchmark e ottimizzazione
- **StressTests**: Test per condizioni di stress e scenari estremi

## 🚀 Esecuzione dei Test

### Esecuzione Completa
```bash
swift test
```

### Esecuzione di Test Specifici
```bash
# Test del database core
swift test --filter DatabaseTests

# Test delle transazioni
swift test --filter TransactionManagerTests

# Test di performance
swift test --filter PerformanceTests
```

### Esecuzione con Output Dettagliato
```bash
swift test --verbose
```

## 📊 Struttura dei Test

### Test Structure
Il file `TestStructure.swift` contiene:
- **TestUtils**: Utility per creare dati di test, misurare performance, e gestire operazioni asincrone
- **TestAssertions**: Funzioni di asserzione personalizzate per verificare condizioni
- **TestDataGenerator**: Generatori di dati di test per tabelle, righe e query SQL
- **BaseTest**: Classe base per test con setup/teardown comune

### Categorie di Test

#### 🧪 Unit Tests
Test per singoli moduli e componenti:
- Inizializzazione e configurazione
- Operazioni CRUD di base
- Gestione degli stati interni
- Invarianti e proprietà

#### 🔗 Integration Tests
Test per l'integrazione tra moduli:
- Workflow completi del database
- Interazione tra buffer pool e WAL
- Gestione delle transazioni distribuite
- Recovery end-to-end

#### ⚡ Performance Tests
Test per verificare le performance:
- Throughput delle transazioni
- Latenza delle operazioni
- Utilizzo della memoria
- Scalabilità del sistema

#### 🎯 Stress Tests
Test per condizioni estreme:
- Carico elevato di transazioni
- Pressione sulla memoria
- Concorrenza estrema
- Recovery sotto stress

## 🔧 Configurazione dei Test

### Ambiente di Test
I test utilizzano directory temporanee per:
- File di database
- Log WAL
- File di configurazione
- Dati di test

### Dati di Test
I test generano automaticamente:
- Definizioni di tabelle
- Righe di dati di esempio
- Query SQL di test
- Utenti e sessioni di autenticazione

### Metriche di Performance
I test misurano e verificano:
- Tempo di esecuzione delle operazioni
- Throughput (operazioni per secondo)
- Utilizzo della memoria
- Latenza delle operazioni

## 📈 Metriche e Benchmark

### Soglie di Performance
- **Transazioni**: > 100 TPS
- **Inserimenti**: > 1000 IPS
- **Letture**: > 5000 RPS
- **Aggiornamenti**: > 1000 UPS
- **Parsing SQL**: > 10000 QPS

### Test di Scalabilità
- Test con 1000-10000 operazioni
- Verifica della degradazione delle performance
- Test di concorrenza con 10-100 task simultanei

## 🛠️ Debugging e Troubleshooting

### Log dei Test
I test includono logging dettagliato per:
- Operazioni di database
- Errori e eccezioni
- Metriche di performance
- Stato del sistema

### Test di Error Handling
Ogni modulo include test per:
- Gestione degli errori
- Recovery da fallimenti
- Validazione degli input
- Stati di errore

## 📚 Documentazione dei Test

### Copertura dei Test
La suite copre:
- ✅ Tutti i moduli core
- ✅ Tutte le operazioni CRUD
- ✅ Tutti i livelli di isolamento
- ✅ Tutte le funzionalità di sicurezza
- ✅ Tutti i meccanismi di recovery
- ✅ Tutte le operazioni distribuite

### Invarianti Verificati
I test verificano invarianti importanti:
- **ACID Properties**: Atomicità, Consistenza, Isolamento, Durabilità
- **Buffer Pool**: Consistenza della cache, gestione delle pagine sporche
- **WAL**: Log-before-data, ordine dei record
- **B+Tree**: Ordinamento delle chiavi, bilanciamento dell'albero
- **Transazioni**: Gestione dei lock, rilevamento deadlock

## 🔄 Continuous Integration

### Automazione
I test sono progettati per:
- Esecuzione automatica in CI/CD
- Generazione di report di coverage
- Notifiche per test falliti
- Metriche di performance

### Qualità del Codice
I test verificano:
- Correttezza funzionale
- Performance accettabili
- Gestione degli errori
- Robustezza del sistema

## 📝 Contribuire ai Test

### Aggiungere Nuovi Test
1. Seguire la struttura esistente
2. Utilizzare `TestUtils` e `TestAssertions`
3. Includere test per errori e edge cases
4. Verificare invarianti importanti
5. Misurare performance quando appropriato

### Best Practices
- Test deterministici e riproducibili
- Cleanup delle risorse temporanee
- Test isolati e indipendenti
- Nomi descrittivi per test e asserzioni
- Documentazione per test complessi

## 🎯 Obiettivi della Suite di Test

La suite di test ha l'obiettivo di:
1. **Verificare la correttezza** di tutti i moduli del sistema
2. **Garantire le performance** sotto vari carichi di lavoro
3. **Assicurare la robustezza** in condizioni di stress
4. **Validare la sicurezza** e l'autenticazione
5. **Testare la scalabilità** e la distribuzione
6. **Verificare il recovery** e la fault tolerance

Questa suite di test completa garantisce che ColibrìDB sia un database robusto, performante e affidabile per applicazioni di produzione.

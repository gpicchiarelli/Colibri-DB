# 🤝 Contribuire a ColibrDB

Grazie per il tuo interesse a contribuire a ColibrDB! Questo documento fornisce linee guida per contribuire efficacemente al progetto.

## 📋 Indice
- [Come Contribuire](#come-contribuire)
- [Setup di Sviluppo](#setup-di-sviluppo)
- [Convenzioni di Codice](#convenzioni-di-codice)
- [Processo di Pull Request](#processo-di-pull-request)
- [Testing](#testing)
- [Documentazione](#documentazione)
- [Architettura del Progetto](#architettura-del-progetto)

## 🚀 Come Contribuire

### Tipi di Contributi
- 🐛 **Bug Fixes**: Risoluzione di problemi esistenti
- ✨ **Nuove Features**: Implementazione di nuove funzionalità
- 📚 **Documentazione**: Miglioramento della documentazione
- 🧪 **Test**: Aggiunta di test e miglioramento della copertura
- ⚡ **Performance**: Ottimizzazioni e miglioramenti delle performance
- 🔧 **Refactoring**: Miglioramento del codice esistente

### Prima di Iniziare
1. Controlla le [issue esistenti](https://github.com/gpicchiarelli/Colibr-DB/issues)
2. Assicurati che la tua idea non sia già in discussione
3. Per feature importanti, apri prima una issue per discussione

## 🛠️ Setup di Sviluppo

### Prerequisiti
- **macOS 13+** (Apple Silicon consigliato)
- **Swift 6.2** o superiore
- **Xcode 15+** (opzionale, per debugging)
- **Git** per version control

### Installazione
```bash
# 1. Fork del repository su GitHub
# 2. Clona il tuo fork
git clone https://github.com/[TUO-USERNAME]/Colibr-DB.git
cd Colibr-DB

# 3. Aggiungi il repository originale come upstream
git remote add upstream https://github.com/gpicchiarelli/Colibr-DB.git

# 4. Installa le dipendenze
swift package resolve

# 5. Compila il progetto
swift build

# 6. Esegui i test
swift test
```

### Struttura del Progetto
```
Colibr-DB/
├── Sources/
│   ├── ColibriCore/          # Motore database core
│   │   ├── Buffer/           # Gestione buffer pool
│   │   ├── Catalog/          # Catalogo di sistema
│   │   ├── Database/         # Operazioni database
│   │   ├── Index/            # Implementazioni indici
│   │   ├── Storage/          # Motore storage
│   │   ├── Transactions/     # MVCC e locking
│   │   └── WAL/              # Write-Ahead Logging
│   ├── coldb/                # CLI amministrativa
│   ├── coldb-server/         # Server di rete
│   └── benchmarks/           # Test di performance
├── Tests/                    # Suite di test
├── docs/                     # Documentazione tecnica
└── Examples/                 # Esempi di utilizzo
```

## 📝 Convenzioni di Codice

### Swift Style Guide
- **Swift 6.2** con strict concurrency
- **Naming**: camelCase per variabili, PascalCase per tipi
- **Documentazione**: Header comment per ogni file pubblico
- **Indentazione**: 4 spazi (no tab)
- **Line Length**: Massimo 120 caratteri

### Esempio di Struttura File
```swift
//
//  NomeFile.swift
//  ColibrDB
//
//  Created by [Nome] on [Data].
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: [Descrizione breve del modulo]

import Foundation

/// Descrizione della classe/funzione
public final class NomeClasse {
    // MARK: - Properties
    
    /// Descrizione della proprietà
    public let proprieta: Tipo
    
    // MARK: - Initialization
    
    /// Inizializzatore
    public init(proprieta: Tipo) {
        self.proprieta = proprieta
    }
    
    // MARK: - Public Methods
    
    /// Descrizione del metodo
    public func metodo() {
        // Implementazione
    }
}
```

### Convenzioni Specifiche ColibrDB
- **Performance First**: Ogni componente deve essere ottimizzato per velocità
- **Thread Safety**: Usare `NSLock` o strutture lock-free per concorrenza
- **Memory Management**: Evitare retain cycles e memory leak
- **Error Handling**: Usare `Result<T, Error>` per operazioni che possono fallire
- **Logging**: Usare il sistema di logging centralizzato

## 🔄 Processo di Pull Request

### 1. Creazione del Branch
```bash
# Crea un nuovo branch per la tua feature
git checkout -b feature/nome-feature
# oppure
git checkout -b bugfix/nome-bug
```

### 2. Sviluppo
- Implementa le modifiche seguendo le convenzioni
- Aggiungi test per le nuove funzionalità
- Aggiorna la documentazione se necessario
- Esegui tutti i test localmente

### 3. Commit
```bash
# Aggiungi i file modificati
git add .

# Crea un commit descrittivo
git commit -m "feat: aggiungi supporto per [descrizione]"
# oppure
git commit -m "fix: risolvi problema con [descrizione]"
```

### Convenzioni Commit
- `feat:` - Nuova feature
- `fix:` - Bug fix
- `docs:` - Documentazione
- `test:` - Test
- `refactor:` - Refactoring
- `perf:` - Performance
- `chore:` - Manutenzione

### 4. Push e Pull Request
```bash
# Push del branch
git push origin feature/nome-feature

# Crea una Pull Request su GitHub
```

### Template Pull Request
Usa il template fornito in `.github/PULL_REQUEST_TEMPLATE.md` per creare PR complete e ben strutturate.

## 🧪 Testing

### Esecuzione Test
```bash
# Tutti i test
swift test

# Test specifici per modulo
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Test con verbose output
swift test --verbose
```

### Tipi di Test
- **Unit Tests**: Test di singole funzioni e classi
- **Integration Tests**: Test di workflow end-to-end
- **Performance Tests**: Benchmark per rilevare regressioni
- **Stress Tests**: Test con carico elevato

### Aggiungere Nuovi Test
```swift
import Testing

struct NomeModuloTests {
    @Test func testFunzionalita() async throws {
        // Arrange
        let input = "test"
        
        // Act
        let result = await funzione(input)
        
        // Assert
        #expect(result == "expected")
    }
}
```

### Benchmark
```bash
# Esegui benchmark
swift run benchmarks --help

# Benchmark specifici
swift run benchmarks --wal-throughput
swift run benchmarks --btree-lookups
```

## 📚 Documentazione

### Tipi di Documentazione
- **API Documentation**: Commenti nel codice per funzioni pubbliche
- **Technical Docs**: Documentazione in `docs/`
- **README**: Aggiornamenti al README principale
- **Examples**: Esempi di utilizzo in `Examples/`

### Aggiornare Documentazione
1. **API Changes**: Aggiorna commenti nel codice
2. **New Features**: Aggiungi sezioni al README
3. **Architecture Changes**: Aggiorna documentazione in `docs/`
4. **Examples**: Aggiungi esempi per nuove funzionalità

## 🏗️ Architettura del Progetto

### Principi Architetturali
- **Modularità**: Componenti indipendenti e pluggabili
- **Performance**: Ottimizzazione per velocità e throughput
- **Concorrenza**: Supporto multi-threading con MVCC
- **Durabilità**: WAL e recovery ARIES-compliant
- **Scalabilità**: Progettato per milioni di connessioni

### Moduli Core
- **Storage Engine**: Heap file con slot directory
- **Buffer Pool**: Eviction LRU/Clock con flush in background
- **WAL**: Write-Ahead Logging con recovery ARIES-compliant
- **Index Engine**: B+Tree, Hash, ART, LSM pluggabili
- **MVCC**: Multi-Version Concurrency Control
- **Catalog**: Gestione metadati e schema
- **Query Processor**: Iterator Volcano con ottimizzazione cost-based

### Aree per Contributi
- **Core Engine**: Storage, WAL, Buffer Pool
- **Indexing**: Nuovi tipi di indici, ottimizzazioni
- **Query Processing**: Parser SQL, ottimizzatore
- **Concurrency**: MVCC, locking, deadlock detection
- **Testing**: Copertura test, benchmark
- **Documentation**: Guide, esempi, API docs
- **Tooling**: CLI, monitoring, debugging

## 🎯 Aree di Focus

### Priorità Alta
- Stabilizzazione del core WAL e recovery
- Completamento del parser SQL
- Miglioramento della copertura test
- Ottimizzazioni performance

### Priorità Media
- Nuovi tipi di indici (Hash, Bitmap)
- Supporto per transazioni distribuite
- Miglioramenti alla CLI
- Strumenti di monitoring

### Priorità Bassa
- Features avanzate di analytics
- Supporto per più piattaforme
- Integrazione con tool esterni

## 🐛 Reporting Bug

### Prima di Segnalare
1. Verifica che il bug non sia già stato segnalato
2. Controlla la documentazione e le FAQ
3. Prova con la versione più recente

### Come Segnalare
1. Usa il template in `.github/ISSUE_TEMPLATE/bug_report.md`
2. Fornisci informazioni dettagliate sull'ambiente
3. Includi passi per riprodurre il bug
4. Aggiungi log e output di errore

## 💬 Discussioni

- **GitHub Discussions**: Per domande generali e discussioni
- **Issues**: Per bug e feature requests
- **Pull Requests**: Per discussioni su codice specifico

## 📄 Licenza

Contribuendo a ColibrDB, accetti che le tue modifiche saranno licenziate sotto la [Licenza BSD 3-Clause](LICENSE).

## 🙏 Riconoscimenti

Grazie a tutti i contributori che rendono ColibrDB possibile! I tuoi contributi sono apprezzati e aiutano a costruire un database migliore per tutti.

---

**Hai domande?** Apri una [discussione](https://github.com/gpicchiarelli/Colibr-DB/discussions) o contatta il team di sviluppo!

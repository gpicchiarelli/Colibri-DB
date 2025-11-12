
# Contribuire a ColibrìDB

Grazie per il tuo interesse a contribuire a ColibrìDB! Questo documento fornisce linee guida complete per contribuire al progetto.

## 🎯 Panoramica

ColibrìDB è un database relazionale formalmente verificato implementato in Swift 6.0. Il progetto combina rigorosità accademica con implementazione pratica, utilizzando TLA+ per la verifica formale e Swift actors per la concorrenza sicura.

## 🚀 Quick Start

### Prerequisiti

- **macOS 13+** (Apple Silicon consigliato per performance ottimali)
- **Swift 6.0** (o toolchain compatibile)
- **Xcode 15+** (per sviluppo e debugging)
- **TLA+ Tools** (opzionale, per verifiche formali)
- **Git** (per version control)

### Setup Sviluppo

```bash
# 1. Fork del repository su GitHub
# 2. Clona il tuo fork
git clone https://github.com/your-username/Colibri-DB.git
cd Colibri-DB

# 3. Aggiungi upstream remote
git remote add upstream https://github.com/gpicchiarelli/Colibri-DB.git

# 4. Installa dipendenze
swift package resolve

# 5. Build del progetto
swift build

# 6. Esegui test
swift test

# 7. Esegui formattazione
make format

# 8. Esegui linting
make lint
```

## 📋 Processo di Contribuzione

### 1. Creazione Issue

Prima di iniziare a lavorare su una feature o fix:

1. **Verifica** che non esista già un'issue simile
2. **Crea** una nuova issue con:
   - Titolo descrittivo
   - Descrizione dettagliata del problema/feature
   - Label appropriata (`bug`, `enhancement`, `documentation`, etc.)
   - Priorità se applicabile

### 2. Setup Branch

```bash
# Aggiorna main branch
git checkout main
git pull upstream main

# Crea nuovo branch
git checkout -b feature/your-feature-name
# oppure
git checkout -b fix/your-bug-description
```

### 3. Sviluppo

#### Linee Guida Codice

- **Swift 6.0**: Usa le funzionalità più recenti del linguaggio
- **Actor Model**: Usa actors per concorrenza sicura
- **Async/Await**: Preferisci async/await su callback
- **Error Handling**: Usa `Result` types e `throws` appropriatamente
- **Documentation**: Documenta tutte le API pubbliche

#### Esempio Struttura

```swift
/// TLA+ Action: ActionName == /\ precondition /\ state' = newState
public func actionName() async throws {
    // Guard su precondizioni
    guard precondition else {
        throw DBError.invalidState
    }
    
    // Applica modifiche stato
    state = newState
    
    // Verifica invarianti
    try assertInvariants()
}

/// TLA+ Invariant: Inv_Module_Property
private func assertInvariants() throws {
    // Implementazione invariante
    assert(property, "Invariant violated: description")
}
```

#### TLA+ Conformità

Ogni modulo deve essere conforme alla specifica TLA+:

1. **Variabili di stato** mappate correttamente
2. **Azioni TLA+** implementate come metodi Swift
3. **Invarianti** implementate come assertion methods
4. **Commenti** che referenziano la specifica TLA+

### 4. Testing

#### Test Obbligatori

```bash
# Test unitari
swift test --filter ModuleName

# Test integrazione
swift test --filter Integration

# Test performance
swift run benchmarks --module ModuleName

# Test chaos engineering
swift run chaos-engineering --module ModuleName
```

#### Coverage Requirements

- **Moduli critici**: 100% coverage
- **Moduli standard**: 90%+ coverage
- **Nuovi moduli**: 95%+ coverage

### 5. Documentazione

#### Aggiornamenti Richiesti

- **API Reference**: Per nuove API pubbliche
- **README**: Per nuove funzionalità significative
- **Wiki**: Per guide e tutorial
- **TLA+ Specs**: Per nuovi moduli

#### Esempio Documentazione

```swift
/// Gestisce la concorrenza multi-versione per transazioni.
/// 
/// Implementa snapshot isolation come descritto in:
/// - Berenson et al. (1995) "A Critique of ANSI SQL Isolation Levels"
/// - TLA+ Specification: `spec/MVCC.tla`
/// 
/// ## Invarianti TLA+
/// - Inv_MVCC_ReadStability: Read stability per snapshot
/// - Inv_MVCC_WriteWriteConflict: Rilevamento write-write conflicts
/// 
/// ## Esempio
/// ```swift
/// let mvcc = MVCCManager()
/// try await mvcc.begin(tid: 1)
/// let value = try await mvcc.read(tid: 1, key: "data")
/// try await mvcc.write(tid: 1, key: "data", value: .string("new"))
/// try await mvcc.commit(tid: 1)
/// ```
public actor MVCCManager {
    // Implementazione...
}
```

### 6. Code Review

#### Pre-commit Checklist

- [ ] Codice compila senza errori
- [ ] Tutti i test passano
- [ ] Coverage requirements soddisfatti
- [ ] Formattazione applicata (`make format`)
- [ ] Linting passato (`make lint`)
- [ ] Documentazione aggiornata
- [ ] TLA+ conformità verificata
- [ ] Commit message segue convenzioni

#### Commit Messages

Usa [Conventional Commits](https://www.conventionalcommits.org/):

```
feat: aggiungi supporto window functions
fix: risolvi deadlock in LockManager
docs: aggiorna API reference per MVCC
test: aggiungi test per chaos engineering
refactor: ottimizza BufferPool eviction
```

### 7. Pull Request

#### Template PR

```markdown
## Descrizione
Breve descrizione delle modifiche.

## Tipo di Cambiamento
- [ ] Bug fix
- [ ] Nuova feature
- [ ] Breaking change
- [ ] Documentazione
- [ ] Test

## TLA+ Conformità
- [ ] Specifica TLA+ aggiornata (se applicabile)
- [ ] Invarianti implementati
- [ ] Model checking passato

## Testing
- [ ] Test unitari aggiunti/aggiornati
- [ ] Test integrazione passati
- [ ] Performance test passati
- [ ] Chaos engineering test passati

## Documentazione
- [ ] API reference aggiornata
- [ ] README aggiornato
- [ ] Wiki aggiornata (se applicabile)

## Checklist
- [ ] Codice compila
- [ ] Test passano
- [ ] Coverage soddisfatto
- [ ] Formattazione applicata
- [ ] Linting passato
```

## 🏗️ Architettura e Design

### Principi Fondamentali

1. **Verifica Formale**: Ogni componente critico ha specifica TLA+
2. **Concorrenza Sicura**: Swift actors per zero data races
3. **Performance**: Ottimizzazioni per database ad alte prestazioni
4. **Sicurezza**: Modelli di sicurezza multipli
5. **Manutenibilità**: Codice pulito e ben documentato

### Struttura Progetto

```
Colibri-DB/
├── Sources/
│   ├── ColibriCore/          # Motore database core
│   │   ├── Core/             # Tipi fondamentali
│   │   ├── WAL/              # Write-Ahead Logging
│   │   ├── MVCC/             # Multi-Version Concurrency Control
│   │   ├── Transaction/      # Gestione transazioni
│   │   ├── BufferPool/       # Buffer pool management
│   │   ├── Recovery/         # Crash recovery
│   │   ├── Indexes/          # Gestione indici
│   │   ├── Storage/          # Storage engine
│   │   ├── SQL/              # Query processing
│   │   ├── Security/         # Sicurezza e autorizzazione
│   │   └── Distributed/      # Sistemi distribuiti
│   ├── coldb/                # CLI amministrativa
│   ├── coldb-server/         # Server di rete
│   └── benchmarks/           # Test di performance
├── Tests/                    # Suite di test
├── spec/                     # Specifiche TLA+
├── docs/                     # Documentazione
└── tools/                    # Strumenti di sviluppo
```

## 🧪 Testing

### Tipi di Test

#### Unit Tests
```bash
swift test --filter Unit
```

#### Integration Tests
```bash
swift test --filter Integration
```

#### Performance Tests
```bash
swift run benchmarks --help
```

#### Chaos Engineering
```bash
swift run chaos-engineering --help
```

### Coverage

```bash
# Genera report coverage
swift test --enable-code-coverage
xcrun llvm-cov show .build/debug/ColibriCorePackageTests.xctest/Contents/MacOS/ColibriCorePackageTests -instr-profile .build/debug/codecov/default.profdata
```

## 🔧 Strumenti di Sviluppo

### Formattazione

```bash
# Formatta tutto il codice
make format

# Formatta file specifico
swiftformat Sources/ColibriCore/Module/File.swift
```

### Linting

```bash
# Lint tutto il codice
make lint

# Lint file specifico
swiftlint Sources/ColibriCore/Module/File.swift
```

### TLA+ Verification

```bash
# Verifica specifica TLA+
tlc spec/Module.tla

# Verifica con configurazione
tlc -config spec/Module.cfg spec/Module.tla
```

## 📚 Documentazione

### Generazione Documentazione

```bash
# Genera documentazione API
swift package generate-documentation

# Serve documentazione localmente
swift package --disable-sandbox preview-documentation
```

### Aggiornamento Wiki

La documentazione si trova in `docs/`. Per aggiornamenti:

1. Modifica i file HTML appropriati nella directory `docs/`
2. Testa la formattazione localmente
3. Invia PR con le modifiche

## 🐛 Bug Reports

### Template Bug Report

```markdown
## Descrizione
Descrizione chiara e concisa del bug.

## Riproduzione
Passi per riprodurre il comportamento:
1. Vai a '...'
2. Clicca su '...'
3. Scorri fino a '...'
4. Vedi errore

## Comportamento Atteso
Descrizione chiara e concisa di cosa ti aspettavi.

## Screenshots
Se applicabile, aggiungi screenshot.

## Ambiente
- OS: [e.g. macOS 13.0]
- Swift: [e.g. 6.0]
- Versione: [e.g. 1.0.0]

## Log
Se applicabile, aggiungi log di errore.

## Contesto Aggiuntivo
Aggiungi qualsiasi altro contesto sul problema.
```

## 💡 Feature Requests

### Template Feature Request

```markdown
## Descrizione
Descrizione chiara e concisa della feature richiesta.

## Problema
Quale problema risolve questa feature?

## Soluzione Proposta
Descrizione chiara e concisa della soluzione che vorresti.

## Alternative Considerate
Descrizione di soluzioni alternative considerate.

## Contesto Aggiuntivo
Aggiungi qualsiasi altro contesto o screenshot.
```

## 🤝 Code of Conduct

### I Nostri Impegni

- Mantenere un ambiente accogliente e inclusivo
- Rispettare tutti i contributori
- Accogliere feedback costruttivo
- Concentrarsi su ciò che è meglio per la comunità

### Comportamenti Accettabili

- Uso di linguaggio inclusivo
- Rispetto per opinioni diverse
- Accettazione di critiche costruttive
- Concentrazione sul bene comune

### Comportamenti Inaccettabili

- Linguaggio o immagini sessualizzati
- Trolling, commenti offensivi o dispregiativi
- Molestie pubbliche o private
- Pubblicazione di informazioni private

## 📞 Supporto

### Canali di Supporto

- **GitHub Issues**: Per bug e feature requests
- **GitHub Discussions**: Per domande e discussioni
- **Email**: [maintainer@example.com]
- **Documentation**: [docs/](docs/)

### Risposta Times

- **Bug critici**: 24-48 ore
- **Feature requests**: 1-2 settimane
- **Domande generali**: 3-5 giorni
- **Documentation**: 1 settimana

## 🏆 Riconoscimenti

### Contributori

Tutti i contributori sono riconosciuti in:
- [AUTHORS.md](AUTHORS.md)
- GitHub contributors page
- Release notes

### Tipi di Contributi

- **Code**: Implementazione features e bug fixes
- **Documentation**: Guide, tutorial, API reference
- **Testing**: Test cases, bug reports, performance testing
- **Design**: Architettura, UX, UI
- **Community**: Supporto, mentoring, organizzazione

## 📄 Licenza

Contribuendo a ColibrìDB, accetti che le tue modifiche siano rilasciate sotto la [Licenza BSD 3-Clause](LICENSE).

## 🙏 Grazie

Grazie per il tuo interesse a contribuire a ColibrìDB! Ogni contributo, grande o piccolo, aiuta a rendere il progetto migliore per tutti.

---

## Development Environment

### Prerequisites
- macOS 13+
- Swift 6.0+
- Xcode 15+ (recommended)

### Local Build and Test

```bash
# Build the project
swift build

# Run tests
swift test

# Run benchmarks
swift run benchmarks
```

## Code Style

- **Swift 6**: Use modern Swift features, protocol-first design, typed errors
- **Focused Changes**: Keep changes focused and small
- **Documentation**: Update documentation (`docs/`) when modifying behaviors or APIs
- **Code Quality**: Run `swiftformat` and `swiftlint` with profiles in `Configuration/` before opening a PR

```bash
# Format code
swiftformat .

# Lint code
swiftlint
```

## Commit and PR Guidelines

### Commit Messages
- Use clear, descriptive titles
- Prefer [Conventional Commits](https://www.conventionalcommits.org/) format:
  - `feat:` for new features
  - `fix:` for bug fixes
  - `docs:` for documentation changes
  - `style:` for formatting changes
  - `refactor:` for code refactoring
  - `test:` for test additions/changes
  - `chore:` for maintenance tasks

### Pull Requests
- Associate PRs with issues when possible
- Provide comprehensive descriptions
- Include tests for new functionality
- Ensure all tests pass before submitting

## Development Workflow

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes
4. Run tests and linting
5. Commit your changes with conventional commit format
6. Push to your fork (`git push origin feature/amazing-feature`)
7. Open a Pull Request

## License

By contributing, you agree that your contributions will be licensed under the BSD 3-Clause License.

## Questions?

Feel free to open an issue for questions or discussions about the project.

**ColibrìDB Contributing Guidelines** - v1.0.0  
*Ultimo aggiornamento: 2025-10-19*
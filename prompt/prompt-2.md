# Linee guida per un agente AI nella scrittura della documentazione tecnica di ColibrìDB

## Obiettivo
Questo documento specifica come un **agente AI** deve procedere nella redazione della **documentazione tecnica completa** del progetto **ColibrìDB** (RDBMS scritto in Swift 6).  
La documentazione deve essere **chiara, completa, modulare**, e indirizzata a sviluppatori, architetti software, e potenziali utenti tecnici.

---

## Principi generali
1. **Accuratezza**: ogni parte della documentazione deve riflettere fedelmente le specifiche di ColibrìDB.  
2. **Completezza**: coprire tutti i moduli (Storage, WAL, Buffer Pool, Concurrency, CLI `coldb`, sicurezza, import/export, ecc.).  
3. **Struttura modulare**: organizzare la documentazione in sezioni indipendenti ma collegate.  
4. **Chiarezza e semplicità**: linguaggio tecnico ma leggibile, spiegazioni esaurienti con esempi.  
5. **Coerenza**: usare terminologia uniforme (es. “Executor modello Volcano”, “MVCC”, “coldb”).  
6. **Multi‑livello**: prevedere un livello introduttivo (overview) e livelli dettagliati (API, algoritmi, formati file).  

---

## Struttura della documentazione

### 1. Introduzione generale
- Visione del progetto e obiettivi (milioni di connessioni, ottimizzazione Apple Silicon, sicurezza).  
- Breve descrizione di ColibrìDB e della CLI `coldb`.  
- Filosofia progettuale (protocol‑first, sicurezza, modularità, performance).

### 2. Architettura
- Diagramma a blocchi: Storage Engine, Planner, Executor, Concurrency, CLI.  
- Descrizione strati e interfacce principali.  
- Spiegazione modello di esecuzione (Volcano).  
- Opzioni paradigmatiche (relazionale, grafi, documenti).

### 3. Moduli core
- **Storage Engine**: file layout, pagine, record, catalogo.  
- **WAL & Recovery**: principi, flusso write‑ahead, checkpoint, redo/undo.  
- **Buffer Pool**: caching, politiche di eviction.  
- **Transazioni & Concorrenza**: lock manager, MVCC, isolamento, deadlock detection.  
- **Indici & Strutture dati pluggabili**: Hash, B+Tree, estensioni custom.  
- **Sicurezza**: cifratura, autenticazione, audit, conformità.  

### 4. Ottimizzazioni Apple Silicon & APFS
- Uso di P‑cores/E‑cores.  
- Snapshot APFS per backup.  
- Istruzioni CRC32 hardware.  
- Integrazione con strumenti Apple (os_log, Instruments).

### 5. CLI `coldb`
- Modalità interattiva e batch.  
- Elenco comandi (\help, \dt, \export, \import, ecc.).  
- Esempi di sessioni reali.  
- Sicurezza CLI (autenticazione, audit log).

### 6. Import/Export
- CSV, JSON, BSON: mapping tipi dati.  
- Comandi CLI e API.  
- Esempi di import/export.  
- Considerazioni di sicurezza sui file.

### 7. Configurazione
- File `colibridb.conf` (YAML/JSON).  
- Parametri principali (maxConnections, bufferPoolSize, pageSize).  
- Override con variabili ambiente e flag CLI.

### 8. API & Estendibilità
- Protocolli Swift (StorageEngine, IndexProtocol, TableStorageProtocol).  
- Come implementare nuove strutture dati.  
- Come estendere la CLI con nuovi comandi.  
- Integrazione driver Swift con Codable e async/await.

### 9. Roadmap
- Indici B+Tree avanzati.  
- Query parallele.  
- Replica e sharding.  
- JSON nativo.  
- Alta disponibilità (Raft/Paxos).

### 10. Glossario
- MVCC, WAL, Volcano, Multiplexing, ecc.

### 11. Appendici
- Esempi di file binari (pagina, WAL record).  
- Diagrammi di sequenza (commit, recovery, checkpoint).  
- Benchmark preliminari.  
- Linee guida contributori.

---

## Stile e formattazione
- Usare Markdown per la documentazione.  
- Evidenziare codice Swift con blocchi ```swift.  
- Diagrammi: ASCII art o mermaid.js.  
- Tabelle per mapping tipi (es. SQL ↔ JSON/BSON).  
- Note di sicurezza evidenziate (⚠️).  

---

## Processo di generazione della documentazione
1. **Raccolta specifiche** → estrarre requisiti dai documenti ufficiali (come questo).  
2. **Strutturazione** → mappare requisiti nelle sezioni sopra elencate.  
3. **Espansione** → dettagliare ogni parte con descrizioni, esempi, diagrammi.  
4. **Revisione automatica** → verificare consistenza terminologica e completezza.  
5. **Output** → produrre file `.md` multipli (una sezione per file) o un manuale unico.  
6. **Aggiornamento iterativo** → mantenere sincronizzata la documentazione con l’evoluzione del progetto.

---

## Deliverable finali
- **Manuale sviluppatori**: dettagli interni, API, protocolli, formati file.  
- **Manuale utenti CLI**: guida a `coldb`.  
- **Manuale amministratori**: sicurezza, backup, recovery, tuning.  
- **Manuale estensibilità**: come creare nuovi indici, moduli, protocolli.

---

## Criteri di accettazione
- Documentazione copre tutti i moduli e funzionalità di ColibrìDB.  
- È scritta in stile chiaro, tecnico ma leggibile.  
- Include esempi pratici, diagrammi e tabelle.  
- Può essere usata sia per sviluppo sia per operatività.  
- Aggiornabile facilmente dall’agente AI con nuove sezioni.


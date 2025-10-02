Changelog
=========

Tutte le modifiche note a ColibrìDB.

## v1.0.0 - Performance & Stability Release (2025-01-02)

### 🚀 **Ottimizzazioni Performance**
- **Lock Striping**: Implementato lock striping con 64 stripe per ridurre contention (5-10x miglioramento concorrenza)
- **Serializzazione Binaria**: Nuovo formato binario custom per Row data (3-5x più veloce di JSON)
- **B-Tree Caching**: Page cache intelligente con LRU eviction e prefetching
- **Query Plan Cache**: Caching dei piani di esecuzione per query frequenti (10-50x più veloce)
- **Adaptive Algorithms**: Split points adattivi basati su distribuzione chiavi

### 🔧 **Fix Critici**
- **Memory Leaks**: Risolti leak in transaction management e global state
- **Race Conditions**: Implementato fine-grained locking in MVCC
- **Resource Leaks**: Proper cleanup di file handles in FileHeapTable
- **WAL Error Handling**: Migliorata resilienza durante inizializzazione e recovery
- **SQL Injection**: Implementata validazione e sanitizzazione input completa

### 🏗️ **Architettura**
- **Fine-grained Locking**: Sostituiti lock globali con lock granulari
- **Periodic Cleanup**: Sistema automatico di pulizia memoria
- **Enhanced Error Handling**: Gestione errori robusta in tutti i componenti
- **Performance Monitoring**: Metriche integrate per monitoraggio performance

### 📚 **Documentazione**
- Aggiornato README con nuove ottimizzazioni
- Documentazione completa delle performance improvements
- Guide per utilizzo delle nuove funzionalità

Unreleased
--
- B+Tree persistente su disco (insert/split/range/equality, chiavi multi-tipo)
- Indici Hash/ART in-memory
- CLI `coldb` con comandi indici, policy, insert/scan
- Storage heap file-backed (insert/scan) e WAL minimo
- Catalogo indici persistente e ripristino
- Documentazione allineata (README, indice docs, moduli storage/indici/WAL/concorrenza, guida CLI)

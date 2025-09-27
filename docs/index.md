# Documentazione ColibrìDB

Questo indice riunisce i documenti tecnici mantenuti in `docs/` e suggerisce un percorso di lettura per comprendere il motore ColibrìDB.

## Percorso consigliato
1. **Panoramica generale** — `docs/overview.md`
2. **Architettura** — `docs/architecture.md`
3. **Componenti principali** — serie `docs/modules-*.md`
4. **Operazioni & configurazione** — `docs/cli.md`, `docs/configuration.md`, `docs/policies.md`
5. **Approfondimenti trasversali** — `docs/security.md`, `docs/apple-silicon.md`, `docs/appendices.md`
6. **Roadmap e piani futuri** — `docs/roadmap.md`

## Documenti di riferimento
- `overview.md` — Visione, stato MVP, riepilogo componenti.
- `architecture.md` — Strati logici, flussi dati, dipendenze.
- `modules-storage.md` — Heap file, FSM, compattazione, interazione MVCC.
- `modules-buffer-pool.md` — Politiche LRU/Clock/LRU2, quote, flusher.
- `modules-indexes.md` — Indici in-memory e persistenti (Hash, ART, SkipList, LSM, B+Tree).
- `modules-wal.md` — WAL DB e indici, record, checkpoint, recovery.
- `modules-concurrency.md` — MVCC, lock manager, serializzazione, vacuum.
- `cli.md` — Comandi `coldb`, metriche e script.
- `configuration.md` — Parametri del file `colibridb.conf.json`.
- `policies.md` — Politiche di manutenzione/ottimizzazione e simulatore.
- `import-export.md` — Import/export CSV oggi, roadmap JSON/BSON.
- `security.md` — Integrità, durabilità, cifratura in roadmap.
- `apple-silicon.md` — Ottimizzazioni specifiche per Apple Silicon/APFS.
- `appendices.md` — Layout pagine, sequenze operative, materiale ausiliario.
- `api-extendibility.md` — Punti di estensione per storage/indici/CLI.
- `glossary.md` — Terminologia chiave.
- `roadmap.md` — Milestone organizzate per orizzonte temporale.
- `dimensional-limits.md` — Limiti dimensionali (pagine, slot, buffer, WAL, identificatori).
- `performance.md` — Pianificazione performance, benchmark e strumenti di profiling.

## Stato della documentazione
Tutti i file sono allineati al codice al commit corrente. Ogni documento indica cosa è già disponibile nell'MVP e cosa resta nella roadmap. Aggiornare `docs/index.md` quando si aggiungono nuovi materiali.

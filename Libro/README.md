Libro degli Internals di ColibrìDB
==================================

Questo libro descrive gli internals del motore: architettura, sottosistemi (SQL, planner/executor, transazioni/MVCC, storage, buffer pool, WAL, indici), server e CLI. È scritto interamente in Markdown per una fruizione diretta su GitHub.

Come leggere
------------
- Inizia da "02 Architettura" per una vista d'insieme.
- Approfondisci i capitoli tematici in base all'interesse (es. `06 Storage (Heap)` o `05 Transazioni & MVCC`).
- Ogni capitolo rimanda ai file sorgenti e ai documenti tecnici in `docs/`.

Struttura
---------
Il sommario è in `SUMMARY.md`. I capitoli sono numerati per facilitare i riferimenti nelle issue/PR.

Integrazione con GitHub
-----------------------
- Nessun tool di build richiesto: i file `.md` sono navigabili direttamente su GitHub.
- Per GitHub Pages puoi pubblicare la directory `Libro/` come sorgente del sito impostando Pages su branch `main` e cartella `/(root)` o copiando `Libro/` sotto `docs/` (opzione classica Pages). In alternativa usa un generatore (MkDocs, mdBook, GitBook) puntando a questi markdown.

Contribuire
-----------
- Ogni capitolo ha una sezione finale "Verifiche e test" con casi d'uso e file di riferimento.
- Mantieni coerenza tra esempi e API correnti; cita file e simboli del codice quando utile.

Riferimenti rapidi
------------------
- Documentazione tecnica: `docs/`
- Codice sorgente core: `Sources/ColibriCore/`
- CLI: `Sources/coldb/`
- Server: `Sources/coldb-server/`


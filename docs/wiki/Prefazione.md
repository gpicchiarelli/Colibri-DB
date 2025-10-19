---
layout: page
title: Prefazione
description: Prefazione alla documentazione Colibrì DB
---

# Prefazione

Colibrì DB nasce come esperimento ingegneristico volto a dimostrare che un motore relazionale moderno può essere costruito con rigore formale mantenendo un codice sorgente leggibile. Questo manuale costituisce il ponte fra teoria e implementazione: ogni sezione illustra i concetti classici dei sistemi di gestione di basi di dati e li mette in relazione diretta con le funzioni reali presenti nella codebase Swift.

## Obiettivi didattici
1. **Comprensione sistemica** — Fornire una visione coerente dell'intero stack, dal modello relazionale al server SQL.
2. **Rigore scientifico** — Dimostrare le proprietà fondamentali (ACID, correttezza del logging, consistenza del catalogo) attraverso analisi formali e ispezione del codice.
3. **Riproducibilità** — Ogni processo descritto è accompagnato da istruzioni per replicare esperimenti (esecuzione di test, benchmark, scenari di failure/recovery).

## Metodo
dsegniamo un percorso progressivo:
- Introduciamo il principio teorico mediante definizioni, teoremi o leggi empiriche tratte dalla letteratura (es. Codd, Gray & Reuter, Bernstein & Newcomer).
- Isoliamo il corrispettivo implementativo individuando il file, la funzione e le strutture dati coinvolte.
- Analizziamo la funzione riga per riga descrivendo precondizioni, invarianti, complessità, effetti collaterali e casi limite.
- Concludiamo con esercizi o esperimenti guidati che permettono di osservare il comportamento nel sistema reale.

## Come leggere il manuale
- **Parti I–II**: introducono le basi teoriche e il nucleo del motore (WAL, storage, concorrenza).
- **Parti III–IV**: descrivono la pipeline delle query e il sistema dei metadati, essenziali per comprendere l'ottimizzazione.
- **Parti V–VI**: illustrano l'infrastruttura server e gli strumenti di amministrazione e sviluppo.
- **Parte VII**: fornisce metodi per verificare empiricamente gli invarianti tramite test e benchmark.
- **Parte VIII e Appendici**: delineano la roadmap e fungono da riferimento rapido.

Ogni capitolo riporta sistematicamente riferimenti incrociati al codice sorgente (es. `Database+GlobalWALRecovery.swift`) e suggerisce esperimenti ripetibili. Il lettore è incoraggiato a tenere aperto l'editor e utilizzare i comandi `swift build`, `swift test`, `swift run` per seguire gli esempi mentre legge.

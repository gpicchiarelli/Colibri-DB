---
layout: page
title: Introduzione alla Parte II — Motore Core
description: Introduzione al motore core di ColibrìDB
---

# Introduzione alla Parte II — Motore Core

La Parte II costituisce il nucleo tecnico del manuale: qui dimostriamo come ColibrìDB implementa i meccanismi di persistenza, recovery, gestione della memoria e concorrenza. Ogni capitolo segue un'impostazione scientifica:

1. **Modello teorico**: richiamo al framework matematico (ad es. logica temporale per il WAL, teoria delle code per il buffer pool, algebra dei B+Tree).
2. **Derivazione implementativa**: analisi dettagliata delle funzioni Swift, con enunciazione di invarianti e complessità.
3. **Prove empiriche**: esperimenti da eseguire con la codebase per osservare il comportamento.

Gli argomenti trattati includono il Write-Ahead Logging (Cap. 5), la gestione delle pagine in memoria (Cap. 6), lo storage heap (Cap. 7), gli indici B+Tree (Cap. 8) e il sistema di concorrenza MVCC (Cap. 9).

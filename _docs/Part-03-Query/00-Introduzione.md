---
layout: page
title: Parte III — Pipeline di Query e Ottimizzazione
description: Pipeline di query e ottimizzazione in ColibrDB
---

# Parte III — Pipeline di Query e Ottimizzazione

Questa parte del manuale approfondisce l'intero ciclo di vita di una query SQL in ColibrDB. Analizzeremo:
1. **Parsing** — dalla stringa SQL all'albero sintattico astratto (AST).
2. **Pianificazione logica** — trasformazione dell'AST in un piano basato su operatori relazionali.
3. **Ottimizzazione** — applicazione di regole logiche e stime di costo.
4. **Pianificazione fisica** — scelta degli algoritmi concreti.
5. **Esecuzione** — pipeline iterator-based che materializza i risultati.

Ogni capitolo segue il tema: spiegazione teorica, analisi del codice (`SQLParser`, `LogicalPlanner`, `PhysicalPlanner`, `Executor`) ed esperimenti empirici.

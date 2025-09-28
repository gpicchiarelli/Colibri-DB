---
layout: page
title: Parte IV — Catalogo, Statistiche e Metadati
description: Catalogo, statistiche e metadati in ColibrDB
---

# Parte IV — Catalogo, Statistiche e Metadati

In questa parte descriviamo la struttura dati che memorizza la conoscenza del database su se stesso. L'obiettivo è comprendere come ColibrDB mantiene la consistenza dei metadati, fornisce statistiche per l'ottimizzatore e gestisce permessi/configurazioni.

Argomenti trattati:
- `SystemCatalog`: persistenza logica/fisica di tabelle, indici, ruoli.
- `CatalogManager`: API DDL ad alto livello.
- `StatisticsManager`: raccolta e utilizzo di statistiche per il planner.

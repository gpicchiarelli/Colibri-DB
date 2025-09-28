# Parte III — Pipelines di Query e Ottimizzazione

Questa parte illustra come ColibrìDB elabora le query SQL dal parsing all’esecuzione, con attenzione a pianificazione, ottimizzazione e runtime iterator-based. Ogni capitolo approfondirà:

- Strutture dati dell’AST e del piano logico.
- Conversione in piano fisico e operatori.
- Meccanismi di valutazione espressioni, aggregazioni e join.
- Collegamenti con statistiche catalogo e cost-based optimization.

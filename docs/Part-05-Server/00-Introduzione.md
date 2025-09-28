# Parte V — Server SQL, Networking e Wire Protocol

Questa parte analizza la componente server: dall’accettazione delle connessioni al protocollo di comunicazione, fino alla gestione delle sessioni e del planner remoto. Struttura:

- Diagrammi architetturali: processi, thread, code, sistemi I/O.
- Analisi file per file (`Sources/ColibriServer`, `Sources/coldb-server`).
- Descrizione dei comandi wire e delle risposte.
- Considerazioni su sicurezza, autenticazione, resilienza.

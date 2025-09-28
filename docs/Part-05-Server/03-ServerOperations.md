# Capitolo 20 — Operazioni Server, Fault Tolerance e Manutenzione

## 20.1 Configurazione
`ServerConfig` carica parametri da file JSON: porta, thread pool, durabilità, log. Analizziamo la struttura e le validazioni.

## 20.2 Gestione errori
Il server distingue errori di protocollo, SQL e runtime. `APIHandler` converte le eccezioni in risposte strutturate.

## 20.3 Fault tolerance
Grazie al WAL globale, un crash del server non perde dati committati. Spieghiamo come il server richiami `Database.replayGlobalWAL()` al riavvio.

## 20.4 Manutenzione
Il server espone comandi per checkpoint, vacuum, statistiche. Dettagliamo come vengono eseguiti (`db.checkpoint()`, `db.vacuum`).

## 20.5 Monitoraggio
Metriche: numero di connessioni, throughput, latenza. Discussione sui punti di integrazione con sistemi esterni.

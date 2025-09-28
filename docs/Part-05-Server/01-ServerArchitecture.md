# Capitolo 18 — Architettura del Server ColibrìDB

## 18.1 Panoramica
- Componenti principali: `coldb-server` (binario), `ColibriServer` (libreria), `ConnectionManager`.
- Diagramma dei thread: listener, worker pool, task asincroni.

## 18.2 Entry point
- `Sources/coldb-server/main.swift`: configurazione iniziale, parsing argomenti.
- Caricamento `ServerConfig` e bootstrap `ColibriServer`.

## 18.3 ConnectionManager
- File `Sources/coldb-server/ConnectionManager.swift`.
- Funzioni chiave: `start()`, `acceptLoop()`, `handle(client:)`.
- Gestione backpressure e limiti di connessione.

## 18.4 Logging e monitoring
- `Logger.swift`, `Logging.swift`.
- Integrazione con `Metrics` e `Telemetry`.

## 18.5 Scalabilità
- Strategia multi-core, dispatch queue, QoS.
- TODO: connessioni multiplexed, async/await.

---
layout: page
title: Architettura Server
description: Capitolo 10 - Architettura del server Colibrì DB
---

# Capitolo 18 — Architettura del Server Colibrì DB

> **Obiettivo**: descrivere la struttura del server SQL, includendo diagrammi dei componenti, flussi di controllo e strumenti di osservazione.

---

## 18.1 Panoramica dei componenti

| Componente | Responsabilità |
|------------|----------------|
| `coldb-server` (binario) | Entry point, parsing configurazione, avvio server |
| `ColibriServer` | Logica applicativa: sessioni, planner, executor |
| `ConnectionManager` | Networking, accettazione client, dispatch |
| `Logger`/`Telemetry` | Logging strutturato e metriche |

Diagramma architetturale:
```
[Client] ⇄ [Socket Listener] → [ConnectionManager]
                                 │
                                 ▼
                           [ColibriServer]
                           │           │
                       [Session]   [Database]
```

---

## 18.2 Bootstrap

`main.swift` esegue i seguenti passi:
1. Carica `ServerConfig` (porta, percorsi, parametri di sicurezza).
2. Inizializza `ColibriServer` con riferimento a `Database` e `CatalogManager`.
3. Avvia `ConnectionManager.start()`.

Flowchart (ASCII):
```
Start → ParseConfig → Initialize Database → Start ConnectionManager → Wait for clients
```

---

## 18.3 ConnectionManager

`ConnectionManager` gestisce un socket listener (GCD). Algoritmo semplificato:
```swift
func start() {
    listener = createSocket()
    DispatchQueue.global().async { acceptLoop() }
}

func acceptLoop() {
    while running {
        let client = listener.accept()
        dispatchQueue.async { handle(client) }
    }
}
```

Caratteristiche:
- Limite connessioni (`maxConnections`).
- Backpressure tramite coda di pending client.
- Integrazione con TLS (roadmap).

---

## 18.4 Sessioni

Ogni connessione → `ServerSession` che tiene stato:
- Transazione corrente (`tid`, autocommit).
- Impostazioni (`isolationLevel`, `fetchSize`).
- Cursor APC (planned).

Le sessioni interagiscono con `ColibriServer` per eseguire i comandi.

---

## 18.5 Logging e metriche

`Logger` utilizza `os_log` (macOS) o una soluzione cross-platform. `Telemetry` raccoglie metriche su connessioni attive, throughput, latenza. Diagramma di flusso:
```
Eventi → Logger → File/Console
           │
           └→ Telemetry → Metric collector
```

---

## 18.6 Laboratorio

1. Avviare il server (`swift run coldb-server`).
2. Monitorare log in tempo reale (`tail -f Server.log`).
3. Usare `coldb-dev \server stats` (da implementare) per visualizzare metriche.

---

## 18.7 Collegamenti
- **Capitolo 19**: wire protocol e gestione messaggi.
- **Parte VI**: CLI e strumenti interagiscono con il server.


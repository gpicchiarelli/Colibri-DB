# Capitolo 18 — Architettura del Server ColibrìDB

## 18.1 Componenti principali
- Binario `coldb-server`: entry point per lanciare il server.
- Libreria `ColibriServer`: contiene la logica di business per gestire sessioni e routing.
- `ConnectionManager`: gestisce socket, thread e backpressure.

## 18.2 Bootstrap
`main.swift` legge la configurazione (`ServerConfig`), inizializza `ColibriServer`, avvia `ConnectionManager`. Analizziamo il flusso di inizializzazione, compresi i controlli su file di configurazione e directory data.

## 18.3 ConnectionManager
`ConnectionManager.start()` esegue:
1. Apertura del socket listener.
2. Loop `acceptLoop()` che accetta connessioni.
3. Per ogni client, delega a `handle(client:)` su thread/queue dedicata.

ColibrìDB utilizza GCD (DispatchQueue) per gestire la concorrenza. Discutiamo strategie di limitazione (`maxConnections`).

## 18.4 Logging e monitoraggio
Il server emette log strutturati mediante `Logger`. Le metriche sono raccolte in `Telemetry`. Spieghiamo come attivare livelli di log e streaming.

## 18.5 Roadmap
- Supporto async/await.
- Load balancing multi-node.
- Warm restart.

---
layout: page
title: Wire Protocol
description: Capitolo 11 - Protocollo di comunicazione ColibrìDB
---

# Capitolo 19 — Wire Protocol e Gestione Sessioni

> **Obiettivo**: documentare il protocollo di comunicazione tra client e server, mostrando il formato dei messaggi, la sequenza di handshake e la gestione dello stato di sessione.

---

## 19.1 Modello comunicativo

ColibrìDB utilizza un protocollo binario personalizzato (estendibile) definito in `WireProtocol.swift`. Ogni messaggio contiene:
- `type`: identifica il comando (es. `ExecuteSQL`, `Prepare`, `Describe`).
- `payload`: dati (JSON/Binary) serializzati.
- `length` e, in roadmap, `checksum`.

Tabella messaggi (estratto):

| Tipo | Payload | Descrizione |
|------|---------|-------------|
| `HELLO` | Versione, capabilities | Inizio handshake |
| `AUTH` | Credenziali | Autenticazione |
| `EXECUTE` | SQL, parametri | Esecuzione query |
| `FETCH` | Cursor, batch size | Recupero risultati |

---

## 19.2 Handshake

Sequenza (diagramma di sequenza):
```
Client → Server: HELLO
Server → Client: HELLO_ACK
Client → Server: AUTH(username, password)
Server → Client: AUTH_OK / AUTH_FAIL
Client → Server: SETUP (opzioni sessione)
```

### 19.2.1 Autenticazione
Attualmente password in chiaro (roadmap: TLS e hashing). Ruoli/profili sono gestiti tramite `SystemCatalog.registerRole`.

---

## 19.3 Gestione sessione

`Session` mantiene variabili:
- `transactionState`: autocommit, `begun`, `committed`, `aborted`.
- `currentIsolationLevel`.
- `cursors`: per fetch incrementale.

Ogni comando wire è processato da `APIHandler.handle(request:session:)` che aggiorna lo stato di sessione e invoca `Database`/`Executor`.

---

## 19.4 Messaggi SQL

Sequenza tipica per query:
```
Client → EXECUTE (SQL)
Server → RESULT_METADATA
Server → ROWSET (batch n)
... (ripetuto finché ROWSET empty)
Server → COMPLETE (rows, timing)
```

`FETCH` consente di ottenere batch successivi quando i risultati sono stati bufferizzati nel server.

---

## 19.5 Error handling

Errori sono incapsulati in messaggi `ERROR` con campi:
- Codice (es. `ERR_SYNTAX`, `ERR_RUNTIME`).
- Messaggio descrittivo.
- Dettagli (stack trace o query correlata).

---

## 19.6 Sicurezza e roadmap

Progettate estensioni:
- TLS con certificati.
- Autenticazione token e plugin.
- Rate limiting e audit log.

---

## 19.7 Laboratorio

1. Avviare il server e catturare traffico con `tcpdump`/`Wireshark` (in ambiente di test) per osservare handshake.
2. Utilizzare la CLI e verificare la sequenza dei messaggi.
3. Simulare errori (es. query errata) e analizzare il messaggio `ERROR`.

---

## 19.8 Collegamenti
- **Capitolo 18**: architettura server.
- **Parte VI**: CLI `coldb` e `coldb-dev` implementano il protocollo.


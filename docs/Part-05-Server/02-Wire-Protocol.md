# Capitolo 19 — Wire Protocol e Gestione Sessioni

## 19.1 Protocollo di comunicazione
- Messaggi definiti in `Sources/coldb-server/WireProtocol.swift`.
- Sequenza handshake: auth, capabilities, setup transazionali.

## 19.2 Serializzazione dati
- Formato messaggi: header, payload, checksum (se previsto).
- Conversione tipi (`Value` ↔ wire representation).

## 19.3 API Handler
- `Sources/ColibriServer/APIHandler.swift`.
- Routing di comandi (SQL, metadata, maintenance).

## 19.4 Session management
- Stato della sessione: transazione corrente, cursori, fetch size.
- Concorrenza e locking sessioni.

## 19.5 Sicurezza
- Autenticazione, ruoli, TLS (roadmap).
- Rate limiting, auditing.

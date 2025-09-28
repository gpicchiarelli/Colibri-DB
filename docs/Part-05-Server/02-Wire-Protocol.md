# Capitolo 19 — Wire Protocol e Gestione Sessioni

## 19.1 Protocollo wire
Il file `WireProtocol.swift` definisce messaggi e codifica. Descriviamo il formato binario: header (tipo messaggio, lunghezza), payload (JSON/Binary), checksum (in roadmap).

## 19.2 Handshake
Quando un client si connette:
1. Scambio `HELLO` con versione protocollo.
2. Autenticazione (username/password, future estensioni).
3. Negoziazione di opzioni (encoding, fetch size).

## 19.3 API Handler
`APIHandler` gestisce comandi: `executeSQL`, `prepare`, `describe`, `maintenance`. Analizziamo la funzione `handle(request:session:)` che effettua dispatch in base al tipo di messaggio.

## 19.4 Gestione sessione
`Session` mantiene stato: transazione corrente, autocommit, cursori, parametri. Discutiamo la staffetta tra `ConnectionManager` e `APIHandler`.

## 19.5 Sicurezza
Attualmente supporto di base (password). Roadmap: TLS, token, ruoli avanzati.

## 19.6 Laboratorio
- Utilizzare il client CLI per inviare comandi e analizzare i pacchetti con un packet sniffer.
- Simulare richieste errate per testare la gestione errori.

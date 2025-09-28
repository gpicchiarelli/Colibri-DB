# Appendice B — Guida alla Configurazione

## B.1 File di configurazione
- `colibridb.conf.json`: parametri di database, WAL, server.
- Esempio con commenti e spiegazione di ciascun campo.

## B.2 Parametri runtime
- `DBConfig`: opzioni per storage, WAL, checkpoint.
- `ServerConfig`: porta, pool thread, sicurezza.
- `CheckpointConfig`: intervalli e durata.

## B.3 Directory
- `data/`: file WAL, catalogo, checkpoint.
- Best practice per permessi e backup.

## B.4 Ambienti
- Setup su macOS (launchctl) e Linux (systemd).

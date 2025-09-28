# Capitolo 23 — Monitoring, Build e DevOps

## 23.1 Pipeline di build
- `swift build`, `swift test`, integrazione con CI.
- Script `docs/build.sh` (nuova versione da pianificare).

## 23.2 Monitoring
- `Telemetry` e `Metrics` (file `Sources/ColibriCore/Telemetry`).
- Esposizione metriche per Prometheus/Grafana (roadmap).

## 23.3 Packaging e distribuzione
- Bundle server macOS/Linux.
- Configurazione `plist`, `launchd`.

## 23.4 Backup e ripristino
- Strategie con `CheckpointCatalog`, snapshot WAL.
- Strumenti CLI per backup.

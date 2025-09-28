# Capitolo 22 — `coldb-dev`: Strumenti per sviluppatori

## 22.1 Architettura del tool
- Organizzazione `Sources/coldb-dev` (CLI, Debugging, Monitoring, Reporting, Testing, Utilities).
- Entry point `main.swift`.

## 22.2 Comandi di debug
- `\wal tail`, `\heap inspect`, `\buffer stats`.
- File `DevCLI+Debugging.swift`, `DevCLI+Data.swift`.

## 22.3 Testing e simulazioni
- `DevCLI+Testing.swift`: generazione workload, fuzzing, assertions.

## 22.4 Reporting
- `DevCLI+Reporting.swift`: esportazione metriche, grafici.

## 22.5 Estensioni future
- Integrazione con Swift scripting, plugin system.

# Capitolo 22 — `coldb-dev`: Strumenti per sviluppatori

## 22.1 Organizzazione
`coldb-dev` offre comandi avanzati per debugging, testing, monitoring. La struttura prevede moduli per CLI, Debugging, Monitoring, Reporting, Testing, Utilities.

## 22.2 Debugging
Comandi come `\wal tail`, `\heap inspect`, `\buffer stats` permettono di esplorare lo stato interno. Analizziamo come queste funzioni chiamano direttamente API Swift (`Database`, `FileHeapTable`, `BufferPool`).

## 22.3 Testing
`DevCLI+Testing.swift` fornisce generatori di workload, fuzzing, test di coerenza. Descriviamo gli scenari disponibili e come interpretarli.

## 22.4 Reporting e Monitoring
`DevCLI+Reporting.swift` esporta metriche, grafici. `DevCLI+Monitoring.swift` integra con sistemi di monitoring.

## 22.5 Roadmap
Plugin system, script personalizzati, integrazione con IDE.

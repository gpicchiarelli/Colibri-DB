# Capitolo 22 — `coldb-dev`: Strumenti per Sviluppatori

> **Obiettivo**: documentare la CLI avanzata per debugging e manutenzione, trattando comandi, architettura interna e scenari pratici.

---

## 22.1 Organizzazione del progetto

`coldb-dev` è suddivisa in moduli:
- `CLI/` — parsing comandi e dispatcher.
- `Debugging/` — strumenti di introspezione (heap, WAL, buffer).
- `Monitoring/` — metriche e stati runtime.
- `Testing/` — generatori workload, fuzzing.
- `Reporting/` — esportazione report.

Diagramma moduli:
```
DevCLI
 ├─ Debugging
 ├─ Testing
 ├─ Monitoring
 └─ Utilities
```

---

## 22.2 Comandi di debugging

| Comando | Descrizione |
|---------|-------------|
| `\wal tail` | Visualizza gli ultimi record WAL |
| `\heap inspect table` | Mostra dettagli pagina per pagina |
| `\buffer stats` | Riassunto del buffer pool |
| `\catalog dump` | Stampa contenuto catalogo |

Ogni comando chiama funzioni Swift che interagiscono direttamente con il motore (senza passare dal wire protocol in alcuni casi).

---

## 22.3 Testing e simulazione

`DevCLI+Testing.swift` offre strumenti per generare carichi e validare invarianti:
- `\test wal` per verificare monotonicità LSN.
- `\test recovery` per simulare crash.
- `\benchmark insert` per misurare throughput.

---

## 22.4 Reporting e Monitoring

`DevCLI+Reporting.swift` esporta metriche in formati (CSV/JSON). `Monitoring` può integrare con sistemi esterni (future feature).

---

## 22.5 Laboratorio

1. Eseguire `\wal tail` dopo una sequenza di transazioni.
2. Usare `\heap inspect accounts` per visualizzare layout pagine.
3. Avviare `\test recovery` e osservare output.

---

## 22.6 Collegamenti
- **Capitolo 5**: comprensione WAL aiuta a interpretare output `\wal tail`.
- **Parte VII**: test e benchmark utilizzano DevCLI.


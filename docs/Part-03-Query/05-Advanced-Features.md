# Capitolo 14 — Funzionalità Avanzate di Query

> **Obiettivo**: esplorare le capacità avanzate del motore SQL (aggregazioni, funzioni, ordinamenti) e delineare le estensioni pianificate.

---

## 14.1 Aggregazioni e Group By

`AggregateOperator` implementa funzioni aggregate:
- `SUM`
- `COUNT`
- `AVG`
- `MIN`/`MAX`

Pipeline tipica:
```
HashAggregate
└─ Project/Filter
   └─ Scan
```

Tabella di stato (esempio `GROUP BY department`):

| Chiave | Stato parziale |
|--------|----------------|
| Sales | {sum=1000, count=4} |
| Tech | {sum=2000, count=3} |

Formula per `AVG`: \( \text{avg} = \frac{\text{sum}}{\text{count}} \).

---

## 14.2 Funzioni scalari

`FunctionRegistry` mappa nomi (es. `UPPER`) a implementazioni Swift. Schema:
```
FunctionRegistry
 ├─ builtIn
 └─ userDefined (roadmap)
```

### Estensioni
- Funzioni user-defined via plugin.
- Funzioni matematiche avanzate, stringhe, date.

---

## 14.3 Ordinamento e limit

`SortOperator` implementa un sort ibrido (in-memory con spill-to-disk). `TopKOperator` effettua `LIMIT/OFFSET`:
```
Sort → TopK → Output
```

---

## 14.4 Funzionalità future

- **Window functions**: `ROW_NUMBER`, `RANK`, `OVER(partition by ...)`.
- **Common Table Expressions (CTE)** e subquery ricorsive.
- **Materialized views** e indicizzazione delle query.

---

## 14.5 Laboratorio

1. Eseguire query con aggregazione e osservare piani (`--explain`).
2. Aggiungere `ORDER BY` e `LIMIT`, verificare operatori aggiuntivi.
3. Progettare un'estensione `median()` tramite `FunctionRegistry` (es. pseudocodice/roadmap).

---

## 14.6 Collegamenti
- **Parte VII**: benchmarking di scenari aggregati.
- **Parte VIII**: roadmap per window functions e CTE.


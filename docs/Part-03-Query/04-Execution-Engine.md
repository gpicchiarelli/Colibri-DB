# Capitolo 13 — Motore di Esecuzione e Iteratori

> **Obiettivo**: descrivere il runtime delle query in ColibrìDB basato su operatori iteratore, evidenziando il flusso dati e i meccanismi di valutazione delle espressioni.

---

## 13.1 Modello iteratore

Ogni operatore fisico implementa il protocollo `ExecutionOperator` con funzione `next()` che restituisce `Row?`. Questa architettura segue il modello Volcano (Graefe, 1990).

Schema:
```
Client ← Executor ← OperatorA ← OperatorB ← ... ← Scan
```

Il modello è **pull-based**: il livello sopra richiede tuple a quello sotto.

---

## 13.2 Operator catalog

| Operatore | Funzione | File |
|-----------|----------|------|
| `TableScanOperator` | Legge tuple sequenziali | `Query/Operators/TableScanOperator.swift` |
| `IndexScanOperator` | Percorre B+Tree | `Query/Operators/IndexScanOperator.swift` |
| `FilterOperator` | Applica predicati | `Query/Operators/FilterOperator.swift` |
| `ProjectionOperator` | Calcola espressioni | `Query/Operators/ProjectionOperator.swift` |
| `JoinOperator` | Nested Loop Join (hash future) | `Query/Operators/JoinOperator.swift` |
| `AggregateOperator` | Funzioni di aggregazione | `Query/Operators/AggregateOperator.swift` |

---

## 13.3 Sequenza di esecuzione

Pseudocodice generico:
```swift
func execute(plan: PhysicalPlan) -> ResultSet {
    let operator = buildOperator(plan)
    var rows: [Row] = []
    while let row = operator.next() {
        rows.append(row)
    }
    return ResultSet(rows)
}
```

### 13.3.1 TableScan
```
while let page = heap.nextPage() {
    for row in page.rows {
        yield row
    }
}
```

### 13.3.2 Filter
```
while let row = child.next() {
    if predicate(row) {
        yield row
    }
}
```

---

## 13.4 Valutazione espressioni

`ExpressionEvaluator` traduce `SQLExpression` in funzioni Swift. Supporta:
- Operazioni aritmetiche (`+`, `-`, `*`, `/`).
- Operatori logici (`AND`, `OR`, `NOT`).
- Funzioni built-in (`UPPER`, `LOWER`, etc.).

Tabella di supporto:

| Tipo operazione | Implementazione |
|-----------------|-----------------|
| Aritmetica | `evaluateNumeric(lhs, rhs)` |
| Confronto | `compare(lhs, rhs)` |
| Funzioni | `FunctionRegistry.lookup(name)` |

---

## 13.5 Materializzazione e streaming

Il server può restituire risultati in blocchi (`ResultBuffer`). L'esecuzione mantiene un bilanciamento tra latenza e throughput. Schema:
```
Executor → ResultBuffer → WireProtocol
```

---

## 13.6 Controllo errori

Gli operatori propagano errori (`ExecutionError`) che il server converte in messaggi wire. Esempi: divisione per zero, tipo non supportato.

---

## 13.7 Laboratorio

1. Abilitare logging del runtime (`Executor.enableTracing = true`).
2. Eseguire query con join e aggregazioni.
3. Analizzare l'ordine delle chiamate a `next()` nel log.

---

## 13.8 Collegamenti
- **Capitolo 12**: piani fisici generano operatori.
- **Parte V**: `APIHandler` usa l'executor per rispondere alle richieste client.


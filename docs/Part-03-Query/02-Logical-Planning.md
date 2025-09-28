# Capitolo 11 — Piano Logico e Analisi Semantica

> **Obiettivo**: formalizzare il passaggio da AST a piano logico, evidenziando regole algebriche, processi di binding e controllo dei tipi.

---

## 11.1 Ruolo del piano logico

Il piano logico è un DAG di operatori relazionali che rappresenta l'esecuzione ideale di una query indipendentemente dagli algoritmi fisici. Ogni nodo è un'operazione algebrica (`Scan`, `Filter`, `Project`, `Join`, `Aggregate`).

Diagramma esemplificativo:
```
Project [balance]
└─ Filter [id = 42]
   └─ Scan [accounts]
```

---

## 11.2 Componenti del planner

| Componente | Funzione | File |
|------------|----------|------|
| `LogicalPlanner` | Costruisce operatori logici dall'AST | `Planner/LogicalPlanner.swift` |
| `BindingContext` | Mappa alias → colonne | `Planner/BindingContext.swift` |
| `TypeChecker` | Verifica coerenza tipi | `Planner/TypeChecker.swift` |
| `RuleEngine` | Applica riscritture | `Planner/Rules` |

---

## 11.3 Pipeline di pianificazione

Pseudocodice:
```swift
func plan(select stmt: SQLSelect) -> LogicalPlan {
    let source = planFromClause(stmt.from)
    let filtered = applyWhere(stmt.where, to: source)
    let grouped = applyGroupBy(stmt.groupBy, to: filtered)
    let projected = applyProjections(stmt.projections, to: grouped)
    return projected
}
```

### 11.3.1 From clause
- `planFromClause` gestisce tabelle e join.
- Usa `CatalogManager` per verificare l'esistenza delle tabelle e recuperare schema.

### 11.3.2 Where clause
`applyWhere` produce un `LogicalPlan.filter`. Il predicato è convertito in `Predicate` dopo type-checking.

### 11.3.3 Proiezioni
`applyProjections` crea `LogicalPlan.project`, generando espressioni (`ExpressionPlan`) con alias.

---

## 11.4 Binding e analisi semantica

#### 11.4.1 Binding
`BindingContext` mantiene l'associazione alias→colonne. Durante la parse di `accounts a`, il planner registra `a` come alias.

#### 11.4.2 Type checking
`TypeChecker` percorre il piano e assegna tipi alle espressioni. Tabelle riassuntiva (esempio):

| Espressione | Tipo dedotto |
|-------------|--------------|
| `id + 1` | `INT` |
| `balance * 1.05` | `DOUBLE` |
| `owner || ' Inc.'` | `STRING` |

Errori generano `PlannerError.typeMismatch`.

---

## 11.5 Regole logiche

`RuleEngine` applica trasformazioni per semplificare il piano:
- **Pushdown selezioni**: sposta filtri vicino alle sorgenti.
- **Proiezioni minimali**: elimina colonne inutilizzate.
- **Rimozione join ridondanti**: ottimizzazione basata su chiavi.

Schema rule application:
```
repeat
    for rule in rules
        if rule.matches(plan)
            plan = rule.apply(plan)
until no changes
```

---

## 11.6 Output e diagnosi

`LogicalPlan.describe()` produce un dump testuale. Esempio per join:
```
Project [a.id, b.balance]
└─ Join [a.id = b.id]
   ├─ Scan [accounts a]
   └─ Scan [balances b]
```

Le descrizioni facilitano il debug e la didattica.

---

## 11.7 Laboratorio

1. Eseguire `swift run coldb --explain "SELECT ..."`.
2. Annotare il piano logico stampato.
3. Modificare query (aggiungere filtri/alias) e osservare il binding.

---

## 11.8 Collegamenti
- **Capitolo 12**: dal piano logico a quello fisico.
- **Capitolo 5** (WAL): alcune riscritture devono preservare determinati invarianti per supportare recovery.


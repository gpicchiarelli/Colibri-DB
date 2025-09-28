---
layout: page
title: B+Tree Indexes
description: Capitolo 8 - Indici B+Tree in ColibrìDB
---

# Capitolo 8 — Indici B+Tree e Strutture Secondarie

> **Obiettivo**: illustrare il funzionamento degli indici B+Tree in ColibrìDB con una trattazione simile a quella dei testi classici (es. Comer, 1979), integrando diagrammi, pseudocodice e riferimenti al codice Swift.

---

## 8.1 Teoria dei B+Tree

Un B+Tree è definito da un parametro d (ordine minimo) che determina il grado dei nodi. Proprietà:
- Tutti i nodi (tranne la radice) hanno tra d e 2d chiavi.
- Le foglie sono collegate sequenzialmente.
- Profondità uniforme (albero bilanciato).

Diagramma ASCII (d=2):
```
         [K1 | K2]
        /     |    \
    [..]    [..]   [..]
             |
        [leaf] - [leaf] - [leaf]
```

---

## 8.2 Implementazione `FileBPlusTreeIndex`

### 8.2.1 Header
`Header` contiene `pageSize`, `root`, `nextPage`, `checkpointLSN`. È persistito nel file indice e aggiornato a ogni checkpoint.

### 8.2.2 Pagine
- **InternalNode**: array di chiavi + puntatori a pagine figlie.
- **LeafNode**: array di chiavi + RIDs, più puntatore alla foglia successiva.

Chiavi sono memorizzate come `KeyBytes` per supportare tipi multipli.

---

## 8.3 Operazioni

### 8.3.1 Ricerca
`search(key:)`:
1. Inizia dal root.
2. In ciascun nodo, trova il figlio appropriate (ricerca binaria).
3. Arriva alla foglia e restituisce la posizione.

### 8.3.2 Inserimento
Pseudocodice semplificato:
```swift
func insert(key, rid) {
    let leaf = findLeaf(key)
    leaf.insert(key, rid)
    if leaf.isFull {
        let (newKey, newPage) = leaf.split()
        insertIntoParent(leaf, newKey, newPage)
    }
}
```

`split()` dividi il nodo in due metà; `insertIntoParent` potrebbe propagare a nodi interni e fino al root.

### 8.3.3 Cancellazione
1. Rimuove la chiave dalla foglia.
2. Se la foglia scende sotto il minimo, prova a prendere prestito da fratello o effettua merge.
3. Se un nodo interno scende sotto soglia, ripete l'operazione.

---

## 8.4 Logging e checkpoint

Le operazioni indice generano record WAL (`WALIndexInsertRecord`, `WALIndexDeleteRecord`). Durante `checkpointIndex`, l'header viene aggiornato e il WAL dell'indice è troncato per evitare crescita sregolata.

---

## 8.5 Uso nel planner

`IndexStatistics` fornisce cardinalità e selettività stimata. Il planner usa queste informazioni per decidere se utilizzare un index scan.

Tabella decisionale semplificata:

| Condizione | Piano scelto |
|------------|--------------|
| Selettività bassa | IndexScan |
| Selettività alta | TableScan |
| Nessun indice disponibile | TableScan |

---

## 8.6 Laboratorio

1. Creare indice: `CREATE INDEX idx_balance ON accounts(balance);`
2. Eseguire query `EXPLAIN SELECT * FROM accounts WHERE balance > 1000;` (funzione `--explain`).
3. Confrontare piani con e senza indice.
4. Utilizzare `coldb-dev \index stats idx_balance` (da implementare) per visualizzare layout.

---

## 8.7 Collegamenti
- **Capitolo 7**: RIDs puntano alle tuple nelle heap tables.
- **Capitolo 12**: planner fisico usa gli indici per ottimizzare join e selezioni.


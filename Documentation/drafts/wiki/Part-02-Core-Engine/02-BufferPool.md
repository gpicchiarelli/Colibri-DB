# Capitolo 6 — Buffer Pool e Gestione Pagine

> **Obiettivo**: analizzare il sottosistema buffer pool con schemi, tabelle riassuntive e laboratori. Dimostrare come ColibrìDB realizzi la coerenza tra memoria e disco.

---

## 6.1 Modello teorico

Il buffer pool è una struttura cache che mantiene in memoria un sottoinsieme delle pagine di disco. Il problema classico è il **caching con politiche di rimpiazzamento**.

### 6.1.1 Politica LRU
ColibrìDB utilizza una variante LRU (Least Recently Used). Formalmente, il buffer seleziona come vittima la pagina con timestamp di accesso minimo tra quelle con `pinCount = 0`.

### 6.1.2 Equazioni base
- Miss rate approssimato \( R_m = \frac{\text{misses}}{\text{accessi totali}} \)
- Hit rate \( R_h = 1 - R_m \)

Queste metriche sono esposte via `BufferPool.stats`.

---

## 6.2 Strutture dati

| Struttura | Descrizione | Campi principali |
|-----------|-------------|------------------|
| `BufferPool` | Gestisce l'intero pool | `frames`, `lruList`, `lock` |
| `BufferFrame` | Rappresenta una pagina in memoria | `pageId`, `data`, `pinCount`, `isDirty`, `lastAccess` |
| `BufferNamespaceManager` | Gestisce pool per namespace | `namespaces`, `registerNamespace()` |

Diagramma UML semplificato:
```
BufferNamespaceManager
 └─ BufferPool (per namespace)
     ├─ BufferFrame
     └─ Lock/Stats
```

---

## 6.3 API principali

### 6.3.1 Pin
`pin(pageId:)` carica una pagina. Pseudocodice:
```swift
func pin(pageId) -> BufferFrame {
    lock.lock()
    if let frame = frames[pageId] {
        frame.pinCount += 1
        frame.lastAccess = now
        lock.unlock()
        return frame
    }
    // Miss: carica dal disco
    let page = storage.read(pageId)
    let frame = BufferFrame(pageId, page)
    frames[pageId] = frame
    frame.pinCount = 1
    lock.unlock()
    return frame
}
```

### 6.3.2 Unpin
`unpin(pageId:)` decrementa `pinCount`. Se `pinCount` raggiunge zero, la pagina diventa candidabile per eviction.

### 6.3.3 Mark dirty
`markDirty(pageId:)` segna la pagina come modificata, richiedendo flush futuro.

---

## 6.4 Flush e WAL

`flushAll()`:
1. Itera sui `frames` dirty.
2. Per ogni frame, verifica `page.pageLSN ≤ wal.flushedLSN`.
3. Scrive la pagina su disco (`storage.write(page:)`).

Questo passaggio assicura WAL-before-data.

---

## 6.5 Eviction

`evictVictim()` seleziona la pagina con `pinCount == 0` e minimo `lastAccess`. In caso di litigi sulle politiche di sostituzione, il manuale suggerisce di considerare algoritmi CLOCK o 2Q (roadmap).

---

## 6.6 BufferNamespaceManager

Consente di avere pool separati (es. tabelle vs indici). Funzioni:
- `registerNamespace(name:size:)`
- `buffer(namespace:)`
- `flush(namespace:)`

---

## 6.7 Laboratorio

1. Configurare un buffer pool piccolo.
2. Eseguire un carico (es. 10K letture) e misurare hit/miss con `\buffer stats`.
3. Generare collisioni e osservare l'eviction.

Output atteso:
```
Namespace default:
  frames: 128
  hitRate: 0.85
  dirtyPages: 10
```

---

## 6.8 Collegamenti
- **Capitolo 7**: interazione con `FileHeapTable`.
- **Capitolo 5**: relazione con WAL (`pageLSN`).
- Appendice: configurazioni del buffer pool.


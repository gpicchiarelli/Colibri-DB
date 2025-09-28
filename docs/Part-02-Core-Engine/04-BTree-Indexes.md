# Capitolo 8 — Indici B+Tree e Strutture Secondarie

## 8.1 Richiami teorici
Un indice B+Tree è un albero bilanciato che minimizza la profondità e permette ricerche log(N). Presentiamo lo schema classico: nodi interni con k+1 figli, nodi foglia con puntatori sequenziali.

## 8.2 Implementazione `FileBPlusTreeIndex`
Struttura definita in `Sources/ColibriCore/Index/BPlusTree`. Elementi importanti:
- `Header`: contiene `pageSize`, `root`, `nextPage`, `checkpointLSN`.
- `Node`: struttura delle pagine interne/foglia.
- `KeyBytes`: codifica delle chiavi (supporto per tipi multipli).

## 8.3 Operazioni
### 8.3.1 Ricerca
`search(key:)` naviga dal root alla foglia confrontando chiavi (comparatore generico). Analizziamo il costo.

### 8.3.2 Inserimento
`insert(key:rid:)`:
1. Ricerca della foglia corretta.
2. Inserimento ordinato.
3. Split se il nodo supera la capacità: generazione di un nuovo nodo, promozione della chiave mediana.
4. Aggiornamento del padre ricorsivamente.

### 8.3.3 Cancellazione
`remove(key:rid:)` rimuove la coppia chiave-RID; se il nodo scende sotto la capacità minima, avvia merge o redistribuzione.

## 8.4 Logging e checkpoint
Ogni operazione produce record WAL (`logIndexInsert/Delete`). `checkpointIndex()` scrive l'header aggiornato e tronca il WAL degli indici.

## 8.5 Ottimizzazione nel planner
`IndexStatistics` fornisce cardinalità e selettività usate dal planner per decidere se utilizzare l'indice.

## 8.6 Laboratorio
- Creare indice su `accounts(balance)`.
- Eseguire query con e senza indice confrontando piani.
- Osservare la struttura mediante `coldb-dev \index inspect` (feature da implementare).

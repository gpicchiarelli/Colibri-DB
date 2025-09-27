# ColibrìDB — Limiti dimensionali

Questo documento raccoglie i principali vincoli dimensionali (intrinseci e configurabili) del motore ColibrìDB nella versione corrente. I valori indicati derivano dal codice sorgente (`Sources/ColibriCore/`) e dai default esposti da `DBConfig`.

## Tabelle e pagine
- **Dimensione pagina**: configurabile tramite `DBConfig.pageSizeBytes` (default 8192 byte). Tutte le tuple devono entrare in una singola pagina; una riga che supera `pageSizeBytes - overhead` viene rifiutata (`FileHeapTable.insert`).
- **Slot per pagina**: il contatore di slot (`PageHeader.slotCount`) è `UInt16`, quindi ogni pagina può contenere al massimo 65 535 tuple.
- **Identificatore record (RID)**: `RID.pageId` è `UInt64`, `RID.slotId` è `UInt16`. In teoria una tabella heap può crescere fino a 2^64−1 pagine (≈ 1.5e19) con 65 535 tuple per pagina, ma i limiti effettivi sono vincolati da spazio disco e dai tool di manutenzione.
- **Row size consigliata**: con la pagina da 8 KB, riservando ~64 B a header e slot directory, la dimensione pratica di una riga è ≤ 8 048 B. Per payload più grandi è necessario introdurre TOAST/overflow page (non ancora implementate).

## Indici
- **Pagine e capacità**: gli indici `FileBPlusTreeIndex` usano la stessa `pageSizeBytes` della tabella. Ogni foglia interna può quindi contenere ≤ 65 535 chiavi.
- **B+Tree**: pageId `UInt64`, quindi l’albero può crescere praticamente senza limiti teorici. Gli aggiornamenti sono limitati dall’I/O e dallo spazio su disco.
- **Indici in-memory (`AnyStringIndex`)**: supportano una singola colonna; le chiavi composite sono disponibili solo con il backend B+Tree persistente.

## Buffer pool e cache
- **Buffer tabelle**: `config.dataBufferPoolPages` (default 16 384) → ~128 MiB con pagina da 8 KB.
- **Buffer indici**: `config.indexBufferPoolPages` (default 4 096) → ~32 MiB.
- **Quote per namespace**: gestite da `BufferNamespaceManager`; i pool aggiuntivi devono rispettare la quota globale per gruppo (`table`, `index`).

## WAL e recovery
- **LSN**: `UInt64`, quindi 2^64−1 record distinguibili; l’LSN cresce monotonicamente.
- **Lunghezza record**: campo `UInt32` (big endian) → ogni record WAL può contenere ≤ 4 294 967 295 byte di payload.
- **Checkpoint**: il WAL principale viene troncato solo a checkpoint esplicito (`\\checkpoint` o API). Accumulare WAL oltre il limite di spazio disco impedisce nuovi commit.

## Transazioni e concorrenza
- **TID**: `Database.nextTID` usa `UInt64` → fino a 18 miliardi di transazioni senza wraparound.
- **Lock manager**: non impone limiti hard-coded al numero di lock simultanei; il bound deriva dalla memoria disponibile.
- **Connessioni**: `DBConfig.maxConnectionsLogical` default 1 000 000 (limitato dalle risorse di sistema). `maxConnectionsPhysical` default 16.

## Riepilogo configurazioni principali

| Parametro (`DBConfig`) | Default | Significato |
| --- | ---: | --- |
| `pageSizeBytes` | 8 192 | Dimensione pagina heap/indice. |
| `dataBufferPoolPages` | 16 384 | Pagine nel buffer pool tabelle. |
| `indexBufferPoolPages` | 4 096 | Pagine nel buffer pool indici. |
| `autoCompactionPagesPerRun` | 32 | Pagine compattate per tick vacuum. |
| `optimizerStatsSampleRows` | 1 024 | Campioni per statistiche cardinalità. |
| `lockTimeoutSeconds` | 5.0 | Timeout standard lock manager. |
| `maxConnectionsLogical` | 1 000 000 | Connessioni logiche supportate. |

## Note di capacity planning
- Pianificare la **dimensione delle tuple** per rimanere ampiamente sotto `pageSizeBytes`. Campi BLOB/testo molto grandi richiedono una futura estensione overflow.
- Monitorare il **WAL**: se la frequenza dei checkpoint è bassa, prevedere spazio sufficiente sul volume per il log.
- Scalare `dataBufferPoolPages`/`indexBufferPoolPages` in base al dataset attivo; con pagina da 8 KB un incremento di 10 000 pagine ≈ 78 MiB.
- In workload con molte tabelle, considerare la pressione sul **free slot count**: 65 535 righe/pagina bastano per chiavi compatte, ma wide row riducono drasticamente la densità.

Per ulteriori dettagli sulle manopole di configurazione consultare `docs/configuration.md`. Per l’impatto sulle performance vedere la sezione dedicata nel README (in aggiornamento).

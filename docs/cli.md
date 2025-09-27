# CLI `coldb`

La CLI `coldb` fornisce un'interfaccia interattiva per amministrare ColibrìDB. Offre comandi stile `psql` con prefisso `\` e stampa metriche e report.

## Avvio
```
swift build
.build/debug/coldb --config colibridb.conf.json
```
Opzioni: `--config/-c <path>` per usare un file di configurazione alternativo.

## Sessione interattiva
- Banner iniziale con versione MVP.
- `\help` elenca tutti i comandi supportati.
- I comandi sono case-sensitive e gli argomenti multipli sono separati da spazi.

## Gestione tabelle
```
\dt                               # elenco tabelle
\create table <name>              # crea tabella heap (rispetta storageEngine)
\scan <table>                     # scansione con snapshot MVCC corrente
\insert <table> col=val,...       # inserisce riga (autocommit o transazione aperta)
\delete <table> col=val[,col2=val2]
\table compact <table> [page]     # compattazione heap mirata
```

## Transazioni
```
\begin
\commit [tid]
\rollback [tid]
\vacuum start [sec] [pages]
\vacuum stop
\vacuum stats
\checkpoint
```
`\commit`/`\rollback` senza argomento operano sul TID corrente; i comandi mostrano l'identificativo della transazione.

## Indici
```
\create index <name> ON <table>(<col[,col2,...]>) USING <Hash|ART|SkipList|Fractal|LSM|BTree>
\indexes <table>
\index search <table> <index> <value[,value2,...]>
\index range <table> <index> <lo> <hi>
\index validate <table> <index>
\index validate-deep <table> <index>
\index rebuild <table> <index>
\index rebuild-bulk <table> <index>
\index dump-header <table> <index> [pageId]
\index dump-leaves <table> <index> [count]
\index compact <table> <index>
```

## Import/Export
```
\import <file.csv> INTO <table>
\export <table> TO <file.csv>
```
- Import CSV richiede header sulla prima riga; i valori vengono mappati per nome colonna.
- Export genera header ordinale (colonne ordinate alfabeticamente) e gestisce escaping `","`/`""`.

## Buffer, WAL e metriche
```
\conf                          # mostra configurazione attiva
\bp                            # statistiche buffer pool per namespace
\stats                         # aggregate buffer/vacuum
\stats prometheus              # esporta metriche per Prometheus
\flush all [fullsync]          # flush globale; con fullsync usa F_FULLFSYNC su heap/indici (macOS)
\flush table <table> [fullsync]
\flush index <table> <index> [fullsync]
```

## Policy & ottimizzazione
```
\policy add time-window <table> [BY col1,col2] WINDOW hh:mm-hh:mm
\policy add load-threshold <table> THRESHOLD qps=100,cpu=20%
\policy add fragmentation <table> THRESHOLD 30%
\policy list
\policy remove <uuid>
\optimize simulate <table> [BY col1,col2]
```
Il simulatore restituisce stima durata, spazio temporaneo e beneficio percentuale.

## Debug & fault injection
```
\fault set <key> <n>           # inietta fallo dopo n eventi (es. wal.append)
\fault clear
```

## Uscita
`\exit` o `Ctrl+D` terminano la sessione restituendo il controllo alla shell.

Aggiorna questo documento ogni volta che vengono aggiunti comandi alla CLI o cambiano le semantiche esistenti.

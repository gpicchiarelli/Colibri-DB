# Politiche di Ottimizzazione e Clustering

Le politiche automatizzano attività di manutenzione (compattazione, clustering, ottimizzazione) limitando l'impatto sul carico OLTP. Sono memorizzate in `InMemoryPolicyStore` e gestite dalla CLI.

## Tipologie supportate
- **Time-window** — definisce finestre temporali in cui è consentito eseguire interventi (`WINDOW hh:mm-hh:mm`).
- **Load-threshold** — associa soglie (QPS, CPU, I/O) oltre le quali posticipare il job.
- **Fragmentation** — attiva compattazione heap/indice quando la frammentazione supera una soglia percentuale.

Ogni policy contiene: `id`, `kind`, `table`, `columns`, `params`. È possibile estendere l'enum `PolicyKind` per aggiungere nuove tipologie.

## Gestione via CLI
```
\policy add time-window <table> [BY col1,col2] WINDOW 02:00-05:00
\policy add load-threshold <table> THRESHOLD qps=100,cpu=20%
\policy add fragmentation <table> THRESHOLD 30%
\policy list
\policy remove <uuid>
```
`columns` consente di mirare la policy a specifici indici/cluster (es. compattare un indice su colonne particolari).

## Simulatore di ottimizzazione
```
\optimize simulate <table> [BY col1,col2]
```
Restituisce `time=<s> temp=<bytes> benefit=<%>` per aiutare a valutare costo/beneficio prima di avviare un'operazione manuale o di pianificare una policy.

## Integrazione con il motore
- Il vacuum periodico legge le policy `fragmentation` per decidere quando compattare una tabella.
- Gli indici B+Tree consultano `indexLeafOccupancyThreshold`/`indexCompactionCooldownSeconds` per pianificare compattazioni.
- I risultati delle simulazioni possono essere loggati nel catalogo (estensione futura) per audit e confronto con l'esecuzione reale.

## Roadmap
- Scheduler cooperativo che monitori effettivamente QPS/CPU per le politiche load-based.
- Storico delle esecuzioni, con registrazione tempo effettivo e spazio temporaneo consumato.
- Policy basate sull'analisi query (es. suggerire indici colonne, clustering).

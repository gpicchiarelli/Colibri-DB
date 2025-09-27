10 — Server
===========

Obiettivi
---------
Gestire connessioni concorrenti, timeouts e transazioni su un protocollo semplice.

Componenti
----------
- `Sources/coldb-server/ConnectionManager.swift` — gestione connection e queue per isolamento.
- `Sources/coldb-server/WireProtocol.swift` — wire protocol e messaggi.

Flusso
------
`DatabaseConnection.executeQuery(sql)` usa `SQLQueryInterface` e mappa promise/future sui thread del canale.


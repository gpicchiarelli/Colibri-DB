12 — Policy e Manutenzione
==========================

Obiettivi
---------
Automatizzare compattazione, vacuum e manutenzione con metriche di feedback.

Componenti
----------
- `Policy/PolicyStore.swift` — registro policy e scheduling.
- `Database+Maintenance.swift` — API di compattazione/vacuum e metriche aggregate.

Metriche
--------
Frammentazione heap, contatori vacuum, tempi di ultima esecuzione, statistiche buffer.


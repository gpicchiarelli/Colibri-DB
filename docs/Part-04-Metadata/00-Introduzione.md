# Parte IV — Catalogo, Statistiche e Metadati

Qui si documenta il sottosistema catalogo: come ColibrìDB tiene traccia di schemi, permessi, statistiche e configurazioni. Ogni capitolo include:

- Definizione delle strutture dati (`SystemCatalog`, `CatalogManager`).
- Flussi di aggiornamento (DDL, DCL, manutenzione).
- Persistenza on-disk (`system_catalog.json`, checkpoints).
- API pubbliche per interrogare e modificare i metadati.

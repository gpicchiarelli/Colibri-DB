# Capitolo 1 — Principi Relazionali e Modello Dati

## 1.1 Introduzione al modello relazionale
- Definizioni fondamentali: relazioni, tuple, attributi
- Chiavi primarie, candidati e vincoli di integrità
- Schema logico vs schema fisico

## 1.2 Implementazione in ColibrìDB
- Mapping tra concetti teorici e tipi Swift:
  - `Row`, `ColumnDefinition`, `TableDefinition`
  - File: `Sources/ColibriCore/Catalog/CatalogStructures.swift`
- Dizionario dei tipi (`DataType`, `TypeCodec`) e serializzazione

## 1.3 Esempi di definizione schema
- Creazione tabella via SQL
- Riflesso in `CatalogManager.createTable`

## 1.4 Vincoli
- Primary key, unique, not null
- Meccanismo di enforcement nel planner e executor

## 1.5 Conclusioni
- Punti di forza del modello nel contesto di ColibrìDB
- Limitazioni attuali e TODO futuri

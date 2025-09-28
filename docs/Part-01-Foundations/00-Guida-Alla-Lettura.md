---
layout: page
title: Guida alla Lettura della Parte I — Fondamenti
description: Guida alla lettura della documentazione tecnica di Colibrì DB
---

# Guida alla Lettura della Parte I — Fondamenti

La Parte I stabilisce il lessico e il sistema assiomatico su cui poggia Colibrì DB. Ogni capitolo è strutturato per guidare il lettore dalla teoria formale alla realizzazione pratica. Per trarre il massimo beneficio si suggerisce di adottare il seguente processo:

1. **Studio delle definizioni**: ogni sottosezione introduce definizioni rigorose. Ad esempio, nel Capitolo 1 definiremo formalmente "relazione" come sottoinsieme del prodotto cartesiano di domini, e "chiave primaria" come insieme minimo di attributi che rende la relazione funzione.
2. **Analisi del codice**: subito dopo la teoria vengono analizzate le strutture dati e le funzioni che incarnano quei concetti. Verranno riportati estratti del codice in notazione `startLine:endLine:file`, con commenti che spiegano il ruolo di ogni istruzione.
3. **Dimostrazioni e invarianti**: dove possibile, dimostreremo che l'implementazione soddisfa le proprietà teoriche. Ad esempio, mostreremo che `SystemCatalog.registerTable` mantiene l'invariante di unicità dei nomi di tabella.
4. **Esperimenti riproducibili**: ogni capitolo si chiude con un laboratorio guidato. I comandi e gli script forniti consentono di osservare concretamente i fenomeni descritti (ad esempio, la creazione di una tabella e l'aggiornamento del catalogo).

### Notazione
- Useremo **grassetto** per concetti teorici, `monospace` per simboli del codice, *corsivo* per commenti metodologici.
- Le citazioni al codice seguono il formato `startLine:endLine:percorso/del/file.swift`.
- Gli esempi SQL saranno mostrati in blocchi dedicati, con traduzione immediata in Swift quando necessario.

### Prerequisiti
- Conoscenza di algebra relazionale di base.
- Familiarità con Swift e il paradigma orientato agli oggetti/funzionale.
- Concetti elementari di sistemi operativi (memoria, I/O, filesystem).

Con questa guida, il lettore potrà navigare la parte fondativa collegando direttamente i principi accademici con l'implementazione concreta di Colibrì DB.

# Introduzione alla Parte II — Motore Core

Questa parte disseziona ogni componente del motore di esecuzione: dal Write-Ahead Log al pianificatore fisico, includendo buffer pool, indici e meccanismi di concorrenza. Ogni capitolo segue la struttura:

1. **Mappa del modulo**: file coinvolti, pattern architetturali, overview API.
2. **Analisi funzione per funzione**: firma, comportamento, invarianti, eccezioni.
3. **Interazione con altri moduli**: diagrammi di sequenza, assert condivisi.
4. **Laboratorio pratico**: come riprodurre e osservare il comportamento nel codice.

Il lettore è invitato a tenere aperto il sorgente per consultare direttamente le funzioni mentre segue i paragrafi numerati.

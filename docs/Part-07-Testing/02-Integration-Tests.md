# Capitolo 25 — Test di Integrazione e End-to-End

## 25.1 Pipeline end-to-end
Descriviamo come configurare un test completo: avvio server, esecuzione script SQL, verifica risultati, teardown.

## 25.2 Recovery tests
Scenario: transazioni in corso, crash del server, riavvio, verifica integrità. Si utilizza `DevCLI+Testing` e script shell.

## 25.3 Concorrenza
Test di transazioni parallele con carichi generati, verifica invarianti (serializability, read phenomena).

## 25.4 Automazione
Integrazione con pipeline CI/CD, scheduling regolare, reporting.

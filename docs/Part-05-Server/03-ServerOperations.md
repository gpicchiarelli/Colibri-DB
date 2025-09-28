# Capitolo 20 — Operazioni Server, Fault Tolerance e Manutenzione

## 20.1 Configurazione runtime
- `ServerConfig`: parametri di listener, sicurezza, pooling.
- Hot-reload configurazioni (TODO).

## 20.2 Gestione errori
- Tipologie di errori server, traduzione in messaggi client.
- Logging structured e alerting.

## 20.3 Fault tolerance
- Comportamento su crash: integrazione col WAL.
- Ridondanza, replicazione (roadmap).

## 20.4 Manutenzione
- Comandi amministrativi (`\vacuum`, `\checkpoint`, `\stats`).
- Metriche esposte e monitoraggio.

## 20.5 Scalabilità distribuita
- Connection pooling esterno, load balancer.
- Pianificazione per clustering e sharding.

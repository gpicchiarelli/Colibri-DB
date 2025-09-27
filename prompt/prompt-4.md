# ColibrìDB — Politiche di Ottimizzazione e Clustering

Questo documento descrive le **politiche automatiche e manuali** che ColibrìDB deve adottare per decidere **quando e come avviare sessioni di ordinamento/clustering**, ricostruzione indici e ottimizzazione dei dati.

---

## 1. Obiettivi delle politiche
- Ridurre **frammentazione** di tabelle e indici.  
- Migliorare prestazioni di **range query**, **join**, **scansioni sequenziali**.  
- Minimizzare l’impatto sui carichi OLTP interattivi.  
- Automatizzare il processo mantenendo **controllo amministrativo** via CLI `coldb`.  

---

## 2. Tipologie di politiche

### 2.1 Time-based (finestre pianificate)
- Politiche basate su **fasce orarie** (es. notte, weekend) per eseguire ottimizzazioni.  
- Definite in una tabella di sistema (`colibridb.conf`) o via CLI:  
  ```
  \policy add time-window <table> [BY <col1,...>] WINDOW <hh:mm-hh:mm>
  ```

### 2.2 Load-based (soglie dinamiche)
- Trigger automatico quando il sistema rileva **carico basso**:  
  - QPS/TPS sotto soglia configurabile.  
  - CPU < X% per N secondi.  
  - I/O NVMe < Y MB/s.  
- CLI:
  ```
  \policy add load-threshold <table> [BY <col>] THRESHOLD <qps=X, cpu=Y%>
  ```

### 2.3 Usage-based (statistiche query)
- Analisi dei piani di esecuzione raccolti (query plan cache).  
- Identificazione delle colonne **più usate in predicati** (`WHERE`, `JOIN`, `ORDER BY`).  
- Ranking delle colonne candidate per clustering.  
- CLI:
  ```
  \policy suggest clustering <table>
  ```

### 2.4 Fragmentation-based
- Monitoraggio della **frammentazione indici** e **percentuale di spazio libero** nelle pagine.  
- Trigger quando soglie superate (es. frammentazione > 30%).  
- CLI:
  ```
  \policy add fragmentation <table> [INDEX <name>] THRESHOLD <percent>
  ```

---

## 3. Algoritmi e simulatore di costo

### 3.1 Simulatore costi
Prima di eseguire un job di ottimizzazione, ColibrìDB deve stimare:
- **Tempo previsto** (stimato da I/O sequenziale, memoria disponibile, dimensione tabella).  
- **Spazio temporaneo richiesto**.  
- **Beneficio atteso** (riduzione frammentazione, miglioramento stimato latenza query).  

CLI:
```
\optimize simulate <table> [BY <col1,...>] [INDEX <name>]
```

### 3.2 Decisione automatica
- Se beneficio stimato > costo (soglia configurabile), avvia il job.  
- Altrimenti, registra raccomandazione e logga motivo del non avvio.  

---

## 4. Priorità e scheduling
- Politiche possono avere **priorità** (alta, media, bassa).  
- Scheduler ibrido: combina finestre temporali, soglie carico e frammentazione.  
- Evitare overlap di più job sullo stesso oggetto; supporto a job concorrenti su tabelle diverse.  

---

## 5. Telemetria e auditing
- Ogni job deve registrare: motivo del trigger (time/load/usage/fragmentation), parametri, stima vs risultato reale.  
- Dati storici conservati per N giorni per migliorare suggerimenti futuri.  
- CLI:
  ```
  \policy list
  \policy history <table>
  \policy remove <id>
  ```

---

## 6. Sicurezza e atomicità
- Job scrive sempre su **segmenti nuovi**, con swap atomico al termine.  
- WAL/checkpoint aggiornati per garantire recovery anche se il job viene interrotto.  
- Possibilità di **rollback** manuale (`\optimize cancel <jobId>`).  

---

## 7. Configurazione in `colibridb.conf`
Esempio:
```yaml
policies:
  - type: time-window
    table: orders
    columns: [order_date]
    window: "02:00-05:00"
  - type: load-threshold
    table: logs
    threshold:
      qps: 100
      cpu: 20%
```

---

## 8. Criteri di accettazione
- Politiche attivabili/disattivabili via CLI e config file.  
- Simulatore di costo sempre disponibile prima del lancio.  
- Telemetria storica accessibile via CLI.  
- Nessun impatto su consistenza o sicurezza dei dati.  
- Job interrotti gestiti con rollback sicuro.  

---

### Conclusione
Le politiche di ottimizzazione/clustering di ColibrìDB garantiscono un sistema **autonomo ma controllabile**, in grado di mantenere **prestazioni stabili** anche su dataset grandi, adattandosi dinamicamente a carichi variabili e sfruttando periodi di inattività per lavori di manutenzione ottimizzati.

# Sicurezza by design

ColibrìDB privilegia integrità e durabilità dei dati, preparando il terreno per cifratura e auditing avanzato.

## Integrità & durabilità
- **Checksum**: CRC32 su tutte le pagine WAL/indice (software oggi, hardware ARMv8 in roadmap) e `pageLSN` per rilevare scritture parziali.
- **Sync**: `FileHandle.synchronize()` dopo ogni record WAL e flush espliciti (`flushPage`, `flushAll`, `checkpoint`). Su macOS è possibile abilitare `F_FULLFSYNC` nel futuro per garanzie massime.
- **WAL**: formati versionati, CRC convalidato in recovery; redo/undo ARIES evitano replay parziali.

## Controllo accessi (roadmap)
- Catalogo ruoli/permessi già predisposto (`SystemCatalog.registerRole`), ma autenticazione/autorizzazione sono ancora da implementare.
- Pianificata integrazione con Keychain/Secure Enclave per gestione sicura delle credenziali.

## Cifratura (roadmap)
- Cifratura a riposo con AES-GCM via CryptoKit, chiavi rotabili, supporto a backup cifrati.
- Cifratura in transito quando sarà introdotto il server remoto (TLS/Network.framework).

## Audit & logging
- CLI e policy generano eventi testuali; roadmap: audit log append-only e integrazione con Unified Logging (`os_log`).
- Metriche Prometheus e telemetria permettono rilevamento anomalie (spikes I/O, vacuum ripetuti, ecc.).

## Resilienza operativa
- Compattazione e rebuild lavorano su segmenti nuovi con swap atomico, permettendo rollback in caso di errori.
- Fault injector (`\fault set`) consente test mirati per verificare la robustezza in presenza di errori di I/O.

## Obiettivi futuri
- Row Level Security (RLS), mascheramento dati sensibili e audit trailing completo.
- Integrazione con sistemi di compliance (GDPR, audit log esterni, EndpointSecurity API su macOS).

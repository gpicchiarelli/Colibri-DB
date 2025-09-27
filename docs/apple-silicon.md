# Ottimizzazioni Apple Silicon & APFS

ColibrìDB nasce su hardware Apple; molte scelte di implementazione mirano a sfruttare caratteristiche specifiche di macOS/Apple Silicon.

## CPU & Scheduling
- Swift Concurrency e actor isolation per distribuire il lavoro tra P-core (query) ed E-core (manutenzione I/O).
- Pianificazione del vacuum e del flusher su queue dedicate per evitare interferenze con il percorso OLTP.
- Uso previsto di `QoS` e `DispatchSource` per bilanciare throughput/latency.
- Il buffer pool può essere configurato via `bufferFlushQoS` per assegnare un QoS specifico alle queue di flush.

## I/O & APFS
- Heap/indici sono file regolari su APFS, con scritture sequenziali per WAL/checkpoint.
- Abilitando `ioSequentialReadHint` vengono applicati `F_RDAHEAD`, `posix_fadvise` e prefetch `preadv`/`preadv2` su scan heap, rebuild indici e replay WAL.
- Snapshot/cloni APFS previsti per implementare `\backup` quasi istantanei (copy-on-write) e PITR.
- Il WAL supporta `F_FULLFSYNC` opzionale (`walFullFSyncEnabled` in config) anche per i log degli indici; i comandi `\flush ... fullsync` sfruttano lo stesso percorso per forzare la persistenza su heap/indici e, con `walCompression`, puoi scegliere `lzfse` (accelerata) o `zlib` per ridurre I/O.

## Accelerazione hardware
- CRC32 ARMv8 intrinseco ora usato via intrinsics `__crc32*` per ridurre l'overhead dei checksum WAL/pagine.
- `Accelerate/vDSP` e NEON per operatori vettoriali, hashing e scansioni future.
- CryptoKit + Secure Enclave per cifratura e gestione chiavi quando la sicurezza sarà implementata.

## Profiling e osservabilità
- Integrazione con `os_log`/`signpost` e Instruments per analisi runtime (Time Profiler, System Trace, Allocations, I/O).
- Unified Logging (`OSLogStore`) e DTrace per investigare contesa lock e syscalls (roadmap).
- Per linee guida dettagliate su baseline e strumenti consultare anche `docs/performance.md`.

## Energia e termica
- Obiettivo: mantenere throughput elevato limitando lo scaling termico; politiche di flush/vacuum evitano burst eccessivi.
- Supporto futuro a profili low-power (Throttle vacuum/compaction) per laptop.

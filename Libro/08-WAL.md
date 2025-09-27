08 — WAL e Recovery
===================

Obiettivi
---------
Durabilità ARIES-like con record tipizzati, checksum, `pageLSN` e checkpoint.

Componenti
----------
- `WAL/FileWAL.swift` — append/flush, record begin/commit, insert pre/done, delete, CLR, checkpoint e replay.
- `Util/CRC32.swift` e `CRC32Accelerator/` — checksum hardware-accelerato.

Redo/Undo
---------
Redo guidato da `pageLSN` nelle pagine; undo con CLR per operazioni parziali durante `rollback`.


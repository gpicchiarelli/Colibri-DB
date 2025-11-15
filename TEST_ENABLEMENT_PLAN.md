# Piano per Abilitare TUTTI i Test

## 🎯 Obiettivo
Far passare **TUTTI** i test, inclusi i 35+ attualmente disabilitati.

## 📊 Situazione Attuale

### Test Attivi
- ✅ BasicCompilationTests: 2/2
- ✅ DatabaseIntegrationTests: 4/4
- ✅ MVCCManagerTests: 3/3
- ⚠️ RecoveryIntegrationTests: 5/5 (2 skip per toolchain)
- **Totale: 14 test passing**

### Test Disabilitati (da riattivare)

#### 1. WALCrashCampaignTests.swift.wip
**Motivo disabilitazione**: Actor isolation - WALManager API changes
**Errori**:
- `getCurrentLSN()` non accessibile da fuori actor
- `getWALRecord()` non accessibile da fuori actor
- DiskManager mock non conforme a protocol

**Fix necessario**:
```swift
// Aggiungere metodi pubblici in WALManager
public func getCurrentLSNForTest() async -> LSN {
    return await getCurrentLSN()
}

public func getWALRecordForTest(lsn: LSN) async throws -> WALRecord {
    return try await getWALRecord(lsn: lsn)
}

// Aggiornare TestDiskManager
final class TestDiskManager: DiskManager {
    func readPage(pageID: PageID) async throws -> Data { ... }
    func writePage(pageID: PageID, data: Data) async throws { ... }
    func deletePage(pageID: PageID) async throws { ... }
}
```
**Tempo**: 45-60 min

#### 2. MVCCPropertyTests.swift.wip
**Motivo disabilitazione**: API mismatch - MVCCManager methods
**Errori**:
- `commitTransaction()` non trovato (ora esiste)
- `abortTransaction()` non trovato (ora esiste)
- `garbageCollect()` non trovato (ora esiste)

**Fix necessario**: Già fixato! Solo ri-abilitare
**Tempo**: 5 min

#### 3. IndexConformanceTests.swift.wip
**Motivo disabilitazione**: Index API evolution
**Errori**:
- IndexProtocol non trovato
- Index wrappers non conformi
- Manca await per actor calls

**Fix necessario**:
```swift
// Re-enable IndexWrappers.swift
// Aggiungere await per tutte le chiamate agli index wrapper actors
let btreeWrapper = await BTreeIndexWrapper(btree)
try await btreeWrapper.insert(key: key, rid: rid)
```
**Tempo**: 30-45 min

#### 4. EndToEndIntegrationTests.swift.wip
**Motivo disabilitazione**: API evolution
**Errori**:
- `Key("...")` needs `Key(stringLiteral: "...")`
- `TransactionManager` init (già fixato con makeForTesting)
- `Value` construction (già fixato)

**Fix necessario**: Già quasi fixato! Aggiornare chiamate Key
**Tempo**: 15-20 min

#### 5. Testing Framework Tests (35 file .disabled)

**Files**:
- MinimalTest.swift
- BTreeIndexTests.swift
- BufferPoolTests.swift
- WALTests.swift
- TransactionManagerTests.swift
- RecoveryTests.swift
- SecurityTests.swift
- AuthenticationTests.swift
- PerformanceTests.swift
- ChaosEngineeringTests.swift
- StressTests.swift
- DatabaseTests.swift
- IntegrationTests.swift
- DistributedTests.swift
- SQLParserTests.swift
- VACUUMTests.swift
- IndexSubsystemTests.swift
- QueryOptimizerTests.swift
- StatisticsMaintenanceTests.swift
- MultiDatabaseCatalogTests.swift
- ... (altri 15)

**Motivo disabilitazione**: Conflitto con Testing framework
**Errore comune**: `missing required module '_TestingInternals'`

**Fix necessario**:
1. **Opzione A**: Rimuovere tutti `import Testing` e convertire a XCTest
2. **Opzione B**: Configurare correttamente il Testing framework in Package.swift

**Tempo**: 
- Opzione A: 3-4 ore (manuale per ogni file)
- Opzione B: 1-2 ore (se funziona)

---

## 📋 Piano di Azione Prioritizzato

### FASE 1: Quick Wins (1 ora)
1. ✅ MVCCPropertyTests - già fixato, solo enable (5 min)
2. ✅ EndToEndIntegrationTests - quasi fixato (20 min)
3. ✅ WALCrashCampaignTests - aggiungere test helpers (30 min)

### FASE 2: Index Tests (1 ora)
4. ✅ IndexConformanceTests - await calls + enable wrappers (45 min)
5. ✅ Verificare IndexWrappers.swift è abilitato

### FASE 3: Testing Framework (3-4 ore)
6. ⏳ Convertire tutti i 35 test da Testing → XCTest
   - Pattern: `@Test → func test...()` 
   - Pattern: `#expect(...) → XCTAssert...`
   - Pattern: `@Suite → class ...Tests: XCTestCase`

### FASE 4: Validation (1 ora)
7. ✅ Run full test suite
8. ✅ Verificare coverage
9. ✅ Fixare remaining failures

---

## 🔧 Fix Tecnici Specifici

### 1. Actor Isolation (WAL, MVCC)
```swift
// Pattern: Aggiungere metodi di test pubblici
public actor WALManager {
    // Metodo esistente (internal/private)
    func getCurrentLSN() -> LSN { ... }
    
    // Nuovo metodo per test
    public func getCurrentLSNForTest() async -> LSN {
        return getCurrentLSN()
    }
}
```

### 2. Testing → XCTest Conversion
```swift
// PRIMA (Testing framework)
import Testing

@Suite("MyTests")
struct MyTests {
    @Test func myTest() {
        #expect(value == expected)
    }
}

// DOPO (XCTest)
import XCTest

final class MyTests: XCTestCase {
    func testMyTest() {
        XCTAssertEqual(value, expected)
    }
}
```

### 3. Index Protocol Conformance
```swift
// Verificare IndexWrappers.swift è abilitato
// Aggiungere await per actor calls
let wrapper = BTreeIndexWrapper(btree)
try await wrapper.insert(key: key, rid: rid)
let results = try await wrapper.seek(key: key)
```

### 4. Key/Value String Literals
```swift
// PRIMA
let key = Key("user:1")

// DOPO
let key = Key(stringLiteral: "user:1")
// O meglio, verificare ExpressibleByStringLiteral conformance
```

---

## 📈 Metriche Obiettivo

### Coverage Target
- **Attuale**: ~14 test attivi
- **Target**: 49+ test attivi (14 + 35 disabilitati)
- **Coverage**: 80%+ line coverage

### Exit Criteria
- ✅ 0 test disabilitati
- ✅ 0 test skipped (eccetto toolchain issues)
- ✅ 100% test passing
- ✅ Build green in release mode
- ✅ No warnings critici

---

## ⏱️ Tempo Totale Stimato

| Fase | Durata | Priorità |
|------|--------|----------|
| FASE 1: Quick Wins | 1 ora | 🔴 ALTA |
| FASE 2: Index Tests | 1 ora | 🟡 MEDIA |
| FASE 3: Testing Framework | 3-4 ore | 🟢 BASSA |
| FASE 4: Validation | 1 ora | 🔴 ALTA |
| **TOTALE** | **6-7 ore** | |

---

## 🚀 Prossima Azione

**INIZIARE CON FASE 1 - QUICK WINS**

1. Re-enable MVCCPropertyTests (già fixato)
2. Fix EndToEndIntegrationTests (Key string literals)
3. Add WALManager test helpers
4. Run tests e verificare progress

**Comando per iniziare**:
```bash
# 1. Enable MVCCPropertyTests
mv Tests/ColibriCoreTests/MVCCPropertyTests.swift.wip \
   Tests/ColibriCoreTests/MVCCPropertyTests.swift

# 2. Build and test
swift test

# 3. Fix errors iterativamente
```

---

## 🎯 Conclusione

**Cosa manca per far passare TUTTI i test**:

1. **Immediate (1-2 ore)**: 
   - Re-enable 4 test .wip (già quasi fixati)
   - Aggiungere test helper methods per actor isolation

2. **Short-term (3-4 ore)**:
   - Convertire 35 test da Testing framework → XCTest

3. **Validation (1 ora)**:
   - Run full suite
   - Fix remaining issues
   - Verificare 100% passing

**Totale: 6-7 ore di lavoro concentrato per 100% test enabled e passing.**

Vuoi che proceda con FASE 1 (Quick Wins)?






# ✅ Checklist Deployment GitHub Actions CI/CD

## 📋 Pre-Commit Checklist

### ✅ Verifica File Installati

- [x] **FASE 1 - CI Foundation (6 files)**
  - [x] `.github/workflows/ci.yml` - Workflow CI principale
  - [x] `rules/perf_baseline.json` - Performance baselines
  - [x] `rules/coverage_targets.json` - Coverage targets
  - [x] `tools/scripts/perf_guard.py` - Performance validator
  - [x] `tools/scripts/docs_guard.py` - Documentation enforcer
  - [x] `tools/scripts/coverage_guard.swift` - Coverage validator

- [x] **FASE 2 - Formal Verification (3 files)**
  - [x] `.github/workflows/spec.yml` - TLA+ verification workflow
  - [x] `rules/tla_modules.json` - TLA+ modules config
  - [x] `tools/scripts/tla_trace_check.py` - Trace validator

- [x] **FASE 3 - Benchmarks & Release (3 files)**
  - [x] `.github/workflows/nightly.yml` - Nightly benchmarks
  - [x] `.github/workflows/release.yml` - Release automation
  - [x] `tools/scripts/bench_json.sh` - Benchmark JSON converter

- [x] **FASE 4 - Developer Experience (6 files)**
  - [x] `.github/workflows/labeler.yml` - Auto-labeling workflow
  - [x] `.github/labeler.yml` - Labeler configuration
  - [x] `.github/CODEOWNERS` - Code ownership
  - [x] `.github/pull_request_template.md` - PR template
  - [x] `.github/ISSUE_TEMPLATE/bug.yml` - Bug report form
  - [x] `.github/ISSUE_TEMPLATE/feature.yml` - Feature request form

- [x] **FASE 5 - Maintenance & Docs (2 files)**
  - [x] `.github/dependabot.yml` - Dependency auto-update
  - [x] `.github/README.md` - CI/CD documentation

**TOTALE:** 20 files ✅

### ✅ Verifica Permessi Script

```bash
# Tutti gli script devono essere eseguibili
ls -l tools/scripts/
```

Verifica che tutti i file abbiano permesso `x`:
- [x] `perf_guard.py` - rwxr-xr-x
- [x] `docs_guard.py` - rwxr-xr-x
- [x] `coverage_guard.swift` - rwxr-xr-x
- [x] `tla_trace_check.py` - rwxr-xr-x
- [x] `bench_json.sh` - rwxr-xr-x

---

## 🚀 Deployment Steps

### Step 1: Review Files

```bash
# Controlla tutti i file creati
git status

# Dovrai vedere:
# - .github/ (nuovi file)
# - rules/ (nuovi file)
# - tools/scripts/ (nuovi file)
```

- [ ] File presenti in staging
- [ ] Nessun file indesiderato

### Step 2: Commit Changes

```bash
git add .github/
git add rules/
git add tools/scripts/

# Verifica cosa stai committando
git status

git commit -m "ci: add complete GitHub Actions CI/CD system

Implemented military-grade CI/CD with comprehensive quality gates:

✅ Workflows (5):
- ci.yml: Build, test, coverage, perf, docs, security
- spec.yml: TLA+ formal verification
- nightly.yml: Full benchmarks and stability tests
- release.yml: Automated releases with SBOM
- labeler.yml: Auto-labeling PRs

✅ Quality Gates:
- Coverage: 75-95% based on module criticality
- Performance: max 5-15% degradation allowed
- Documentation: mandatory for critical modules
- Security: Trivy scanner + hardened runners
- Formal verification: 6 TLA+ modules

✅ Baselines (3):
- Performance baselines (p50/p95/p99)
- Coverage targets per module
- TLA+ module configurations

✅ Scripts (5):
- Performance guard (Python)
- Documentation guard (Python)
- Coverage guard (Swift)
- TLA+ trace checker (Python)
- Benchmark JSON converter (Bash)

✅ Developer Experience (6):
- Auto-labeling (30+ labels)
- Code ownership
- Structured PR/Issue templates
- Dependabot auto-updates

All workflows optimized for GitHub Free tier.
Security hardened with step-security/harden-runner.

Docs: .github/README.md, CI_CD_DEPLOYMENT_GUIDE.md"
```

- [ ] Commit eseguito
- [ ] Commit message descrittivo

### Step 3: Push to Remote

```bash
# Push al branch develop
git push origin develop
```

- [ ] Push completato senza errori

### Step 4: Verify on GitHub

1. **Vai su GitHub Repository**
   - [ ] `.github/workflows/` contiene 5 file
   - [ ] Vai su "Actions" tab
   - [ ] Verifica che i workflow siano elencati

2. **Controlla File Visibili**
   - [ ] `.github/CODEOWNERS` visibile
   - [ ] `.github/pull_request_template.md` visibile
   - [ ] Issue templates disponibili

---

## 🧪 Testing

### Test 1: Crea PR di Test

```bash
# Crea branch di test
git checkout -b test/verify-ci-system

# Aggiungi file di test
echo "# CI System Test" > CI_TEST.md
git add CI_TEST.md
git commit -m "test: verify CI system is working"

# Push
git push origin test/verify-ci-system
```

**Poi su GitHub:**
1. [ ] Apri Pull Request
2. [ ] Verifica che PR template appaia
3. [ ] Verifica auto-labeling (es. "Documentation" label)
4. [ ] Attendi che workflow CI parta (~2-3 min)

### Test 2: Verifica Workflow CI

**Vai su GitHub → Actions → Workflow run:**

- [ ] **Job 1:** Build & Test (~10 min)
  - [ ] Build completa
  - [ ] Test passano
  - [ ] Coverage generata

- [ ] **Job 2:** Coverage Guard
  - [ ] Scarica artifact coverage
  - [ ] Valida vs targets

- [ ] **Job 3:** Performance Guard
  - [ ] Benchmark eseguiti
  - [ ] Confronto con baseline

- [ ] **Job 4:** Documentation Guard (solo PR)
  - [ ] Controlla docs aggiornate

- [ ] **Job 5:** Lint
  - [ ] SwiftLint passa
  - [ ] SwiftFormat passa

- [ ] **Job 6:** Security
  - [ ] Trivy scan completo

- [ ] **Job 7:** CI Success
  - [ ] Tutti i job verdi ✅

**Tempo totale atteso:** 15-25 minuti

### Test 3: Controlla Artifacts

**Vai su workflow run → Artifacts:**

- [ ] `test-results` - XML test results
- [ ] `coverage-reports` - LCOV, JSON, HTML
- [ ] `benchmark-results` - JSON risultati

**Scarica e verifica:**
```bash
gh run download <run-id>
ls -la
```

### Test 4: Verifica Labeler

**Sulla PR di test:**
- [ ] Almeno 1 label applicata automaticamente
- [ ] Label corrisponde ai file modificati
- [ ] Se modifichi file in `Sources/ColibriCore/Storage/WAL/` → label "WAL"

---

## 🔧 Troubleshooting

### Problema: Workflow non parte

**Possibili cause:**
1. Workflow file non committato correttamente
2. Sintassi YAML errata
3. Branch protection rules

**Soluzione:**
```bash
# Verifica sintassi YAML
yamllint .github/workflows/ci.yml

# Controlla che file sia committato
git log --oneline -n 1 -- .github/workflows/ci.yml
```

### Problema: CI Fails - Coverage Guard

**Causa:** Coverage < target per qualche modulo

**Soluzione:**
1. Scarica coverage HTML artifact
2. Identifica linee non coperte
3. Aggiungi test per quelle linee
4. Ripush

### Problema: CI Fails - Performance Guard

**Causa:** Performance degradata > tolleranza

**Soluzione:**
1. Scarica benchmark artifact
2. Identifica operazione degradata
3. Profila e ottimizza
4. O aggiorna baseline se intenzionale

### Problema: CI Fails - Docs Guard

**Causa:** Moduli critici modificati senza docs update

**Soluzione:**
1. Identifica quale modulo (WAL, MVCC, etc.)
2. Aggiorna docs corrispondente:
   - WAL → `docs/wiki/Part-02-Core-Engine/01-WAL-and-Recovery.md`
   - MVCC → `docs/wiki/Part-02-Core-Engine/05-MVCC-Concurrency.md`
3. Commit e push

---

## 📊 Post-Deployment Verification

### Week 1: Monitor

- [ ] Controlla almeno 3 PR che workflow CI funzioni
- [ ] Verifica che labeler applichi labels corrette
- [ ] Controlla che quality gates funzionino (fail quando dovrebbero)
- [ ] Verifica artifacts vengono generati

### Week 2: Optimize

- [ ] Analizza tempi di esecuzione workflow
- [ ] Verifica cache hit rate (SPM, TLA+ tools)
- [ ] Ottimizza se necessario

### Monthly: Review

- [ ] Review Dependabot PRs (merge se CI verde)
- [ ] Aggiorna baseline se performance migliorate
- [ ] Controlla utilizzo minuti GitHub Actions
- [ ] Review security scan results

---

## 🎯 Success Criteria

### ✅ CI System Funzionante

- [ ] Workflow CI completa in < 30 min
- [ ] Quality gates bloccano PR con problemi
- [ ] Artifacts disponibili per analisi
- [ ] Auto-labeling funziona correttamente
- [ ] Nessun false positive nei quality gates

### ✅ Developer Experience

- [ ] Template PR usato correttamente
- [ ] Issue forms strutturati
- [ ] Feedback rapido su PR (< 30 min)
- [ ] Documentazione chiara e accessibile

### ✅ Release Process

- [ ] Tag → binari automatici
- [ ] SBOM generato
- [ ] Checksums presenti
- [ ] Release notes auto-generate

---

## 📚 Documentation References

| Documento | Scopo |
|-----------|-------|
| `.github/README.md` | Guida completa CI/CD (60+ sezioni) |
| `CI_CD_DEPLOYMENT_GUIDE.md` | Deployment guide dettagliata |
| `GITHUB_ACTIONS_SUMMARY.md` | Quick reference |
| `CHECKLIST_DEPLOYMENT.md` | Questo documento |

---

## 🎉 Deployment Complete!

Quando tutti gli step sono completati:

- [ ] Tutti i file committati e pushati
- [ ] PR di test creata e CI verde
- [ ] Artifacts verificati
- [ ] Labeler funzionante
- [ ] Documentazione letta

**🚀 Sistema CI/CD pronto per produzione!**

---

## 📞 Support

**Domande?**
- Leggi `.github/README.md`
- Controlla troubleshooting section
- Apri issue su GitHub

**Contributi benvenuti!**
- PR per miglioramenti CI/CD
- Suggerimenti per ottimizzazioni
- Report di bug nei workflow

---

**Last Updated:** 2025-10-18  
**Version:** 1.0.0  
**Status:** ✅ READY FOR PRODUCTION


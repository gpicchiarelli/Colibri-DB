# 🚀 Quick Start - GitHub Actions CI/CD

## ⚡ 3-Minute Setup

### 1️⃣ Commit Files (30 seconds)

```bash
cd /Users/gpicchiarelli/Documents/Colibrì-DB

git add .github/ rules/ tools/scripts/
git commit -m "ci: add GitHub Actions CI/CD system"
git push origin develop
```

### 2️⃣ Open Test PR (1 minute)

```bash
git checkout -b test/ci
echo "# CI Test" > TEST_CI.md
git add TEST_CI.md
git commit -m "test: verify CI"
git push origin test/ci
```

Then on GitHub: Open Pull Request

### 3️⃣ Wait & Verify (20 minutes)

- ✅ CI workflow starts automatically
- ✅ Auto-labels applied to PR
- ✅ All quality gates run
- ✅ Check artifacts when complete

---

## 📋 What You Get

### Quality Gates ✅
- **Coverage:** 75-95% enforcement
- **Performance:** 5-15% degradation detection
- **Documentation:** Critical modules enforcement
- **Security:** Trivy vulnerability scan
- **Linting:** SwiftLint + SwiftFormat

### Workflows 🔄
- **CI:** Build, test, quality gates (~20 min)
- **Spec:** TLA+ formal verification (~25 min)
- **Nightly:** Full benchmarks (daily @ 01:00 UTC)
- **Release:** Auto-build on git tags
- **Labeler:** Auto-label PRs

### Artifacts 📦
- Test results (XML)
- Coverage reports (LCOV, JSON, HTML)
- Benchmark results (JSON)
- Build logs (on failure)

---

## 🎯 Daily Usage

### For Contributors

**Create PR:**
```bash
git checkout -b feature/my-feature
# make changes
git commit -m "feat: add feature"
git push origin feature/my-feature
# Open PR on GitHub (template auto-fills)
```

**CI runs automatically:**
- Build & Test
- Coverage check
- Performance check
- Docs check (if critical files)
- Lint & Format
- Security scan

**If CI fails:**
- Download artifacts
- Fix issues
- Push again

### For Maintainers

**Review PR:**
1. Check CI is green ✅
2. Review code changes
3. Check coverage reports (artifacts)
4. Approve & merge

**Create Release:**
```bash
git tag -a v1.0.0 -m "Release 1.0.0"
git push origin v1.0.0
# Release workflow auto-runs
# Check GitHub Releases for binaries
```

---

## 📊 Key Files

| File | Purpose |
|------|---------|
| `.github/workflows/ci.yml` | Main CI pipeline |
| `.github/README.md` | Complete documentation |
| `rules/perf_baseline.json` | Performance targets |
| `rules/coverage_targets.json` | Coverage targets |

---

## 🔧 Local Testing

```bash
# Coverage
swift test --enable-code-coverage
swift tools/scripts/coverage_guard.swift \
  .build/coverage.json rules/coverage_targets.json

# Performance
.build/release/benchmarks --quick > bench.txt
bash tools/scripts/bench_json.sh bench.txt bench.json
python3 tools/scripts/perf_guard.py \
  bench.json rules/perf_baseline.json

# Docs
git diff --name-only origin/main > changed.txt
python3 tools/scripts/docs_guard.py changed.txt

# Lint
swiftlint lint --config Configuration/swiftlint.yml
swiftformat --config Configuration/swiftformat.yml --lint .
```

---

## 🆘 Quick Troubleshooting

### CI Fails - Coverage
➡️ Add tests for uncovered lines

### CI Fails - Performance
➡️ Optimize or update baseline

### CI Fails - Docs
➡️ Update docs in `docs/wiki/`

### CI Fails - Lint
➡️ Run `swiftlint autocorrect` and `swiftformat .`

---

## 📚 Full Documentation

- **Complete Guide:** `.github/README.md`
- **Deployment:** `CI_CD_DEPLOYMENT_GUIDE.md`
- **Checklist:** `CHECKLIST_DEPLOYMENT.md`

---

## ✅ Success Checklist

- [ ] Files committed and pushed
- [ ] Test PR created
- [ ] CI runs and passes
- [ ] Artifacts generated
- [ ] Auto-labeling works

**Done?** System is ready! 🎉

---

**Questions?** Read `.github/README.md` or open an issue.


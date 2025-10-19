# GitHub Actions CI/CD for ColibrìDB

This directory contains the complete CI/CD infrastructure for ColibrìDB, implementing a "military-grade" quality assurance system with multiple quality gates.

## 📁 Directory Structure

```
.github/
├── workflows/           # GitHub Actions workflows
│   ├── ci.yml          # Main CI pipeline (build, test, quality gates)
│   ├── spec.yml        # Formal verification (TLA+ specs)
│   ├── nightly.yml     # Nightly benchmarks and stability tests
│   ├── release.yml     # Release automation
│   └── labeler.yml     # Auto-labeling PRs
├── ISSUE_TEMPLATE/     # Issue templates
│   ├── bug.yml         # Bug report form
│   └── feature.yml     # Feature request form
├── labeler.yml         # Label configuration
├── CODEOWNERS          # Code ownership assignments
├── pull_request_template.md  # PR template
└── README.md           # This file
```

## 🔄 Workflows

### 1. CI Workflow (`ci.yml`)

**Triggers:** Push to `main`/`develop`, Pull Requests

Main continuous integration pipeline with comprehensive quality gates.

#### Jobs:

- **Build & Test**
  - Build in Debug configuration
  - Run test suite with coverage
  - Generate coverage reports (LCOV, JSON, HTML)
  - Upload test results and coverage artifacts

- **Coverage Guard** ⚠️
  - Validates coverage meets module-specific targets
  - Enforces 90%+ coverage for critical modules (WAL, MVCC, BTree)
  - Blocks PR if coverage below minimum thresholds

- **Performance Guard** ⚡
  - Runs quick performance benchmarks
  - Compares against baseline (`rules/perf_baseline.json`)
  - Blocks PR if performance degrades > tolerance (5% p50, 10% p95)

- **Documentation Guard** 📚
  - Checks if critical modules modified without docs updates
  - Enforces documentation for WAL, MVCC, Lock Manager changes
  - Triggered only on PRs

- **Lint & Format**
  - SwiftLint with strict mode
  - SwiftFormat validation
  - No warnings tolerated

- **Security Scan** 🔒
  - Trivy security scanner
  - SARIF upload to GitHub Security

**Quality Gates:**
- ✅ All tests must pass
- ✅ Coverage must meet targets
- ✅ Performance within tolerance
- ✅ Docs updated for critical changes
- ✅ No linter warnings
- ✅ No security vulnerabilities

**Typical Runtime:** 15-20 minutes

---

### 2. Formal Verification Workflow (`spec.yml`)

**Triggers:** Push to specs/, critical source files, or manually

Validates code against TLA+ formal specifications.

#### Jobs:

- **TLA+ Model Checking**
  - Runs TLC model checker on all modules
  - Matrix strategy: WAL, MVCC, LockManager, BTree, TransactionManager, BufferPool
  - Verifies invariants hold for all executions
  - Checks for deadlocks in concurrent algorithms

- **Trace Validation**
  - Validates test execution traces against TLA+ specs
  - Ensures runtime behavior matches formal model
  - Connects testing to formal verification

- **Specification Coverage**
  - Reports which modules have formal specs
  - Tracks coverage of formal verification

**Invariants Checked:**
- **WAL:** Durability, log order, checkpoint consistency
- **MVCC:** Snapshot isolation, serializability, no write-write conflicts
- **LockManager:** No deadlocks, lock compatibility, fairness
- **BTree:** Structure invariant, key order, balanced height
- **TransactionManager:** ACID properties

**Typical Runtime:** 20-30 minutes

---

### 3. Nightly Workflow (`nightly.yml`)

**Triggers:** Scheduled (01:00 UTC daily), Manual dispatch

Comprehensive nightly testing and benchmarking.

#### Jobs:

- **Full Benchmark Suite** 📊
  - Complete performance benchmarks (60-90 minutes)
  - Stress tests (10 minutes high load)
  - Generates JSON results and performance reports
  - Compares with baseline (informational, non-blocking)

- **Memory Profiling** 🔍
  - Build with Address Sanitizer (ASAN)
  - Build with Thread Sanitizer (TSAN)
  - Detects memory leaks and race conditions

- **4-Hour Stability Test** 🏋️
  - Long-running continuous load test
  - Validates stability under sustained operation
  - Detects memory leaks, crashes, performance degradation

**Artifacts:**
- Benchmark results (JSON + raw text)
- Performance reports (markdown)
- Sanitizer reports
- Stability logs

**Retention:** 90 days for benchmarks, 30 days for others

**Typical Runtime:** 4-5 hours

---

### 4. Release Workflow (`release.yml`)

**Triggers:** Git tags (`v*.*.*`), Manual dispatch

Automated release process with binary builds.

#### Jobs:

- **Create Release**
  - Generates changelog from CHANGELOG.md or git log
  - Creates GitHub release (draft/prerelease based on version)

- **Build Binaries**
  - Builds for macOS x86_64 and arm64
  - Creates installation packages with docs and config
  - Generates SHA256 checksums
  - Release-optimized builds

- **Generate SBOM**
  - Software Bill of Materials in multiple formats
  - JSON, SPDX, CycloneDX
  - Supply chain security

- **Validate Release**
  - Tests installation packages
  - Verifies checksums

**Artifacts:**
- `colibridb-v*.*.*.tar.gz` (per architecture)
- SHA256 checksums
- SBOM files
- Installation scripts

**Typical Runtime:** 30-40 minutes

---

### 5. Labeler Workflow (`labeler.yml`)

**Triggers:** PR opened, synchronized, reopened

Automatically labels PRs based on changed files.

**Labels Applied:**
- Component labels: WAL, MVCC, BTree, Indexes, Storage, Query, etc.
- Type labels: Bug Fix, Feature, Refactoring, Documentation
- Severity labels: Critical, Breaking Change
- Context labels: Tests, Benchmarks, CI/CD, Configuration

**Benefits:**
- Easier PR filtering and organization
- Automatic routing to right reviewers (via CODEOWNERS)
- Better project insights and statistics

---

## 🛡️ Quality Gates

### Coverage Targets (`rules/coverage_targets.json`)

| Module | Minimum | Target | Rationale |
|--------|---------|--------|-----------|
| WAL | 95% | 98% | Critical for durability |
| MVCC | 90% | 95% | Critical for correctness |
| Lock Manager | 90% | 95% | Critical for concurrency |
| B-Tree | 90% | 95% | Critical for performance |
| Pager | 85% | 90% | Core storage |
| Query Engine | 80% | 85% | Complex logic |
| Default | 75% | 85% | Other modules |

### Performance Baselines (`rules/perf_baseline.json`)

**Tolerance Levels:**
- p50: 5% degradation allowed
- p95: 10% degradation allowed  
- p99: 15% degradation allowed

**Key Operations:**
- WAL append: p50=100μs, p95=250μs, p99=500μs
- BTree search: p50=50μs, p95=150μs, p99=300μs
- MVCC txn begin: p50=20μs, p95=50μs, p99=100μs

### TLA+ Modules (`rules/tla_modules.json`)

**Formal Specifications:**
- ✅ WAL: Durability and recovery
- ✅ MVCC: Snapshot isolation
- ✅ LockManager: Deadlock freedom
- ✅ BTree: Structure invariants
- ✅ TransactionManager: ACID properties
- ✅ BufferPool: Cache consistency

---

## 🧰 Supporting Tools

### Scripts (`tools/scripts/`)

1. **`perf_guard.py`**
   - Validates benchmark results against baselines
   - Python script, exit code 0/1
   - Detailed reporting with colors

2. **`docs_guard.py`**
   - Checks docs updated for critical module changes
   - Maps source files → documentation files
   - Enforces documentation quality

3. **`coverage_guard.swift`**
   - Parses llvm-cov JSON output
   - Validates against module-specific targets
   - Native Swift script

4. **`tla_trace_check.py`**
   - Converts test traces to TLA+ format
   - Runs TLC model checker
   - Validates runtime behavior against specs

5. **`bench_json.sh`**
   - Converts raw benchmark output to JSON
   - Structured format for perf_guard
   - Bash script with validation

---

## 🔒 Security Hardening

All workflows use `step-security/harden-runner@v2`:
- Audit mode for egress policy
- Disable sudo where not needed
- Monitor file system access
- Network access restrictions

**Fork Protection:**
- Sensitive workflows only run on owner's repo
- Secrets not exposed to forks
- Manual approval for external PRs

---

## 📊 Artifacts & Retention

| Artifact | Retention | Size Estimate |
|----------|-----------|---------------|
| Test results | 30 days | ~10 MB |
| Coverage reports | 30 days | ~50 MB |
| Benchmark results | 90 days | ~5 MB |
| Build logs | 7 days | ~20 MB |
| Nightly benchmarks | 90 days | ~20 MB |
| Release binaries | Permanent | ~50 MB |

---

## 🚀 Usage Guide

### For Contributors

1. **Creating a PR:**
   - Fill out PR template completely
   - Ensure all checkboxes are addressed
   - Wait for CI to complete (~20 minutes)
   - Address any quality gate failures

2. **Quality Gate Failures:**
   - **Coverage:** Add tests to meet targets
   - **Performance:** Investigate regression, optimize if needed
   - **Docs:** Update relevant documentation
   - **Linter:** Run `swiftlint autocorrect` and `swiftformat .`

3. **Getting Help:**
   - Check logs in GitHub Actions UI
   - Review artifacts for detailed reports
   - Ask in PR comments if stuck

### For Maintainers

1. **Reviewing PRs:**
   - Check that all CI jobs pass
   - Review coverage report artifacts
   - Validate performance impact
   - Verify docs updated for critical changes

2. **Releases:**
   - Create git tag: `git tag -a v1.0.0 -m "Release 1.0.0"`
   - Push tag: `git push origin v1.0.0`
   - Release workflow runs automatically
   - Verify artifacts in GitHub release

3. **Updating Baselines:**
   - Performance improvements: Update `rules/perf_baseline.json`
   - Coverage improvements: Update `rules/coverage_targets.json`
   - Commit changes to repository

---

## 🐛 Troubleshooting

### CI Fails on Coverage

**Problem:** Coverage below minimum target

**Solution:**
1. Download coverage HTML artifact
2. Identify uncovered lines
3. Add tests for uncovered paths
4. Run locally: `swift test --enable-code-coverage`

### CI Fails on Performance

**Problem:** Performance degraded beyond tolerance

**Solution:**
1. Download benchmark results artifact
2. Compare with baseline
3. Profile the affected operation
4. Optimize or justify regression in PR description

### TLA+ Check Fails

**Problem:** Invariant violation detected

**Solution:**
1. Review TLC counterexample in logs
2. Fix algorithmic issue in code
3. Or update TLA+ spec if model was incorrect

### Workflow Won't Run

**Problem:** Workflow not triggering

**Solution:**
- Check workflow triggers in YAML
- Verify branch protection rules
- Ensure file paths match trigger patterns
- Check if workflow is disabled

---

## 📈 Metrics & Monitoring

**GitHub Insights:**
- CI success rate by workflow
- Average runtime per job
- Failure patterns and trends

**Useful Queries:**
```bash
# Show all workflows
gh workflow list

# View recent CI runs
gh run list --workflow=ci.yml

# Download artifacts
gh run download <run-id>
```

---

## 🔮 Future Enhancements

- [ ] Parallel test execution with sharding
- [ ] Incremental builds with more granular caching
- [ ] Performance trend tracking over time
- [ ] Code signing for release binaries
- [ ] Docker image builds and publishing
- [ ] Homebrew formula auto-update
- [ ] Slack/Discord notifications for failures
- [ ] GitHub Packages for library distribution

---

## 📚 Additional Resources

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Swift on GitHub Actions](https://github.com/swift-actions)
- [TLA+ Tools](https://github.com/tlaplus/tlaplus)
- [ColibrìDB Contributing Guide](../CONTRIBUTING.md)
- [ColibrìDB Architecture Docs](../docs/wiki/Architecture.md)

---

## 🤝 Contributing to CI/CD

Improvements to CI/CD infrastructure are welcome!

**Process:**
1. Open an issue describing the improvement
2. Discuss with maintainers
3. Submit PR with workflow changes
4. Test thoroughly before merging
5. Update this README if needed

**Guidelines:**
- Keep workflows fast (< 30 min for CI)
- Optimize caching aggressively
- Document all quality gates
- Maintain security hardening
- Consider free tier usage limits

---

**Questions?** Open an issue or ask in discussions!

**Last Updated:** 2025-10-18

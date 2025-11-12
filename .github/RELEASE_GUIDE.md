# 🚀 ColibrDB Release Guide

Questa guida fornisce informazioni complete sul processo di release di ColibrDB, inclusi versioning, deployment e best practices.

## 📋 Indice
- [Panoramica Release](#panoramica-release)
- [Versioning](#versioning)
- [Processo di Release](#processo-di-release)
- [Deployment](#deployment)
- [Rollback](#rollback)
- [Monitoring](#monitoring)
- [Best Practices](#best-practices)

## 🎯 Panoramica Release

### Filosofia di Release
ColibrDB segue un approccio semver (Semantic Versioning) con release incrementali:

- **Major (X.0.0)**: Breaking changes, architettura significativa
- **Minor (X.Y.0)**: Nuove features, backward compatible
- **Patch (X.Y.Z)**: Bug fixes, miglioramenti performance

### Ciclo di Release
```
Development → Alpha → Beta → Release Candidate → Release
     ↓           ↓        ↓           ↓              ↓
   Feature    Testing   Testing    Final Testing   Production
   Branch     Build     Build      Build           Build
```

## 📊 Versioning

### Schema di Versioning
```
v<major>.<minor>.<patch>[-<prerelease>][+<build>]

Esempi:
- v1.0.0          # Release stabile
- v1.0.0-alpha.1  # Alpha release
- v1.0.0-beta.2   # Beta release
- v1.0.0-rc.1     # Release candidate
- v1.0.0+20241201 # Build specifico
```

### Versioni Attuali
- **Current**: v0.1.0-alpha (MVP)
- **Next**: v0.2.0-beta (Multi-user)
- **Future**: v1.0.0 (Production)

### Changelog
```markdown
# Changelog

## [Unreleased]
### Added
- Nuove funzionalità in sviluppo

### Changed
- Modifiche a funzionalità esistenti

### Fixed
- Bug fixes

### Removed
- Funzionalità rimosse

## [1.0.0] - 2024-12-01
### Added
- Release iniziale
- Supporto completo SQL
- Multi-user support
```

## 🔄 Processo di Release

### 1. Pre-Release Checklist
```bash
# 1. Verifica build
swift build -c release

# 2. Esegui tutti i test
swift test

# 3. Esegui benchmark
swift run benchmarks

# 4. Verifica documentazione
swift run coldb --help

# 5. Test manuale
swift run coldb
```

### 2. Release Alpha
```bash
# 1. Crea branch release
git checkout -b release/v0.2.0-alpha

# 2. Aggiorna versioni
# - Package.swift
# - README.md
# - CHANGELOG.md

# 3. Crea tag
git tag v0.2.0-alpha.1

# 4. Push
git push origin release/v0.2.0-alpha
git push origin v0.2.0-alpha.1

# 5. Crea GitHub Release
gh release create v0.2.0-alpha.1 --title "v0.2.0-alpha.1" --notes "Alpha release with new features"
```

### 3. Release Beta
```bash
# 1. Merge da alpha
git checkout main
git merge release/v0.2.0-alpha

# 2. Crea branch beta
git checkout -b release/v0.2.0-beta

# 3. Aggiorna versioni
# - Package.swift
# - README.md
# - CHANGELOG.md

# 4. Crea tag
git tag v0.2.0-beta.1

# 5. Push e GitHub Release
git push origin release/v0.2.0-beta
git push origin v0.2.0-beta.1
gh release create v0.2.0-beta.1 --title "v0.2.0-beta.1" --notes "Beta release with stability improvements"
```

### 4. Release Candidate
```bash
# 1. Merge da beta
git checkout main
git merge release/v0.2.0-beta

# 2. Crea branch RC
git checkout -b release/v0.2.0-rc

# 3. Aggiorna versioni
# - Package.swift
# - README.md
# - CHANGELOG.md

# 4. Crea tag
git tag v0.2.0-rc.1

# 5. Push e GitHub Release
git push origin release/v0.2.0-rc
git push origin v0.2.0-rc.1
gh release create v0.2.0-rc.1 --title "v0.2.0-rc.1" --notes "Release candidate - final testing"
```

### 5. Release Finale
```bash
# 1. Merge da RC
git checkout main
git merge release/v0.2.0-rc

# 2. Aggiorna versioni finali
# - Package.swift
# - README.md
# - CHANGELOG.md

# 3. Crea tag
git tag v0.2.0

# 4. Push e GitHub Release
git push origin main
git push origin v0.2.0
gh release create v0.2.0 --title "v0.2.0" --notes "Stable release with new features"
```

## 🚀 Deployment

### 1. Build Release
```bash
# Build per diverse architetture
swift build -c release --arch arm64
swift build -c release --arch x86_64

# Crea universal binary
lipo -create .build/release/arm64/coldb .build/release/x86_64/coldb -output coldb-universal
```

### 2. Package Distribution
```bash
# Crea package per distribuzione
tar -czf colibridb-v0.2.0-macos.tar.gz coldb-universal README.md LICENSE

# Crea installer
pkgbuild --root .build/release --identifier com.colibridb.server --version 0.2.0 --install-location /usr/local/bin colibridb.pkg
```

### 3. Homebrew Formula
```ruby
class Colibridb < Formula
  desc "High-performance RDBMS written in Swift"
  homepage "https://github.com/gpicchiarelli/Colibri-DB"
  url "https://github.com/gpicchiarelli/Colibri-DB/releases/download/v0.2.0/colibridb-v0.2.0-macos.tar.gz"
  sha256 "sha256-hash"
  license "BSD-3-Clause"

  depends_on :macos
  depends_on :xcode

  def install
    bin.install "coldb-universal" => "coldb"
    bin.install "coldb-server-universal" => "coldb-server"
  end

  test do
    system "#{bin}/coldb", "--version"
  end
end
```

### 4. Docker Image
```dockerfile
FROM swift:6.0-focal

WORKDIR /app
COPY . .
RUN swift build -c release

EXPOSE 5432
CMD [".build/release/coldb-server"]
```

## 🔄 Rollback

### 1. Rollback Automatico
```bash
# Rollback a versione precedente
git checkout v0.1.0
git tag v0.2.0-rollback
git push origin v0.2.0-rollback

# Crea release di rollback
gh release create v0.2.0-rollback --title "v0.2.0-rollback" --notes "Rollback to stable version"
```

### 2. Rollback Database
```bash
# Backup prima del rollback
swift run coldb --backup --output backup-$(date +%Y%m%d).sql

# Rollback database
swift run coldb --restore --input backup-20241201.sql
```

### 3. Rollback Configurazione
```bash
# Ripristina configurazione precedente
cp colibridb.conf.json.backup colibridb.conf.json

# Riavvia servizi
swift run coldb-server --restart
```

## 📊 Monitoring

### 1. Health Checks
```bash
# Check status database
swift run coldb --status

# Check performance
swift run coldb --metrics

# Check logs
swift run coldb --logs
```

### 2. Performance Monitoring
```bash
# Monitor WAL throughput
swift run coldb --monitor-wal

# Monitor buffer pool
swift run coldb --monitor-buffer

# Monitor transactions
swift run coldb --monitor-transactions
```

### 3. Alerting
```bash
# Setup alerting
swift run coldb --setup-alerts --config alerts.json

# Test alerts
swift run coldb --test-alerts
```

## ✅ Best Practices

### 1. Pre-Release Testing
```bash
# Test completo
swift test --configuration release
swift run benchmarks --configuration release

# Test su diverse piattaforme
swift test --platform macos
swift test --platform linux

# Test di stress
swift run benchmarks --stress-test
```

### 2. Documentazione
```bash
# Aggiorna documentazione
swift run coldb --generate-docs

# Verifica documentazione
swift run coldb --validate-docs
```

### 3. Security
```bash
# Security scan
swift run coldb --security-scan

# Dependency check
swift package show-dependencies
```

### 4. Performance
```bash
# Performance baseline
swift run benchmarks --baseline

# Performance regression test
swift run benchmarks --regression-test
```

### 5. Compatibility
```bash
# Test compatibilità
swift test --swift-version 6.0
swift test --swift-version 6.1
swift test --swift-version 6.0
```

## 🔧 Strumenti di Release

### 1. Release Script
```bash
#!/bin/bash
# release.sh

set -e

VERSION=$1
if [ -z "$VERSION" ]; then
    echo "Usage: ./release.sh <version>"
    exit 1
fi

echo "Releasing version $VERSION"

# Build
swift build -c release

# Test
swift test

# Benchmark
swift run benchmarks

# Tag
git tag v$VERSION
git push origin v$VERSION

# GitHub Release
gh release create v$VERSION --title "v$VERSION" --notes "Release $VERSION"

echo "Release $VERSION completed"
```

### 2. CI/CD Pipeline
```yaml
name: Release
on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    runs-on: macos-latest
    steps:
      - uses: actions/checkout@v4
      - uses: swift-actions/setup-swift@v1
      
      - name: Build
        run: swift build -c release
      
      - name: Test
        run: swift test
      
      - name: Benchmark
        run: swift run benchmarks
      
      - name: Create Release
        uses: actions/create-release@v1
        with:
          tag_name: ${{ github.ref }}
          release_name: ${{ github.ref }}
          draft: false
          prerelease: false
```

### 3. Monitoring Dashboard
```bash
# Setup monitoring
swift run coldb --setup-monitoring

# View dashboard
swift run coldb --dashboard
```

---

Questa guida fornisce le basi per gestire il processo di release di ColibrDB. Per domande specifiche, consulta la documentazione tecnica o apri una discussione su GitHub.

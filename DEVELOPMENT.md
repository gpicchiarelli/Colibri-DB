# ColibrìDB Development Environment

## Overview

This document describes the comprehensive development and testing environment for ColibrìDB. The system provides automated development loops, comprehensive testing, performance benchmarking, telemetry collection, and detailed reporting.

## Quick Start

### 1. Setup Development Environment

```bash
# Setup the complete development environment
make dev-setup

# Or run the setup script directly
./Scripts/dev-environment.sh
```

### 2. Run Development Loop

```bash
# Run continuous development loop
make dev-loop

# Run single iteration
make dev-loop-single

# Run specific components
make dev-test      # Run tests
make dev-benchmark # Run benchmarks
make dev-telemetry # Collect telemetry
make dev-report    # Generate reports
```

### 3. Cleanup

```bash
# Clean development environment
make dev-cleanup
```

## Development Environment Structure

```
dev-environment/
├── configs/           # Configuration files
│   ├── colibridb-dev.conf.json
│   ├── colibridb-test.conf.json
│   └── colibridb-perf.conf.json
├── data/              # Test data
│   ├── databases/
│   ├── backups/
│   └── temp/
├── logs/              # Log files
│   ├── server/
│   ├── cli/
│   ├── tests/
│   ├── benchmarks/
│   └── telemetry/
├── reports/           # Generated reports
│   ├── test-results/
│   ├── benchmarks/
│   ├── telemetry/
│   └── coverage/
└── tests/             # Test files
    ├── unit/
    ├── integration/
    ├── performance/
    ├── stress/
    └── regression/
```

## Scripts

### Development Environment Setup

**File:** `Scripts/dev-environment.sh`

Sets up the complete development environment including:
- Directory structure creation
- Configuration file generation
- Project building
- Test data setup
- Telemetry system configuration

**Usage:**
```bash
./Scripts/dev-environment.sh
```

### Development Loop

**File:** `Scripts/development-loop.sh`

Runs automated development cycles including:
- Project building
- Server startup
- Test execution
- Benchmark execution
- Telemetry collection
- Report generation
- Cleanup

**Usage:**
```bash
# Continuous loop
./Scripts/development-loop.sh --continuous

# Single iteration
./Scripts/development-loop.sh --iterations 1

# With custom interval
./Scripts/development-loop.sh --continuous --interval 600
```

**Options:**
- `--continuous`: Run continuously
- `--iterations N`: Number of iterations
- `--interval N`: Interval between iterations (seconds)
- `--verbose`: Verbose output
- `--no-cleanup`: Skip cleanup after each iteration
- `--no-reports`: Skip report generation
- `--no-notify`: Skip failure notifications

### Test Suite

**File:** `Scripts/run-tests.sh`

Runs comprehensive test suite including:
- Unit tests
- Integration tests
- Performance tests
- Stress tests
- Server tests
- Coverage tests

**Usage:**
```bash
# Run all tests
./Scripts/run-tests.sh

# With options
./Scripts/run-tests.sh --verbose --coverage --parallel --stress
```

**Options:**
- `--config FILE`: Test configuration file
- `--verbose`: Verbose output
- `--coverage`: Generate coverage report
- `--parallel`: Run tests in parallel
- `--stress`: Include stress tests

### Benchmark Suite

**File:** `Scripts/run-benchmarks.sh`

Runs comprehensive benchmark suite including:
- SQL performance benchmarks
- Memory performance benchmarks
- Index performance benchmarks
- Constraint performance benchmarks
- Data type performance benchmarks
- Transaction performance benchmarks
- I/O performance benchmarks
- Stress benchmarks

**Usage:**
```bash
# Run all benchmarks
./Scripts/run-benchmarks.sh

# With options
./Scripts/run-benchmarks.sh --iterations 1000 --duration 60 --threads 8
```

**Options:**
- `--config FILE`: Benchmark configuration file
- `--iterations N`: Number of iterations
- `--duration N`: Duration in seconds
- `--threads N`: Number of threads
- `--verbose`: Verbose output
- `--format FORMAT`: Export format (json|csv|prometheus)

### Telemetry Collection

**File:** `Scripts/collect-telemetry.sh`

Collects comprehensive telemetry data including:
- System metrics
- ColibriDB metrics
- Performance data
- Error data
- Query data
- Memory data
- I/O data
- Transaction data
- Index data

**Usage:**
```bash
# Collect telemetry
./Scripts/collect-telemetry.sh

# With options
./Scripts/collect-telemetry.sh --duration 300 --interval 1 --format json
```

**Options:**
- `--output DIR`: Output directory
- `--duration N`: Collection duration (seconds)
- `--interval N`: Collection interval (seconds)
- `--format FORMAT`: Output format (json|csv|prometheus)
- `--verbose`: Verbose output
- `--no-logs`: Skip log collection
- `--no-metrics`: Skip metrics collection
- `--no-profiling`: Skip profiling data

### Report Generation

**File:** `Scripts/generate-report.sh`

Generates comprehensive reports including:
- Test results
- Performance analysis
- Telemetry analysis
- System analysis
- Error analysis
- Benchmark analysis
- Coverage analysis
- Recommendations

**Usage:**
```bash
# Generate report
./Scripts/generate-report.sh

# With options
./Scripts/generate-report.sh --cycle "iteration-1" --format html --verbose
```

**Options:**
- `--cycle ID`: Test cycle ID
- `--output DIR`: Output directory
- `--format FORMAT`: Report format (html|pdf|json|markdown)
- `--verbose`: Verbose output
- `--no-charts`: Skip chart generation
- `--no-metrics`: Skip metrics analysis
- `--no-logs`: Skip log analysis
- `--no-benchmarks`: Skip benchmark analysis

### Cleanup

**File:** `Scripts/cleanup.sh`

Cleans up development environment including:
- Data directories
- Log files
- Report files
- Build artifacts

**Usage:**
```bash
# Clean everything
./Scripts/cleanup.sh --all

# Clean specific components
./Scripts/cleanup.sh --data --logs --reports
```

**Options:**
- `--data`: Clean data directories
- `--logs`: Clean log files
- `--reports`: Clean report files
- `--build`: Clean build artifacts
- `--all`: Clean everything
- `--force`: Force cleanup without confirmation
- `--verbose`: Verbose output

## Makefile Targets

### Development Targets

- `make dev-setup`: Setup development environment
- `make dev-loop`: Run continuous development loop
- `make dev-loop-single`: Run single development iteration
- `make dev-test`: Run comprehensive test suite
- `make dev-benchmark`: Run performance benchmarks
- `make dev-telemetry`: Collect telemetry data
- `make dev-report`: Generate comprehensive reports
- `make dev-cleanup`: Clean development environment
- `make dev-cycle`: Run full development cycle
- `make dev-quick`: Quick development test

### Standard Targets

- `make build`: Build all targets
- `make clean`: Clean build artifacts
- `make test`: Run unit tests
- `make server`: Run server locally
- `make cli`: Run CLI
- `make dev`: Run development tools

## Configuration

### Development Configuration

**File:** `dev-environment/configs/colibridb-dev.conf.json`

```json
{
  "dataDir": "./dev-environment/data",
  "maxConnectionsLogical": 1000,
  "maxConnectionsPhysical": 8,
  "bufferPoolSizeBytes": 268435456,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": true,
  "serverHost": "localhost",
  "serverPort": 8080,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap",
  "logLevel": "debug",
  "telemetryEnabled": true,
  "profilingEnabled": true,
  "debugMode": true
}
```

### Test Configuration

**File:** `dev-environment/configs/colibridb-test.conf.json`

```json
{
  "dataDir": "./dev-environment/data/test",
  "maxConnectionsLogical": 100,
  "maxConnectionsPhysical": 4,
  "bufferPoolSizeBytes": 67108864,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": false,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap",
  "logLevel": "info",
  "telemetryEnabled": true,
  "profilingEnabled": false,
  "debugMode": false
}
```

### Performance Configuration

**File:** `dev-environment/configs/colibridb-perf.conf.json`

```json
{
  "dataDir": "./dev-environment/data/perf",
  "maxConnectionsLogical": 10000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 1073741824,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": true,
  "serverHost": "localhost",
  "serverPort": 8081,
  "indexImplementation": "ART",
  "storageEngine": "FileHeap",
  "logLevel": "warn",
  "telemetryEnabled": true,
  "profilingEnabled": true,
  "debugMode": false
}
```

## Telemetry System

The telemetry system collects comprehensive data about ColibrìDB performance and behavior:

### Metrics Collected

- **Database Metrics**: Size, table count, index count, connections
- **Buffer Pool Metrics**: Hits, misses, utilization, evictions
- **Query Metrics**: Count, rate, response time, types
- **Transaction Metrics**: Count, rate, commit rate, active transactions
- **Index Metrics**: Hits, misses, scans, insertions, deletions
- **Storage Metrics**: Size, utilization, I/O operations
- **System Metrics**: CPU, memory, disk, network usage

### Export Formats

- **JSON**: Structured data for analysis
- **CSV**: Tabular data for spreadsheets
- **Prometheus**: Metrics for monitoring systems
- **XML**: Structured data for enterprise systems

### Data Retention

- Default retention: 24 hours
- Configurable retention period
- Automatic cleanup of old data
- Compression support for large datasets

## Reporting System

The reporting system generates comprehensive reports including:

### Report Sections

1. **Summary**: Overall health and key metrics
2. **Test Results**: Detailed test execution results
3. **Performance Analysis**: Performance metrics and trends
4. **Telemetry Analysis**: System behavior analysis
5. **System Analysis**: Resource utilization and capacity planning
6. **Error Analysis**: Error patterns and resolution suggestions
7. **Benchmark Analysis**: Performance comparison and regression detection
8. **Coverage Analysis**: Code coverage metrics and trends
9. **Recommendations**: Actionable recommendations for improvement

### Report Formats

- **HTML**: Interactive web reports with charts
- **PDF**: Printable reports for documentation
- **JSON**: Structured data for programmatic analysis
- **Markdown**: Text-based reports for documentation
- **XML**: Structured data for enterprise systems

## Best Practices

### Development Workflow

1. **Setup**: Run `make dev-setup` to initialize environment
2. **Development**: Make code changes
3. **Testing**: Run `make dev-test` to validate changes
4. **Benchmarking**: Run `make dev-benchmark` to check performance
5. **Reporting**: Run `make dev-report` to generate reports
6. **Cleanup**: Run `make dev-cleanup` to clean environment

### Continuous Integration

1. **Automated Testing**: Use `make dev-loop` for continuous testing
2. **Performance Monitoring**: Monitor benchmark results for regressions
3. **Telemetry Analysis**: Use telemetry data to identify issues
4. **Report Review**: Review generated reports for insights

### Troubleshooting

1. **Check Logs**: Review log files in `dev-environment/logs/`
2. **Verify Configuration**: Ensure configuration files are correct
3. **Clean Environment**: Run `make dev-cleanup` to reset environment
4. **Check Dependencies**: Ensure all required tools are installed

## Dependencies

### Required Tools

- **Swift**: For building and running ColibrìDB
- **curl**: For HTTP API testing
- **jq**: For JSON processing (optional)
- **osascript**: For system notifications (macOS)

### Optional Tools

- **Instruments**: For performance profiling (macOS)
- **Xcode**: For development and debugging
- **Git**: For version control

## Support

For issues with the development environment:

1. Check the log files in `dev-environment/logs/`
2. Review the configuration files
3. Run `make dev-cleanup` to reset the environment
4. Check the ColibrìDB documentation
5. Report issues on the project repository

## License

This development environment is part of ColibrìDB and is licensed under the BSD 3-Clause License. See the LICENSE file for details.

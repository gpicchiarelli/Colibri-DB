# Changelog

All notable changes to ColibrìDB will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2025-01-02

### Added

- **Professional Logging System**: Comprehensive structured logging with multiple handlers and formatters
- **Simplified Documentation**: Consolidated documentation structure with clear navigation
- **Enhanced CLI**: Improved command-line interface with better help and examples
- **Performance Monitoring**: Real-time metrics and alerting system
- **Configuration Management**: Advanced configuration options and validation

### Changed
- **README Simplification**: Reduced from 38+ badges to 6 essential, verifiable badges
- **Documentation Structure**: Consolidated from 50+ wiki files to 8 focused HTML pages
- **Code Quality**: Removed all print statements and replaced with proper logging
- **Package Configuration**: Cleaned up Package.swift by removing backup file exclusions

### Fixed
- **Debug Code**: Removed all debug print statements from production code
- **Documentation Navigation**: Simplified and improved documentation structure
- **Code Cleanliness**: Removed backup files and cleaned up project structure
- **Professional Presentation**: Enhanced overall repository professionalism

### Documentation
- **New Pages**: Quick Start, API Reference, Configuration, Examples, Troubleshooting, Performance, Monitoring, CLI Reference
- **Consolidated Structure**: Replaced complex wiki structure with focused HTML pages
- **Better Navigation**: Clear user journey based on role (Developer, Architect, Researcher, Operator)
- **Professional Styling**: Added CSS styling for better presentation

## [Unreleased]

### Added
- Persistent B+Tree on disk (insert/split/range/equality, multi-type keys)
- Hash/ART in-memory indexes
- CLI `coldb` with index, policy, insert/scan commands
- File-backed heap storage (insert/scan) and minimal WAL
- Persistent index catalog and recovery
- Aligned documentation (README, index docs, storage/indexes/WAL/concurrency modules, CLI guide)

### Changed
- Improved documentation structure and consistency
- Enhanced code formatting and linting

### Fixed
- Resolved duplicate content in markdown files
- Fixed inconsistent formatting across documentation

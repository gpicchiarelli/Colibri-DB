# Changelog

All notable changes to ColibrìDB will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2025-01-02

### Added

- **Lock Striping**: Implemented lock striping with 64 stripes to reduce contention (5-10x concurrency improvement)
- **Binary Serialization**: New custom binary format for Row data (3-5x faster than JSON)
- **B-Tree Caching**: Intelligent page cache with LRU eviction and prefetching
- **Query Plan Cache**: Execution plan caching for frequent queries (10-50x faster)
- **Adaptive Algorithms**: Adaptive split points based on key distribution

### Changed
- **Fine-grained Locking**: Replaced global locks with granular locks
- **Periodic Cleanup**: Automatic memory cleanup system
- **Enhanced Error Handling**: Robust error handling in all components
- **Performance Monitoring**: Integrated metrics for performance monitoring

### Fixed
- **Memory Leaks**: Fixed leaks in transaction management and global state
- **Race Conditions**: Implemented fine-grained locking in MVCC
- **Resource Leaks**: Proper cleanup of file handles in FileHeapTable
- **WAL Error Handling**: Improved resilience during initialization and recovery
- **SQL Injection**: Implemented complete input validation and sanitization

### Documentation
- Updated README with new optimizations
- Complete documentation of performance improvements
- Guides for using new features

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

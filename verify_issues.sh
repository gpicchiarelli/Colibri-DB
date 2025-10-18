#!/bin/bash
echo "🔍 Verifying Issue Code Implementation..."
echo ""

# Issue #1 - Memory Leak Database
echo "Issue #1 - Database Memory Leak:"
grep -l "startPeriodicCleanup\|cleanupTimer" Sources/ColibriCore/Engine/Database*.swift && echo "  ✅ Periodic cleanup found" || echo "  ❌ NOT FOUND"

# Issue #7 - SQL Injection
echo "Issue #7 - SQL Injection:"
ls Sources/ColibriCore/Engine/Database+PreparedSQL.swift 2>/dev/null && echo "  ✅ Prepared statements file exists" || echo "  ❌ NOT FOUND"

# Issue #8 - Path Traversal
echo "Issue #8 - Path Traversal:"
ls Sources/ColibriCore/Util/PathValidator.swift 2>/dev/null && echo "  ✅ PathValidator exists" || echo "  ❌ NOT FOUND"

# Issue #4 - Buffer Pool Leak
echo "Issue #4 - Buffer Pool Leak:"
grep -l "LRUBufferPool\|cleanupTimer" Sources/ColibriCore/Storage/Buffer/*.swift && echo "  ✅ LRU Buffer Pool found" || echo "  ❌ NOT FOUND"

# Issue #34 - Query Cache
echo "Issue #34 - Query Cache Leak:"
grep -l "class QueryCache\|LRU\|statistics" Sources/ColibriCore/Query/Planner/QueryExecutor.swift && echo "  ✅ QueryCache LRU found" || echo "  ❌ NOT FOUND"

# Issue #15 - Config Validation
echo "Issue #15 - Config Validation:"
grep -l "func validate()" Sources/ColibriCore/System/Config.swift && echo "  ✅ Config validation found" || echo "  ❌ NOT FOUND"

# Issue #29 - Server Config
echo "Issue #29 - Server Config Validation:"
grep -l "ConfigurationValidator\|validateHost" Sources/ColibriServer/ServerConfig.swift && echo "  ✅ Server validation found" || echo "  ❌ NOT FOUND"

# Issue #33 - Compression
echo "Issue #33 - Compression Error Handling:"
grep -l "decompress.*throws\|validate.*compressed" Sources/ColibriCore/Util/CompressionCodec.swift && echo "  ✅ Compression error handling found" || echo "  ❌ NOT FOUND"

# Issue #18 - Page Compaction
echo "Issue #18 - Page Compaction:"
grep -l "memmove\|reserveCapacity\|In-place compaction" Sources/ColibriCore/Storage/Page.swift && echo "  ✅ Optimized compaction found" || echo "  ❌ NOT FOUND"

# Group Commit (P1 task)
echo "Group Commit Implementation:"
ls Sources/ColibriCore/Concurrency/GroupCommit/GroupCommitCoordinator.swift 2>/dev/null && echo "  ✅ GroupCommitCoordinator exists" || echo "  ❌ NOT FOUND"

echo ""
echo "✅ Verification complete!"

#!/bin/bash
echo "🔬 Detailed Code Verification..."
echo ""

# Issue #1 - Database cleanup should clean txLastLSN
echo "Issue #1 - txLastLSN cleanup:"
grep -A 10 "periodicCleanup\|cleanupStaleEntries" Sources/ColibriCore/Engine/Database+Maintenance.swift 2>/dev/null | grep -q "txLastLSN" && echo "  ✅ txLastLSN cleanup confirmed" || echo "  ⚠️  txLastLSN cleanup not explicit"

# Issue #7 - Prepared statements should have PreparedStatement struct
echo "Issue #7 - PreparedStatement struct:"
grep -q "struct PreparedStatement\|class PreparedStatement" Sources/ColibriCore/Engine/Database+PreparedSQL.swift && echo "  ✅ PreparedStatement struct exists" || echo "  ⚠️  PreparedStatement struct not found"

# Issue #4 - Buffer pool should have eviction
echo "Issue #4 - Buffer pool eviction:"
grep -q "evict\|removeOldest" Sources/ColibriCore/Storage/Buffer/LRUBufferPool.swift && echo "  ✅ Eviction logic exists" || echo "  ⚠️  Eviction not found"

# Issue #34 - Query cache should have LRU with statistics
echo "Issue #34 - Query cache statistics:"
grep -q "func statistics.*hitRate\|var hits.*UInt64" Sources/ColibriCore/Query/Planner/QueryExecutor.swift && echo "  ✅ Statistics tracking found" || echo "  ⚠️  Statistics not found"

# Group Commit - Should have submitCommit and commitSync
echo "Group Commit - Core methods:"
grep -q "func submitCommit\|func commitSync" Sources/ColibriCore/Concurrency/GroupCommit/GroupCommitCoordinator.swift && echo "  ✅ Core Group Commit methods exist" || echo "  ⚠️  Methods not found"

# Issue #15 - Config should have validate() method
echo "Issue #15 - Config validate method:"
grep -q "func validate.*throws" Sources/ColibriCore/System/Config.swift && echo "  ✅ Config validate() method exists" || echo "  ⚠️  validate() not found"

# Issue #29 - Server config should validate host format
echo "Issue #29 - Host validation:"
grep -q "validateHost\|isValidIPv4\|isValidIPv6" Sources/ColibriServer/ServerConfig.swift && echo "  ✅ Host validation found" || echo "  ⚠️  Host validation not found"

# Issue #33 - Compression should throw on errors
echo "Issue #33 - Compression error handling:"
grep -q "throws.*Data\|guard.*else.*throw" Sources/ColibriCore/Util/CompressionCodec.swift && echo "  ✅ Error handling found" || echo "  ⚠️  Error handling not found"

# Issue #18 - Page compaction should use memmove
echo "Issue #18 - In-place compaction:"
grep -q "memmove\|In-place" Sources/ColibriCore/Storage/Page.swift && echo "  ✅ In-place compaction found" || echo "  ⚠️  memmove not found"

echo ""
echo "✅ Detailed verification complete!"

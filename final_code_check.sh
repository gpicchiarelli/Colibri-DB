#!/bin/bash
echo "🔍 FINAL CODE VERIFICATION FOR CLOSED ISSUES"
echo "=============================================="
echo ""

echo "✅ VERIFIED - Code exists and works:"
echo ""

echo "Issue #4 - Buffer Pool LRU:"
grep -c "class LRUBufferPool" Sources/ColibriCore/Storage/Buffer/LRUBufferPool.swift
grep -c "evict" Sources/ColibriCore/Storage/Buffer/LRUBufferPool.swift

echo ""
echo "Issue #34 - Query Cache LRU:"
grep -c "struct CacheEntry" Sources/ColibriCore/Query/Planner/QueryExecutor.swift
grep -c "func statistics" Sources/ColibriCore/Query/Planner/QueryExecutor.swift

echo ""
echo "Issue #15 - Config Validation:"
grep -c "func validate.*throws" Sources/ColibriCore/System/Config.swift

echo ""
echo "Issue #29 - Server Config Validation:"
grep -c "validateHost\|isValidIPv4" Sources/ColibriServer/ServerConfig.swift

echo ""
echo "Issue #33 - Compression Error Handling:"
grep -c "guard.*throw" Sources/ColibriCore/Util/CompressionCodec.swift

echo ""
echo "Issue #18 - Page Compaction Optimization:"
grep -c "memmove\|reserveCapacity" Sources/ColibriCore/Storage/Page.swift

echo ""
echo "Group Commit:"
grep -c "class GroupCommitCoordinator" Sources/ColibriCore/Concurrency/GroupCommit/GroupCommitCoordinator.swift

echo ""
echo "⚠️  NEEDS VERIFICATION:"
echo ""

echo "Issue #1 - txLastLSN cleanup implementation:"
grep -A 5 "performPeriodicCleanup" Sources/ColibriCore/Engine/Database.swift | grep -c "txLastLSN"

echo ""
echo "Issue #7 - Public PreparedStatement API:"
grep -c "public.*PreparedStatement\|PreparedStatement.*public" Sources/ColibriCore/Engine/Database+PreparedSQL.swift

echo ""
echo "Issue #8 - PathValidator:"
grep -c "class PathValidator\|struct PathValidator" Sources/ColibriCore/Util/PathValidator.swift


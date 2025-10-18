import Foundation
import ColibriCore
import Dispatch

print("\n🔥 CONCURRENT GROUP COMMIT TEST\n")

let testDir = "/tmp/colibri_concurrent_gc_\(UUID().uuidString)"
defer { try? FileManager.default.removeItem(atPath: testDir) }

var config = DBConfig(dataDir: testDir, storageEngine: "FileHeap")
config.walEnabled = true
config.walGroupCommitMs = 2.0
config.defaultIsolationLevel = IsolationLevel.readCommitted

let db = Database(config: config)
try! db.createTable("test")

let concurrency = 8
let iterationsPerThread = 100
print("Running \(concurrency) concurrent threads...")
print("Each thread: \(iterationsPerThread) commits\n")

let start = Date()
let queue = DispatchQueue(label: "bench", attributes: .concurrent)
let group = DispatchGroup()

for threadId in 0..<concurrency {
    group.enter()
    queue.async {
        defer { group.leave() }
        
        for i in 0..<iterationsPerThread {
            do {
                let tid = try db.begin()
                let id = threadId * iterationsPerThread + i
                try db.insert(into: "test", row: [
                    "id": .int(Int64(id)),
                    "thread": .int(Int64(threadId)),
                    "value": .string("test\(id)")
                ], tid: tid)
                try db.commit(tid)
            } catch {
                print("Error in thread \(threadId): \(error)")
            }
        }
    }
}

group.wait()
let elapsed = Date().timeIntervalSince(start)

let totalCommits = concurrency * iterationsPerThread
print("✓ \(totalCommits) commits in \(String(format: "%.3f", elapsed))s")
print("✓ \(String(format: "%.2f", Double(totalCommits) / elapsed)) commits/sec\n")

if let metrics = db.groupCommitMetrics() {
    print("Group Commit Metrics:")
    print("  • Total commits: \(metrics.totalCommits)")
    print("  • Total batches: \(metrics.totalBatches)")
    print("  • Average batch size: \(String(format: "%.1f", metrics.averageBatchSize))")
    print("  • Largest batch: \(metrics.largestBatch)")
    print("  • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
    print("  • Performance multiplier: \(String(format: "%.1fx", metrics.performanceMultiplier))")
}

try! db.close()
print("\n✅ Concurrent test completed!")


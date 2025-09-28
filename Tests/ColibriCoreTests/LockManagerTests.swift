//
//  LockManagerTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: Lock manager reenactments testing contention scenarios.

import Foundation
import Dispatch
@_spi(Experimental) import Testing
@preconcurrency @testable import ColibriCore


@Suite(.serialized)
struct LockManagerTests {
    @Test func detectsDeadlockBetweenTransactions() throws {
        let manager = LockManager(defaultTimeout: 1.0)
        let resourceA: LockTarget = .table("A")
        let resourceB: LockTarget = .table("B")

        let handleT1 = try manager.lock(resourceA, mode: .exclusive, tid: 1, timeout: nil)
        let handleT2 = try manager.lock(resourceB, mode: .exclusive, tid: 2, timeout: nil)

        let waiterFinished = DispatchSemaphore(value: 0)
        let t1Result = DispatchQueue(label: "t1-result")
        var t1SecondHandle: LockHandle?
        var t1Error: Error?

        // Start T1 trying to acquire resourceB in background
        DispatchQueue.global().async {
            do {
                let h = try manager.lock(resourceB, mode: .exclusive, tid: 1, timeout: nil)
                t1Result.sync { t1SecondHandle = h }
            } catch {
                t1Result.sync { t1Error = error }
            }
            waiterFinished.signal()
        }

        // Wait a bit for T1 to be queued waiting for resourceB
        Thread.sleep(forTimeInterval: 0.1)

        // Now T2 tries to acquire resourceA - this should detect deadlock
        var deadlockRaised = false
        do {
            _ = try manager.lock(resourceA, mode: .exclusive, tid: 2, timeout: nil)
            Issue.record("Expected deadlock when locking resourceA for T2")
        } catch let error as DBError {
            if case .deadlock = error { deadlockRaised = true }
        } catch {
            Issue.record("Unexpected error: \(error)")
        }
        #expect(deadlockRaised)

        // Clean up
        manager.unlock(handleT2)
        _ = waiterFinished.wait(timeout: .now() + 1)
        t1Result.sync {
            if let err = t1Error {
                Issue.record("Unexpected error for T1: \(err)")
            }
            if let h = t1SecondHandle {
                manager.unlock(h)
            }
        }
        manager.unlock(handleT1)
    }

    @Test func honorsTimeoutWhenLockCannotBeGranted() throws {
        let manager = LockManager(defaultTimeout: 1.0)
        let resource: LockTarget = .table("items")
        let handle = try manager.lock(resource, mode: .exclusive, tid: 1, timeout: nil)

        var timeoutRaised = false
        do {
            _ = try manager.lock(resource, mode: .exclusive, tid: 2, timeout: 0.05)
            Issue.record("Expected timeout when acquiring lock for T2")
        } catch let error as DBError {
            if case .lockTimeout = error { timeoutRaised = true }
        } catch {
            Issue.record("Unexpected error: \(error)")
        }
        #expect(timeoutRaised)

        manager.unlock(handle)
    }

    @Test func upgradesSharedLockToExclusiveAfterPeersRelease() throws {
        let manager = LockManager(defaultTimeout: 1.0)
        let resource: LockTarget = .table("orders")
        let sharedT1 = try manager.lock(resource, mode: .shared, tid: 1, timeout: nil)
        let sharedT2 = try manager.lock(resource, mode: .shared, tid: 2, timeout: nil)

        let upgradeFinished = DispatchSemaphore(value: 0)
        let upgradeResult = DispatchQueue(label: "upgrade-result")
        var exclusiveHandle: LockHandle?
        var upgradeError: Error?

        DispatchQueue.global().async {
            do {
                let h = try manager.lock(resource, mode: .exclusive, tid: 1, timeout: nil)
                upgradeResult.sync { exclusiveHandle = h }
            } catch {
                upgradeResult.sync { upgradeError = error }
            }
            upgradeFinished.signal()
        }

        Thread.sleep(forTimeInterval: 0.05)
        manager.unlock(sharedT2)

        let waitResult = upgradeFinished.wait(timeout: .now() + 1)
        #expect(waitResult == .success, "Upgrade to exclusive lock timed out")
        upgradeResult.sync {
            if let error = upgradeError {
                Issue.record("Unexpected error during upgrade: \(error)")
            }
            #expect(exclusiveHandle?.mode == .exclusive)

            if let exclusive = exclusiveHandle {
                manager.unlock(exclusive)
            }
        }
        manager.unlock(sharedT1)
    }
}


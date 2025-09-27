//
//  TwoPhaseCommit.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Two-phase council negotiating distributed commits.

import Foundation

/// Participant wrapper used by the two-phase commit coordinator.
public struct TwoPhaseCommitParticipant {
    public let id: String
    public let prepare: () throws -> Bool
    public let commit: () throws -> Void
    public let abort: () throws -> Void

    public init(id: String,
                prepare: @escaping () throws -> Bool,
                commit: @escaping () throws -> Void,
                abort: @escaping () throws -> Void) {
        self.id = id
        self.prepare = prepare
        self.commit = commit
        self.abort = abort
    }
}

public enum TwoPhaseCommitError: Error, Equatable, CustomStringConvertible {
    case prepareFailed(participant: String)
    case commitFailed(participant: String)

    public var description: String {
        switch self {
        case .prepareFailed(let id):
            return "2PC prepare failed for participant \(id)"
        case .commitFailed(let id):
            return "2PC commit failed for participant \(id)"
        }
    }
}

/// Minimal in-memory two-phase commit coordinator.
public final class TwoPhaseCommitCoordinator {
    public init() {}

    /// Executes a two-phase commit cycle across the provided participants.
    /// - Parameters:
    ///   - globalTransactionID: Identifier for logging/diagnostics.
    ///   - participants: Ordered list of participants to coordinate.
    public func execute(globalTransactionID: String,
                        participants: [TwoPhaseCommitParticipant]) throws {
        var prepared: [TwoPhaseCommitParticipant] = []
        do {
            for participant in participants {
                do {
                    let ok = try participant.prepare()
                    guard ok else { throw TwoPhaseCommitError.prepareFailed(participant: participant.id) }
                    prepared.append(participant)
                } catch {
                    throw TwoPhaseCommitError.prepareFailed(participant: participant.id)
                }
            }
        } catch let error {
            for participant in prepared.reversed() {
                try? participant.abort()
            }
            throw error
        }

        do {
            for participant in prepared {
                do {
                    try participant.commit()
                } catch {
                    throw TwoPhaseCommitError.commitFailed(participant: participant.id)
                }
            }
        } catch let error {
            for participant in prepared.reversed() {
                try? participant.abort()
            }
            throw error
        }
    }
}


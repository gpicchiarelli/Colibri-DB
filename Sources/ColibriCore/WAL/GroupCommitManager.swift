//
//  GroupCommitManager.swift
//  ColibrìDB Group Commit Manager Implementation
//
//  Based on: spec/GroupCommit.tla
//  Implements: Group commit optimization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Durability Preserved: Durability is preserved
//  - Order Preserved: Order is preserved
//  - Bounded Wait: Wait is bounded
//

import Foundation

// MARK: - Group Commit Types




// MARK: - Supporting Types

/// Group commit manager error
public enum GroupCommitManagerError: Error, LocalizedError {
    case queueFull
    case invalidRequest
    case flushFailed
    case timerError
    case configurationError
    
    public var errorDescription: String? {
        switch self {
        case .queueFull:
            return "Commit queue is full"
        case .invalidRequest:
            return "Invalid commit request"
        case .flushFailed:
            return "Flush failed"
        case .timerError:
            return "Timer error"
        case .configurationError:
            return "Configuration error"
        }
    }
}
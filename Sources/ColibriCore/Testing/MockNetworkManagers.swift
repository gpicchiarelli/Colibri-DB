//
//  MockNetworkManagers.swift
//  ColibrìDB Mock Network Managers
//
//  Mock implementations for testing
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Mock Raft Network Manager
public actor MockRaftNetworkManager: RaftNetworkManager {
    private var appendEntriesSent: [(ServerID, Term, [LogEntry])] = []
    private var voteRequestsSent: [(ServerID, Term, ServerID)] = []
    private var voteResponses: [Bool] = []
    
    public init() {}
    
    public func sendAppendEntries(to: ServerID, term: Term, entries: [LogEntry]) async throws {
        appendEntriesSent.append((to, term, entries))
    }
    
    public func sendVoteRequest(to: ServerID, term: Term, candidateId: ServerID) async throws -> Bool {
        voteRequestsSent.append((to, term, candidateId))
        // Return true for mock (vote granted)
        return voteResponses.isEmpty ? true : voteResponses.removeFirst()
    }
    
    public func broadcastHeartbeat() async throws {
        // Mock implementation: no-op
    }
    
    public func setVoteResponse(_ granted: Bool) {
        voteResponses.append(granted)
    }
}

/// Mock State Machine
public actor MockStateMachine: StateMachine {
    private var state: [String: String] = [:]
    
    public init() {}
    
    public func applyCommand(command: String, data: Data) async throws {
        state[command] = String(data: data, encoding: .utf8) ?? ""
    }
    
    public func getState() async -> [String: String] {
        return state
    }
}

/// Mock Network Manager for DistributedQueryManager
public actor MockNetworkManager: NetworkManager {
    private var sentMessages: [(String, Data)] = []
    private var receivedMessages: [(String, Data)] = []
    
    public init() {}
    
    public func sendMessage(to nodeId: String, message: Data) async throws {
        sentMessages.append((nodeId, message))
    }
    
    public func receiveMessage() async throws -> (from: String, message: Data) {
        if receivedMessages.isEmpty {
            throw NetworkError.noMessageAvailable
        }
        return receivedMessages.removeFirst()
    }
    
    public func addReceivedMessage(from: String, message: Data) {
        receivedMessages.append((from, message))
    }
}

public enum NetworkError: Error, LocalizedError {
    case noMessageAvailable
    
    public var errorDescription: String? {
        switch self {
        case .noMessageAvailable:
            return "No message available"
        }
    }
}


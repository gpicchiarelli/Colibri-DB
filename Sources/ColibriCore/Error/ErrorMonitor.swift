//
//  ErrorMonitor.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation
import os.log

/// Error monitoring
public final class ErrorMonitor {
    private let logger = Logger(subsystem: "com.colibridb.error", category: "monitor")
    private let errorManager: ErrorManager
    private var monitoringTimer: Timer?
    private var alertThresholds: [ErrorType: Int] = [:]
    
    public init(errorManager: ErrorManager) {
        self.errorManager = errorManager
        setupAlertThresholds()
    }
    
    /// Sets up alert thresholds
    private func setupAlertThresholds() {
        alertThresholds[.database] = 10
        alertThresholds[.storage] = 5
        alertThresholds[.transaction] = 20
        alertThresholds[.index] = 15
        alertThresholds[.query] = 50
        alertThresholds[.configuration] = 3
        alertThresholds[.unknown] = 100
    }
    
    /// Starts error monitoring
    public func startMonitoring() {
        logger.info("Starting error monitoring...")
        monitoringTimer = Timer.scheduledTimer(withTimeInterval: 5.0, repeats: true) { [weak self] _ in
            self?.checkErrors()
        }
    }
    
    /// Stops error monitoring
    public func stopMonitoring() {
        logger.info("Stopping error monitoring...")
        monitoringTimer?.invalidate()
        monitoringTimer = nil
    }
    
    /// Checks for errors and triggers alerts
    private func checkErrors() {
        let recentErrors = errorManager.getRecentErrors(within: 60) // Last minute
        
        for (errorType, errors) in recentErrors {
            let threshold = alertThresholds[errorType] ?? 100
            if errors.count >= threshold {
                logger.critical("Error threshold exceeded for \(errorType): \(errors.count) errors in the last minute")
                triggerAlert(for: errorType, count: errors.count)
            }
        }
    }
    
    /// Triggers an alert for a specific error type
    private func triggerAlert(for errorType: ErrorType, count: Int) {
        logger.critical("ALERT: \(errorType) errors exceeded threshold - \(count) errors detected")
        // TODO: Implement alert notification (email, Slack, etc.)
    }
}
//
//  CLIColors.swift
//  ColibrìDB - CLI Color Support
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation

/// ANSI color codes for beautiful terminal output
public struct CLIColors {
    private let supportsColor: Bool
    
    public init() {
        // Check if terminal supports colors
        self.supportsColor = ProcessInfo.processInfo.environment["TERM"] != nil &&
                            ProcessInfo.processInfo.environment["NO_COLOR"] == nil
    }
    
    func header(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;36m") // Bold Cyan
    }
    
    func section(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;33m") // Bold Yellow
    }
    
    func prompt(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;32m") // Bold Green
    }
    
    func error(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;31m") // Bold Red
    }
    
    func info(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;34m") // Bold Blue
    }
    
    func timing(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[90m") // Dark Gray
    }
    
    func border(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[37m") // Light Gray
    }
    
    func tableHeader(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[1;37m") // Bold White
    }
    
    func tableName(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[36m") // Cyan
    }
    
    func columnName(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[35m") // Magenta
    }
    
    func dataType(_ text: String) -> String {
        return colorize(text, with: "\u{1B}[33m") // Yellow
    }
    
    private func colorize(_ text: String, with code: String) -> String {
        guard supportsColor else { return text }
        return "\(code)\(text)\u{1B}[0m"
    }
}

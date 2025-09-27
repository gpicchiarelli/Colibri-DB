//
//  DispatchQoS+Config.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: QoS helpers mapping configuration strings to DispatchQoS values.

import Dispatch

extension DispatchQoS {
    static func fromConfig(_ value: String) -> DispatchQoS {
        switch value.lowercased() {
        case "userinteractive", "user_interactive":
            return .userInteractive
        case "userinitiated", "user_initiated":
            return .userInitiated
        case "default":
            return .default
        case "background":
            return .background
        case "utility":
            fallthrough
        default:
            return .utility
        }
    }
}

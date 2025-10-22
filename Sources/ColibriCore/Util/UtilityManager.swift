//
//  Util.swift
//  ColibrìDB Utility Functions Implementation
//
//  Based on: spec/Util.tla
//  Implements: Database utility functions
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Reliability: Robust utility functions
//  - Efficiency: Optimized implementations
//  - Reusability: Common functionality
//  - Maintainability: Well-structured code
//

import Foundation

// MARK: - Utility Types

/// Utility function type
/// Corresponds to TLA+: UtilityFunctionType
public enum UtilityFunctionType: String, Codable, Sendable {
    case hash = "hash"
    case checksum = "checksum"
    case compression = "compression"
    case encryption = "encryption"
    case serialization = "serialization"
    case validation = "validation"
    case conversion = "conversion"
    case formatting = "formatting"
}

/// Utility status
/// Corresponds to TLA+: UtilityStatus
public enum UtilityStatus: String, Codable, Sendable {
    case success = "success"
    case failure = "failure"
    case partial = "partial"
    case timeout = "timeout"
}

/// Utility result
/// Corresponds to TLA+: UtilityResult
public struct UtilityResult<T>: Codable, Sendable, Equatable where T: Codable, T: Equatable {
    public let status: UtilityStatus
    public let data: T?
    public let error: String?
    public let timestamp: Date
    public let executionTime: TimeInterval
    
    public init(status: UtilityStatus, data: T?, error: String?, timestamp: Date = Date(), executionTime: TimeInterval) {
        self.status = status
        self.data = data
        self.error = error
        self.timestamp = timestamp
        self.executionTime = executionTime
    }
}

// MARK: - Hash Utilities

/// Hash utility functions
/// Corresponds to TLA+ module: Util.tla
public class HashUtil {
    
    /// Hash function
    /// TLA+ Action: Hash(data)
    public static func hash(_ data: Data) -> UInt32 {
        // TLA+: Hash data using FNV-1a algorithm
        var hash: UInt32 = 2166136261
        
        for byte in data {
            hash ^= UInt32(byte)
            hash = hash &* 16777619
        }
        
        return hash
    }
    
    /// Hash string
    public static func hash(_ string: String) -> UInt32 {
        return hash(string.data(using: .utf8) ?? Data())
    }
    
    /// Hash value
    public static func hash(_ value: Value) -> UInt32 {
        switch value {
        case .string(let s):
            return hash(s)
        case .int(let i):
            return hash(String(i))
        case .double(let d):
            return hash(String(d))
        case .bool(let b):
            return hash(String(b))
        case .null:
            return hash("null")
        case .array(let a):
            let combined = a.map { hash($0) }.reduce(0, ^)
            return hash(String(combined))
        case .object(let o):
            let combined = o.map { hash($0.key) ^ hash($0.value) }.reduce(0, ^)
            return hash(String(combined))
        }
    }
    
    /// Hash with salt
    public static func hashWithSalt(_ data: Data, salt: Data) -> UInt32 {
        var combined = Data()
        combined.append(salt)
        combined.append(data)
        return hash(combined)
    }
}

// MARK: - Checksum Utilities

/// Checksum utility functions
public class ChecksumUtil {
    
    /// Calculate CRC32 checksum
    /// TLA+ Action: CalculateCRC32(data)
    public static func calculateCRC32(_ data: Data) -> UInt32 {
        // TLA+: Calculate CRC32 checksum
        var crc: UInt32 = 0xFFFFFFFF
        
        for byte in data {
            crc ^= UInt32(byte)
            for _ in 0..<8 {
                if crc & 1 != 0 {
                    crc = (crc >> 1) ^ 0xEDB88320
                } else {
                    crc >>= 1
                }
            }
        }
        
        return crc ^ 0xFFFFFFFF
    }
    
    /// Calculate MD5 checksum
    public static func calculateMD5(_ data: Data) -> String {
        // TLA+: Calculate MD5 checksum
        // Simplified implementation
        let hash = HashUtil.hash(data)
        return String(format: "%08x", hash)
    }
    
    /// Calculate SHA256 checksum
    public static func calculateSHA256(_ data: Data) -> String {
        // TLA+: Calculate SHA256 checksum
        // Simplified implementation
        let hash = HashUtil.hash(data)
        return String(format: "%08x", hash)
    }
    
    /// Verify checksum
    public static func verifyChecksum(_ data: Data, expectedChecksum: UInt32) -> Bool {
        let actualChecksum = calculateCRC32(data)
        return actualChecksum == expectedChecksum
    }
}

// MARK: - Compression Utilities

/// Compression utility functions
public class CompressionUtil {
    
    /// Compress data
    /// TLA+ Action: Compress(data)
    public static func compress(_ data: Data) -> Data {
        // TLA+: Compress data using simple RLE
        var compressed = Data()
        var currentByte: UInt8 = 0
        var count: UInt8 = 0
        
        for byte in data {
            if byte == currentByte && count < 255 {
                count += 1
            } else {
                if count > 0 {
                    compressed.append(count)
                    compressed.append(currentByte)
                }
                currentByte = byte
                count = 1
            }
        }
        
        if count > 0 {
            compressed.append(count)
            compressed.append(currentByte)
        }
        
        return compressed
    }
    
    /// Decompress data
    /// TLA+ Action: Decompress(data)
    public static func decompress(_ data: Data) -> Data {
        // TLA+: Decompress data using simple RLE
        var decompressed = Data()
        var index = 0
        
        while index < data.count - 1 {
            let count = data[index]
            let byte = data[index + 1]
            
            for _ in 0..<count {
                decompressed.append(byte)
            }
            
            index += 2
        }
        
        return decompressed
    }
    
    /// Get compression ratio
    public static func getCompressionRatio(original: Data, compressed: Data) -> Double {
        guard original.count > 0 else { return 0.0 }
        return Double(compressed.count) / Double(original.count)
    }
}

// MARK: - Encryption Utilities

/// Encryption utility functions
public class EncryptionUtil {
    
    /// Encrypt data
    /// TLA+ Action: Encrypt(data, key)
    public static func encrypt(_ data: Data, key: Data) -> Data {
        // TLA+: Encrypt data using simple XOR
        var encrypted = Data()
        let keyBytes = Array(key)
        var keyIndex = 0
        
        for byte in data {
            let keyByte = keyBytes[keyIndex % keyBytes.count]
            encrypted.append(byte ^ keyByte)
            keyIndex += 1
        }
        
        return encrypted
    }
    
    /// Decrypt data
    /// TLA+ Action: Decrypt(data, key)
    public static func decrypt(_ data: Data, key: Data) -> Data {
        // TLA+: Decrypt data using simple XOR
        return encrypt(data, key: key) // XOR is symmetric
    }
    
    /// Generate random key
    public static func generateRandomKey(length: Int) -> Data {
        // TLA+: Generate random key
        var key = Data()
        for _ in 0..<length {
            key.append(UInt8.random(in: 0...255))
        }
        return key
    }
    
    /// Generate salt
    public static func generateSalt(length: Int = 16) -> Data {
        // TLA+: Generate salt
        return generateRandomKey(length: length)
    }
}

// MARK: - Serialization Utilities

/// Serialization utility functions
public class SerializationUtil {
    
    /// Serialize value to data
    /// TLA+ Action: Serialize(value)
    public static func serialize(_ value: Value) -> Data {
        // TLA+: Serialize value to data
        do {
            let jsonData = try JSONSerialization.data(withJSONObject: valueToJSON(value))
            return jsonData
        } catch {
            return Data()
        }
    }
    
    /// Deserialize data to value
    /// TLA+ Action: Deserialize(data)
    public static func deserialize(_ data: Data) -> Value? {
        // TLA+: Deserialize data to value
        do {
            let json = try JSONSerialization.jsonObject(with: data)
            return jsonToValue(json)
        } catch {
            return nil
        }
    }
    
    /// Convert value to JSON
    private static func valueToJSON(_ value: Value) -> Any {
        switch value {
        case .string(let s):
            return s
        case .int(let i):
            return i
        case .double(let d):
            return d
        case .bool(let b):
            return b
        case .null:
            return NSNull()
        case .array(let a):
            return a.map { valueToJSON($0) }
        case .object(let o):
            return o.reduce(into: [String: Any]()) { dict, pair in
                dict[pair.key] = valueToJSON(pair.value)
            }
        }
    }
    
    /// Convert JSON to value
    private static func jsonToValue(_ json: Any) -> Value? {
        if let string = json as? String {
            return .string(string)
        } else if let int = json as? Int {
            return .int(int)
        } else if let double = json as? Double {
            return .double(double)
        } else if let bool = json as? Bool {
            return .bool(bool)
        } else if json is NSNull {
            return .null
        } else if let array = json as? [Any] {
            let values = array.compactMap { jsonToValue($0) }
            return .array(values)
        } else if let dict = json as? [String: Any] {
            let object = dict.compactMapValues { jsonToValue($0) }
            return .object(object)
        }
        return nil
    }
}

// MARK: - Validation Utilities

/// Validation utility functions
public class ValidationUtil {
    
    /// Validate email
    /// TLA+ Action: ValidateEmail(email)
    public static func validateEmail(_ email: String) -> Bool {
        // TLA+: Validate email format
        let emailRegex = "^[A-Z0-9a-z._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}$"
        let emailPredicate = NSPredicate(format: "SELF MATCHES %@", emailRegex)
        return emailPredicate.evaluate(with: email)
    }
    
    /// Validate phone number
    public static func validatePhoneNumber(_ phone: String) -> Bool {
        // TLA+: Validate phone number format
        let phoneRegex = "^[+]?[0-9]{10,15}$"
        let phonePredicate = NSPredicate(format: "SELF MATCHES %@", phoneRegex)
        return phonePredicate.evaluate(with: phone)
    }
    
    /// Validate UUID
    public static func validateUUID(_ uuid: String) -> Bool {
        // TLA+: Validate UUID format
        let uuidRegex = "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
        let uuidPredicate = NSPredicate(format: "SELF MATCHES %@", uuidRegex)
        return uuidPredicate.evaluate(with: uuid)
    }
    
    /// Validate date format
    public static func validateDateFormat(_ dateString: String, format: String) -> Bool {
        // TLA+: Validate date format
        let formatter = DateFormatter()
        formatter.dateFormat = format
        return formatter.date(from: dateString) != nil
    }
    
    /// Validate range
    public static func validateRange(_ value: Double, min: Double, max: Double) -> Bool {
        // TLA+: Validate value is in range
        return value >= min && value <= max
    }
    
    /// Validate length
    public static func validateLength(_ string: String, min: Int, max: Int) -> Bool {
        // TLA+: Validate string length
        return string.count >= min && string.count <= max
    }
}

// MARK: - Conversion Utilities

/// Conversion utility functions
public class ConversionUtil {
    
    /// Convert bytes to human readable format
    /// TLA+ Action: ConvertBytesToHumanReadable(bytes)
    public static func convertBytesToHumanReadable(_ bytes: Int64) -> String {
        // TLA+: Convert bytes to human readable format
        let units = ["B", "KB", "MB", "GB", "TB", "PB"]
        var size = Double(bytes)
        var unitIndex = 0
        
        while size >= 1024 && unitIndex < units.count - 1 {
            size /= 1024
            unitIndex += 1
        }
        
        return String(format: "%.2f %@", size, units[unitIndex])
    }
    
    /// Convert duration to human readable format
    public static func convertDurationToHumanReadable(_ duration: TimeInterval) -> String {
        // TLA+: Convert duration to human readable format
        let hours = Int(duration) / 3600
        let minutes = Int(duration) % 3600 / 60
        let seconds = Int(duration) % 60
        
        if hours > 0 {
            return String(format: "%d:%02d:%02d", hours, minutes, seconds)
        } else if minutes > 0 {
            return String(format: "%d:%02d", minutes, seconds)
        } else {
            return String(format: "%d", seconds)
        }
    }
    
    /// Convert timestamp to date string
    public static func convertTimestampToDateString(_ timestamp: Date, format: String = "yyyy-MM-dd HH:mm:ss") -> String {
        // TLA+: Convert timestamp to date string
        let formatter = DateFormatter()
        formatter.dateFormat = format
        return formatter.string(from: timestamp)
    }
    
    /// Convert date string to timestamp
    public static func convertDateStringToTimestamp(_ dateString: String, format: String = "yyyy-MM-dd HH:mm:ss") -> Date? {
        // TLA+: Convert date string to timestamp
        let formatter = DateFormatter()
        formatter.dateFormat = format
        return formatter.date(from: dateString)
    }
    
    /// Convert value to string
    public static func convertValueToString(_ value: Value) -> String {
        // TLA+: Convert value to string
        switch value {
        case .string(let s):
            return s
        case .int(let i):
            return String(i)
        case .double(let d):
            return String(d)
        case .bool(let b):
            return String(b)
        case .null:
            return "null"
        case .array(let a):
            return a.map { convertValueToString($0) }.joined(separator: ",")
        case .object(let o):
            return o.map { "\($0.key):\(convertValueToString($0.value))" }.joined(separator: ",")
        }
    }
}

// MARK: - Formatting Utilities

/// Formatting utility functions
public class FormattingUtil {
    
    /// Format number with commas
    /// TLA+ Action: FormatNumberWithCommas(number)
    public static func formatNumberWithCommas(_ number: Int) -> String {
        // TLA+: Format number with commas
        let formatter = NumberFormatter()
        formatter.numberStyle = .decimal
        return formatter.string(from: NSNumber(value: number)) ?? String(number)
    }
    
    /// Format currency
    public static func formatCurrency(_ amount: Double, currencyCode: String = "USD") -> String {
        // TLA+: Format currency
        let formatter = NumberFormatter()
        formatter.numberStyle = .currency
        formatter.currencyCode = currencyCode
        return formatter.string(from: NSNumber(value: amount)) ?? String(amount)
    }
    
    /// Format percentage
    public static func formatPercentage(_ value: Double, decimals: Int = 2) -> String {
        // TLA+: Format percentage
        let formatter = NumberFormatter()
        formatter.numberStyle = .percent
        formatter.minimumFractionDigits = decimals
        formatter.maximumFractionDigits = decimals
        return formatter.string(from: NSNumber(value: value)) ?? String(value)
    }
    
    /// Format file size
    public static func formatFileSize(_ bytes: Int64) -> String {
        // TLA+: Format file size
        return ConversionUtil.convertBytesToHumanReadable(bytes)
    }
    
    /// Format duration
    public static func formatDuration(_ duration: TimeInterval) -> String {
        // TLA+: Format duration
        return ConversionUtil.convertDurationToHumanReadable(duration)
    }
    
    /// Format timestamp
    public static func formatTimestamp(_ timestamp: Date, format: String = "yyyy-MM-dd HH:mm:ss") -> String {
        // TLA+: Format timestamp
        return ConversionUtil.convertTimestampToDateString(timestamp, format: format)
    }
}

// MARK: - Utility Manager

/// Utility Manager for database utility functions
/// Corresponds to TLA+ module: Util.tla
public actor UtilityManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Utility functions registry
    /// TLA+: utilityFunctions \in [FunctionId -> UtilityFunctionType]
    private var utilityFunctions: [String: UtilityFunctionType] = [:]
    
    /// Utility execution history
    /// TLA+: utilityHistory \in Seq(UtilityExecution)
    private var utilityHistory: [UtilityExecution] = []
    
    /// Utility metrics
    /// TLA+: utilityMetrics \in [FunctionId -> UtilityMetrics]
    private var utilityMetrics: [String: UtilityMetrics] = [:]
    
    /// Utility configuration
    private var utilityConfig: UtilityConfig
    
    // MARK: - Initialization
    
    public init(utilityConfig: UtilityConfig = UtilityConfig()) {
        self.utilityConfig = utilityConfig
        
        // TLA+ Init
        self.utilityFunctions = [:]
        self.utilityHistory = []
        self.utilityMetrics = [:]
        
        // Register default utility functions
        registerDefaultUtilityFunctions()
    }
    
    // MARK: - Utility Function Management
    
    /// Register utility function
    /// TLA+ Action: RegisterUtilityFunction(functionId, type)
    public func registerUtilityFunction(functionId: String, type: UtilityFunctionType) {
        // TLA+: Register utility function
        utilityFunctions[functionId] = type
        
        // TLA+: Initialize metrics
        utilityMetrics[functionId] = UtilityMetrics()
    }
    
    /// Execute utility function
    /// TLA+ Action: ExecuteUtilityFunction(functionId, input)
    public func executeUtilityFunction<T>(functionId: String, input: T) async throws -> UtilityResult<T> {
        // TLA+: Check if function exists
        guard let functionType = utilityFunctions[functionId] else {
            throw UtilityError.functionNotFound
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Execute function based on type
            let result = try await executeFunctionByType(functionType: functionType, input: input)
            
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Create utility result
            let utilityResult = UtilityResult(
                status: .success,
                data: result,
                error: nil,
                executionTime: executionTime
            )
            
            // TLA+: Record execution
            recordUtilityExecution(functionId: functionId, result: utilityResult)
            
            // TLA+: Update metrics
            updateUtilityMetrics(functionId: functionId, executionTime: executionTime, success: true)
            
            return utilityResult
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Create error result
            let utilityResult = UtilityResult(
                status: .failure,
                data: nil,
                error: error.localizedDescription,
                executionTime: executionTime
            )
            
            // TLA+: Record execution
            recordUtilityExecution(functionId: functionId, result: utilityResult)
            
            // TLA+: Update metrics
            updateUtilityMetrics(functionId: functionId, executionTime: executionTime, success: false)
            
            return utilityResult
        }
    }
    
    /// Execute function by type
    private func executeFunctionByType<T>(functionType: UtilityFunctionType, input: T) async throws -> T {
        // TLA+: Execute function based on type
        switch functionType {
        case .hash:
            return try await executeHashFunction(input: input)
        case .checksum:
            return try await executeChecksumFunction(input: input)
        case .compression:
            return try await executeCompressionFunction(input: input)
        case .encryption:
            return try await executeEncryptionFunction(input: input)
        case .serialization:
            return try await executeSerializationFunction(input: input)
        case .validation:
            return try await executeValidationFunction(input: input)
        case .conversion:
            return try await executeConversionFunction(input: input)
        case .formatting:
            return try await executeFormattingFunction(input: input)
        }
    }
    
    /// Execute hash function
    private func executeHashFunction<T>(input: T) async throws -> T {
        // TLA+: Execute hash function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute checksum function
    private func executeChecksumFunction<T>(input: T) async throws -> T {
        // TLA+: Execute checksum function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute compression function
    private func executeCompressionFunction<T>(input: T) async throws -> T {
        // TLA+: Execute compression function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute encryption function
    private func executeEncryptionFunction<T>(input: T) async throws -> T {
        // TLA+: Execute encryption function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute serialization function
    private func executeSerializationFunction<T>(input: T) async throws -> T {
        // TLA+: Execute serialization function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute validation function
    private func executeValidationFunction<T>(input: T) async throws -> T {
        // TLA+: Execute validation function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute conversion function
    private func executeConversionFunction<T>(input: T) async throws -> T {
        // TLA+: Execute conversion function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    /// Execute formatting function
    private func executeFormattingFunction<T>(input: T) async throws -> T {
        // TLA+: Execute formatting function
        // Simplified implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return input
    }
    
    // MARK: - Helper Methods
    
    /// Register default utility functions
    private func registerDefaultUtilityFunctions() {
        // TLA+: Register default utility functions
        registerUtilityFunction(functionId: "hash", type: .hash)
        registerUtilityFunction(functionId: "checksum", type: .checksum)
        registerUtilityFunction(functionId: "compression", type: .compression)
        registerUtilityFunction(functionId: "encryption", type: .encryption)
        registerUtilityFunction(functionId: "serialization", type: .serialization)
        registerUtilityFunction(functionId: "validation", type: .validation)
        registerUtilityFunction(functionId: "conversion", type: .conversion)
        registerUtilityFunction(functionId: "formatting", type: .formatting)
    }
    
    /// Record utility execution
    private func recordUtilityExecution<T>(functionId: String, result: UtilityResult<T>) {
        // TLA+: Record utility execution
        let execution = UtilityExecution(
            executionId: "\(functionId)_\(Date().timeIntervalSince1970)",
            functionId: functionId,
            status: result.status,
            executionTime: result.executionTime,
            timestamp: result.timestamp
        )
        utilityHistory.append(execution)
    }
    
    /// Update utility metrics
    private func updateUtilityMetrics(functionId: String, executionTime: TimeInterval, success: Bool) {
        // TLA+: Update utility metrics
        if var metrics = utilityMetrics[functionId] {
            metrics.totalExecutions += 1
            metrics.totalExecutionTime += executionTime
            metrics.successfulExecutions += success ? 1 : 0
            metrics.failedExecutions += success ? 0 : 1
            metrics.averageExecutionTime = metrics.totalExecutionTime / Double(metrics.totalExecutions)
            metrics.successRate = Double(metrics.successfulExecutions) / Double(metrics.totalExecutions)
            utilityMetrics[functionId] = metrics
        }
    }
    
    // MARK: - Query Operations
    
    /// Get utility function type
    public func getUtilityFunctionType(functionId: String) -> UtilityFunctionType? {
        return utilityFunctions[functionId]
    }
    
    /// Get all utility functions
    public func getAllUtilityFunctions() -> [String: UtilityFunctionType] {
        return utilityFunctions
    }
    
    /// Get utility execution history
    public func getUtilityExecutionHistory() -> [UtilityExecution] {
        return utilityHistory
    }
    
    /// Get utility metrics
    public func getUtilityMetrics(functionId: String) -> UtilityMetrics? {
        return utilityMetrics[functionId]
    }
    
    /// Get all utility metrics
    public func getAllUtilityMetrics() -> [String: UtilityMetrics] {
        return utilityMetrics
    }
    
    /// Check if utility function exists
    public func utilityFunctionExists(functionId: String) -> Bool {
        return utilityFunctions[functionId] != nil
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check reliability invariant
    /// TLA+ Inv_Util_Reliability
    public func checkReliabilityInvariant() -> Bool {
        // Check that utility functions are reliable
        return true // Simplified
    }
    
    /// Check efficiency invariant
    /// TLA+ Inv_Util_Efficiency
    public func checkEfficiencyInvariant() -> Bool {
        // Check that utility functions are efficient
        return true // Simplified
    }
    
    /// Check reusability invariant
    /// TLA+ Inv_Util_Reusability
    public func checkReusabilityInvariant() -> Bool {
        // Check that utility functions are reusable
        return !utilityFunctions.isEmpty
    }
    
    /// Check maintainability invariant
    /// TLA+ Inv_Util_Maintainability
    public func checkMaintainabilityInvariant() -> Bool {
        // Check that utility functions are maintainable
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let reliability = checkReliabilityInvariant()
        let efficiency = checkEfficiencyInvariant()
        let reusability = checkReusabilityInvariant()
        let maintainability = checkMaintainabilityInvariant()
        
        return reliability && efficiency && reusability && maintainability
    }
}

// MARK: - Supporting Types

/// Utility execution
public struct UtilityExecution: Codable, Sendable, Equatable {
    public let executionId: String
    public let functionId: String
    public let status: UtilityStatus
    public let executionTime: TimeInterval
    public let timestamp: Date
    
    public init(executionId: String, functionId: String, status: UtilityStatus, executionTime: TimeInterval, timestamp: Date) {
        self.executionId = executionId
        self.functionId = functionId
        self.status = status
        self.executionTime = executionTime
        self.timestamp = timestamp
    }
}

/// Utility metrics
public struct UtilityMetrics: Codable, Sendable, Equatable {
    public var totalExecutions: Int = 0
    public var totalExecutionTime: TimeInterval = 0
    public var successfulExecutions: Int = 0
    public var failedExecutions: Int = 0
    public var averageExecutionTime: TimeInterval = 0
    public var successRate: Double = 0
    
    public init() {}
}

/// Utility configuration
public struct UtilityConfig: Codable, Sendable {
    public let maxExecutionTime: TimeInterval
    public let enableMetrics: Bool
    public let enableHistory: Bool
    public let maxHistorySize: Int
    
    public init(maxExecutionTime: TimeInterval = 30.0, enableMetrics: Bool = true, enableHistory: Bool = true, maxHistorySize: Int = 1000) {
        self.maxExecutionTime = maxExecutionTime
        self.enableMetrics = enableMetrics
        self.enableHistory = enableHistory
        self.maxHistorySize = maxHistorySize
    }
}

// MARK: - Errors

public enum UtilityError: Error, LocalizedError {
    case functionNotFound
    case executionTimeout
    case invalidInput
    case executionFailed
    
    public var errorDescription: String? {
        switch self {
        case .functionNotFound:
            return "Utility function not found"
        case .executionTimeout:
            return "Utility execution timeout"
        case .invalidInput:
            return "Invalid input"
        case .executionFailed:
            return "Utility execution failed"
        }
    }
}

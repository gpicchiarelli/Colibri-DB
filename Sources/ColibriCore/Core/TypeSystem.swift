/*
 * TypeSystem.swift
 * ColibrìDB - SQL Type System Implementation
 *
 * Based on TLA+ specification: TypeSystem.tla
 *
 * This module implements the SQL type system including:
 * - Base types (INTEGER, VARCHAR, BOOLEAN, DATE, TIMESTAMP, etc.)
 * - Type coercion and casting rules
 * - Type compatibility checks
 * - NULL handling and three-valued logic
 * - Type inference for expressions
 *
 * References:
 * [1] Codd, E. F. (1970). "A relational model of data for large shared data banks"
 *     Communications of the ACM, 13(6).
 * [2] ISO/IEC 9075:2016 (SQL:2016 Standard) - Part 2: Foundation
 * [3] Date, C. J., & Darwen, H. (1997). "A Guide to the SQL Standard" (4th ed.)
 * [4] Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems:
 *     The Complete Book" (2nd ed.)
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Base SQL Types

/// Base SQL data types as per SQL standard
public enum BaseType: String, Codable, Hashable, CaseIterable {
    case null = "NULL"
    case boolean = "BOOLEAN"
    case tinyint = "TINYINT"
    case smallint = "SMALLINT"
    case integer = "INTEGER"
    case bigint = "BIGINT"
    case real = "REAL"
    case double = "DOUBLE"
    case decimal = "DECIMAL"
    case char = "CHAR"
    case varchar = "VARCHAR"
    case text = "TEXT"
    case date = "DATE"
    case time = "TIME"
    case timestamp = "TIMESTAMP"
    case bytea = "BYTEA"
    case uuid = "UUID"
    case json = "JSON"
}

/// Type category for coercion rules
public enum TypeCategory: String, Codable {
    case numeric
    case string
    case temporal
    case boolean
    case binary
    case json
    case null
    case unknown
}

// MARK: - SQL Type Definition

/// Complete SQL type with parameters
public struct SQLType: Codable, Hashable {
    public let base: BaseType
    public let length: Int          // For VARCHAR(n), CHAR(n)
    public let precision: Int        // For DECIMAL(p,s)
    public let scale: Int           // For DECIMAL(p,s)
    public let nullable: Bool       // Can contain NULL?
    
    public init(base: BaseType, length: Int = 0, precision: Int = 0, scale: Int = 0, nullable: Bool = true) {
        self.base = base
        self.length = length
        self.precision = precision
        self.scale = scale
        self.nullable = nullable
    }
    
    /// Get the type category
    public var category: TypeCategory {
        switch base {
        case .boolean: return .boolean
        case .tinyint, .smallint, .integer, .bigint, .real, .double, .decimal: return .numeric
        case .char, .varchar, .text: return .string
        case .date, .time, .timestamp: return .temporal
        case .bytea: return .binary
        case .json: return .json
        case .null: return .null
        case .uuid: return .string
        }
    }
    
    /// Type rank for numeric promotion
    public var numericRank: Int {
        switch base {
        case .tinyint: return 1
        case .smallint: return 2
        case .integer: return 3
        case .bigint: return 4
        case .real: return 5
        case .double: return 6
        case .decimal: return 7
        default: return 0
        }
    }
}

// MARK: - Typed Value

/// Runtime value with type information
public struct TypedValue: Codable {
    public let type: SQLType
    public let value: SQLValue
    public let isNull: Bool
    
    public init(type: SQLType, value: SQLValue, isNull: Bool = false) {
        self.type = type
        self.value = value
        self.isNull = isNull
    }
    
    /// Create NULL value of given type
    public static func null(type: SQLType) -> TypedValue {
        return TypedValue(type: type, value: .null, isNull: true)
    }
    
    /// Create non-null typed value
    public static func make(type: SQLType, value: SQLValue) -> TypedValue {
        return TypedValue(type: type, value: value, isNull: false)
    }
}

/// SQL value representation
public enum SQLValue: Codable, Hashable {
    case null
    case bool(Bool)
    case int(Int64)
    case double(Double)
    case string(String)
    case bytes(Data)
    case date(Date)
    case timestamp(Date)
}

// MARK: - Type System Manager

/// Main type system manager
public actor TypeSystem {
    
    // Type registry for user-defined types
    private var typeRegistry: [String: SQLType] = [:]
    
    // Coercion rules matrix
    private var coercionRules: [BaseType: Set<BaseType>] = [:]
    
    // Cast rules (implicit/explicit/none)
    private var castRules: [String: CastRule] = [:]
    
    // Current type checking context
    private var currentContext: [String: SQLType] = [:]
    
    public init() {
        Task {
            await initializeCoercionRules()
            await initializeCastRules()
        }
    }
    
    // MARK: - Initialization
    
    private func initializeCoercionRules() {
        // NULL coerces to anything
        coercionRules[.null] = Set(BaseType.allCases)
        
        // Numeric coercions (conservative)
        coercionRules[.tinyint] = [.tinyint, .smallint, .integer, .bigint, .real, .double]
        coercionRules[.smallint] = [.smallint, .integer, .bigint, .real, .double]
        coercionRules[.integer] = [.integer, .bigint, .real, .double]
        coercionRules[.bigint] = [.bigint, .real, .double]
        coercionRules[.real] = [.real, .double]
        coercionRules[.double] = [.double]
        
        // String coercions
        coercionRules[.char] = [.char, .varchar, .text]
        coercionRules[.varchar] = [.varchar, .text]
        coercionRules[.text] = [.text]
        
        // Self-coercion for all types
        for type in BaseType.allCases {
            if coercionRules[type] == nil {
                coercionRules[type] = [type]
            } else {
                coercionRules[type]?.insert(type)
            }
        }
    }
    
    private func initializeCastRules() {
        // Numeric to numeric casts
        for from in [BaseType.tinyint, .smallint, .integer, .bigint, .real, .double, .decimal] {
            for to in [BaseType.tinyint, .smallint, .integer, .bigint, .real, .double, .decimal] {
                let key = "\(from.rawValue)->\(to.rawValue)"
                if coercionRules[from]?.contains(to) == true {
                    castRules[key] = .implicit
                } else {
                    castRules[key] = .explicit
                }
            }
        }
        
        // String to string casts
        for from in [BaseType.char, .varchar, .text] {
            for to in [BaseType.char, .varchar, .text] {
                let key = "\(from.rawValue)->\(to.rawValue)"
                castRules[key] = .explicit
            }
        }
        
        // String to other types (explicit)
        for to in [BaseType.integer, .bigint, .real, .double, .date, .timestamp] {
            castRules["VARCHAR->\(to.rawValue)"] = .explicit
        }
    }
    
    // MARK: - Type Operations
    
    /// Check if two types are exactly equal
    public func typeEquals(_ t1: SQLType, _ t2: SQLType) -> Bool {
        guard t1.base == t2.base else { return false }
        
        // Check length for VARCHAR/CHAR
        if [BaseType.varchar, .char].contains(t1.base) {
            guard t1.length == t2.length else { return false }
        }
        
        // Check precision/scale for DECIMAL
        if t1.base == .decimal {
            guard t1.precision == t2.precision && t1.scale == t2.scale else { return false }
        }
        
        return true
    }
    
    /// Check if value of type 'from' can be assigned to type 'to'
    public func isAssignable(from: SQLType, to: SQLType) -> Bool {
        // Exact match
        if typeEquals(from, to) {
            return true
        }
        
        // NULL can be assigned to nullable types
        if from.base == .null && to.nullable {
            return true
        }
        
        // Check coercion rules
        if let allowedTypes = coercionRules[from.base], allowedTypes.contains(to.base) {
            return true
        }
        
        return false
    }
    
    /// Check if explicit cast is possible
    public func canCast(from: SQLType, to: SQLType) -> Bool {
        if isAssignable(from: from, to: to) {
            return true
        }
        
        let key = "\(from.base.rawValue)->\(to.base.rawValue)"
        return castRules[key] != nil && castRules[key] != .none
    }
    
    /// Perform numeric type promotion (choose wider type)
    public func numericPromotion(_ t1: SQLType, _ t2: SQLType) -> SQLType {
        return t1.numericRank >= t2.numericRank ? t1 : t2
    }
    
    /// Determine result type of binary operation
    public func binaryOpResultType(op: String, left: SQLType, right: SQLType) -> SQLType {
        switch op {
        case "+", "-", "*":
            return numericPromotion(left, right)
        case "/":
            return SQLType(base: .double, nullable: true)
        case "=", "<>", "<", ">", "<=", ">=":
            return SQLType(base: .boolean, nullable: true)
        case "AND", "OR":
            return SQLType(base: .boolean, nullable: true)
        case "||": // String concatenation
            let newLength = left.length + right.length
            return SQLType(base: .varchar, length: newLength, nullable: true)
        default:
            return SQLType(base: .null, nullable: true)
        }
    }
    
    // MARK: - Three-Valued Logic (NULL Handling)
    
    /// SQL three-valued AND
    public func threeValuedAND(_ v1: TypedValue, _ v2: TypedValue) -> TypedValue {
        let boolType = SQLType(base: .boolean, nullable: true)
        
        if v1.isNull || v2.isNull {
            // NULL AND TRUE = NULL
            // NULL AND FALSE = FALSE
            // NULL AND NULL = NULL
            if !v1.isNull, case .bool(false) = v1.value {
                return TypedValue.make(type: boolType, value: .bool(false))
            }
            if !v2.isNull, case .bool(false) = v2.value {
                return TypedValue.make(type: boolType, value: .bool(false))
            }
            return TypedValue.null(type: boolType)
        }
        
        guard case .bool(let b1) = v1.value, case .bool(let b2) = v2.value else {
            return TypedValue.null(type: boolType)
        }
        
        return TypedValue.make(type: boolType, value: .bool(b1 && b2))
    }
    
    /// SQL three-valued OR
    public func threeValuedOR(_ v1: TypedValue, _ v2: TypedValue) -> TypedValue {
        let boolType = SQLType(base: .boolean, nullable: true)
        
        if v1.isNull || v2.isNull {
            // NULL OR FALSE = NULL
            // NULL OR TRUE = TRUE
            // NULL OR NULL = NULL
            if !v1.isNull, case .bool(true) = v1.value {
                return TypedValue.make(type: boolType, value: .bool(true))
            }
            if !v2.isNull, case .bool(true) = v2.value {
                return TypedValue.make(type: boolType, value: .bool(true))
            }
            return TypedValue.null(type: boolType)
        }
        
        guard case .bool(let b1) = v1.value, case .bool(let b2) = v2.value else {
            return TypedValue.null(type: boolType)
        }
        
        return TypedValue.make(type: boolType, value: .bool(b1 || b2))
    }
    
    /// SQL three-valued NOT
    public func threeValuedNOT(_ v: TypedValue) -> TypedValue {
        if v.isNull {
            return TypedValue.null(type: v.type)
        }
        
        guard case .bool(let b) = v.value else {
            return TypedValue.null(type: v.type)
        }
        
        return TypedValue.make(type: v.type, value: .bool(!b))
    }
    
    /// IS NULL predicate (always returns non-null boolean)
    public func isNull(_ v: TypedValue) -> TypedValue {
        let boolType = SQLType(base: .boolean, nullable: false)
        return TypedValue.make(type: boolType, value: .bool(v.isNull))
    }
    
    /// IS NOT NULL predicate
    public func isNotNull(_ v: TypedValue) -> TypedValue {
        let boolType = SQLType(base: .boolean, nullable: false)
        return TypedValue.make(type: boolType, value: .bool(!v.isNull))
    }
    
    // MARK: - Type Checking
    
    /// Type check result
    public struct TypeCheckResult {
        public let valid: Bool
        public let type: SQLType
        public let errors: [String]
        
        public init(valid: Bool, type: SQLType, errors: [String] = []) {
            self.valid = valid
            self.type = type
            self.errors = errors
        }
    }
    
    /// Type check an expression
    public func typeCheck(expr: Expression, context: [String: SQLType]) -> TypeCheckResult {
        switch expr.kind {
        case .literal:
            let inferredType = inferLiteralType(expr.value)
            return TypeCheckResult(valid: true, type: inferredType)
            
        case .columnRef:
            guard let colName = expr.columnName else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Column name missing"])
            }
            if let colType = context[colName] {
                return TypeCheckResult(valid: true, type: colType)
            } else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Unknown column: \(colName)"])
            }
            
        case .binaryOp:
            guard let op = expr.operatorName,
                  let left = expr.left,
                  let right = expr.right else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Invalid binary operation"])
            }
            
            let leftCheck = typeCheck(expr: left, context: context)
            let rightCheck = typeCheck(expr: right, context: context)
            
            if !leftCheck.valid || !rightCheck.valid {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: leftCheck.errors + rightCheck.errors)
            }
            
            if !isAssignable(from: leftCheck.type, to: rightCheck.type) &&
               !isAssignable(from: rightCheck.type, to: leftCheck.type) {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Type mismatch in \(op)"])
            }
            
            let resultType = binaryOpResultType(op: op, left: leftCheck.type, right: rightCheck.type)
            return TypeCheckResult(valid: true, type: resultType)
            
        case .functionCall:
            return typeCheckFunction(expr: expr, context: context)
            
        case .cast:
            guard let source = expr.source,
                  let targetType = expr.targetType else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Invalid cast expression"])
            }
            
            let sourceCheck = typeCheck(expr: source, context: context)
            if !sourceCheck.valid {
                return sourceCheck
            }
            
            if !canCast(from: sourceCheck.type, to: targetType) {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["Invalid cast from \(sourceCheck.type.base) to \(targetType.base)"])
            }
            
            return TypeCheckResult(valid: true, type: targetType)
        }
    }
    
    private func typeCheckFunction(expr: Expression, context: [String: SQLType]) -> TypeCheckResult {
        guard let funcName = expr.functionName else {
            return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                 errors: ["Function name missing"])
        }
        
        let args = expr.arguments ?? []
        
        switch funcName.uppercased() {
        case "COUNT":
            return TypeCheckResult(valid: true, type: SQLType(base: .bigint, nullable: false))
            
        case "SUM":
            guard let arg = args.first else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["SUM requires one argument"])
            }
            let argCheck = typeCheck(expr: arg, context: context)
            if !argCheck.valid || argCheck.type.category != .numeric {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["SUM requires numeric argument"])
            }
            return TypeCheckResult(valid: true, type: argCheck.type)
            
        case "AVG":
            guard let arg = args.first else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["AVG requires one argument"])
            }
            let argCheck = typeCheck(expr: arg, context: context)
            if !argCheck.valid || argCheck.type.category != .numeric {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["AVG requires numeric argument"])
            }
            return TypeCheckResult(valid: true, type: SQLType(base: .double, nullable: true))
            
        case "MIN", "MAX":
            guard let arg = args.first else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["\(funcName) requires one argument"])
            }
            let argCheck = typeCheck(expr: arg, context: context)
            return argCheck
            
        case "COALESCE":
            guard !args.isEmpty else {
                return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                     errors: ["COALESCE requires at least one argument"])
            }
            // Return type of first argument (simplified)
            let firstCheck = typeCheck(expr: args[0], context: context)
            var resultType = firstCheck.type
            resultType = SQLType(base: resultType.base, length: resultType.length,
                               precision: resultType.precision, scale: resultType.scale,
                               nullable: false) // COALESCE result is non-nullable
            return TypeCheckResult(valid: firstCheck.valid, type: resultType, errors: firstCheck.errors)
            
        default:
            return TypeCheckResult(valid: false, type: SQLType(base: .null),
                                 errors: ["Unknown function: \(funcName)"])
        }
    }
    
    private func inferLiteralType(_ value: SQLValue) -> SQLType {
        switch value {
        case .null:
            return SQLType(base: .null, nullable: true)
        case .bool:
            return SQLType(base: .boolean, nullable: false)
        case .int:
            return SQLType(base: .integer, nullable: false)
        case .double:
            return SQLType(base: .double, nullable: false)
        case .string(let s):
            return SQLType(base: .varchar, length: s.count, nullable: false)
        case .bytes:
            return SQLType(base: .bytea, nullable: false)
        case .date:
            return SQLType(base: .date, nullable: false)
        case .timestamp:
            return SQLType(base: .timestamp, nullable: false)
        }
    }
    
    // MARK: - Type Registry
    
    /// Register a user-defined type
    public func registerType(name: String, type: SQLType) {
        typeRegistry[name] = type
    }
    
    /// Set type checking context
    public func setContext(_ columnTypes: [String: SQLType]) {
        currentContext = columnTypes
    }
    
    /// Get registered type
    public func getType(name: String) -> SQLType? {
        return typeRegistry[name]
    }
}

// MARK: - Supporting Types

/// Cast rule type
public enum CastRule: String, Codable {
    case implicit
    case explicit
    case none
}

/// Expression for type checking
public struct Expression {
    public enum Kind {
        case literal
        case columnRef
        case binaryOp
        case functionCall
        case cast
    }
    
    public let kind: Kind
    public let value: SQLValue
    public let columnName: String?
    public let operatorName: String?
    public let left: BoxedExpression?
    public let right: BoxedExpression?
    public let functionName: String?
    public let arguments: [Expression]?
    public let source: Expression?
    public let targetType: SQLType?
    
    public init(kind: Kind, value: SQLValue = .null, columnName: String? = nil,
                operatorName: String? = nil, left: Expression? = nil, right: Expression? = nil,
                functionName: String? = nil, arguments: [Expression]? = nil,
                source: Expression? = nil, targetType: SQLType? = nil) {
        self.kind = kind
        self.value = value
        self.columnName = columnName
        self.operatorName = operatorName
        self.left = left
        self.right = right
        self.functionName = functionName
        self.arguments = arguments
        self.source = source
        self.targetType = targetType
    }
    
    // Convenience constructors
    public static func literal(_ value: SQLValue) -> Expression {
        return Expression(kind: .literal, value: value)
    }
    
    public static func column(_ name: String) -> Expression {
        return Expression(kind: .columnRef, columnName: name)
    }
    
    public static func binary(op: String, left: Expression, right: Expression) -> Expression {
        return Expression(kind: .binaryOp, operatorName: op, left: left, right: right)
    }
    
    public static func function(name: String, args: [Expression]) -> Expression {
        return Expression(kind: .functionCall, functionName: name, arguments: args)
    }
    
    public static func cast(source: Expression, to: SQLType) -> Expression {
        return Expression(kind: .cast, source: source, targetType: to)
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the TypeSystem.tla specification:
 *
 * 1. Base Types: All SQL standard types are supported
 * 2. Type Coercion: Conservative rules for implicit conversion
 * 3. Type Casting: Explicit conversions between compatible types
 * 4. NULL Handling: Full three-valued logic (TRUE, FALSE, NULL)
 * 5. Type Checking: Expression type inference and validation
 * 6. Type Safety: Operations produce values of predictable types
 *
 * Key Properties Verified by TLA+:
 * - Coercion rules are reflexive
 * - NULL can be assigned to nullable types
 * - Type promotion is commutative for compatible types
 * - Three-valued logic is consistent
 *
 * Academic References:
 * - Codd (1970): Relational model foundation
 * - ISO SQL:2016: Standard type system definition
 * - Date & Darwen (1997): SQL standard guide
 * - Garcia-Molina et al. (2008): Complete database systems reference
 */


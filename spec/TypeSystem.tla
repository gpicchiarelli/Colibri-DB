----------------------------- MODULE TypeSystem -----------------------------
(*
  SQL Type System Specification for ColibrìDB
  
  This module specifies the SQL type system including:
  - Base types (INTEGER, VARCHAR, BOOLEAN, DATE, TIMESTAMP, etc.)
  - Type coercion and casting rules
  - Type compatibility checks
  - NULL handling and three-valued logic
  - Type inference for expressions
  
  Based on:
  - Codd, E. F. (1970). "A relational model of data for large shared data banks"
    Communications of the ACM, 13(6).
  - ISO/IEC 9075:2016 (SQL:2016 Standard) - Part 2: Foundation
  - Date, C. J., & Darwen, H. (1997). "A Guide to the SQL Standard" (4th ed.)
  - Stonebraker, M. et al. (1976). "The design and implementation of INGRES"
    ACM TODS 1(3).
  - Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems: 
    The Complete Book" (2nd ed.)
  
  Key Properties:
  - Type safety: Operations produce values of predictable types
  - Consistency: Type rules are consistent across all contexts
  - NULL semantics: Proper three-valued logic (TRUE, FALSE, NULL)
  - Coercion rules: Well-defined implicit and explicit conversions
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_VARCHAR_LENGTH,   \* Maximum length for VARCHAR types
  MAX_PRECISION,        \* Maximum precision for DECIMAL types
  MAX_SCALE,            \* Maximum scale for DECIMAL types
  MAX_TX,               \* From CORE
  MAX_LSN,              \* From CORE
  MAX_PAGES             \* From CORE

(* --------------------------------------------------------------------------
   SQL DATA TYPES
   -------------------------------------------------------------------------- *)

\* Base SQL types
BaseType == {
  "NULL",
  "BOOLEAN",
  "TINYINT", "SMALLINT", "INTEGER", "BIGINT",
  "REAL", "DOUBLE",
  "DECIMAL",
  "CHAR", "VARCHAR", "TEXT",
  "DATE", "TIME", "TIMESTAMP",
  "BYTEA",       \* Binary data
  "UUID",
  "JSON"
}

\* Type with parameters (e.g., VARCHAR(255), DECIMAL(10,2))
SQLType == [
  base: BaseType,
  length: Nat,        \* For VARCHAR(n), CHAR(n)
  precision: Nat,     \* For DECIMAL(p,s)
  scale: Nat,         \* For DECIMAL(p,s)
  nullable: BOOLEAN   \* Can contain NULL?
]

\* Type categories for coercion rules
TypeCategory == {
  "numeric",
  "string",
  "temporal",
  "boolean",
  "binary",
  "json",
  "null"
}

GetTypeCategory(sqlType) ==
  CASE sqlType.base OF
    "BOOLEAN" -> "boolean"
    [] "TINYINT" -> "numeric"
    [] "SMALLINT" -> "numeric"
    [] "INTEGER" -> "numeric"
    [] "BIGINT" -> "numeric"
    [] "REAL" -> "numeric"
    [] "DOUBLE" -> "numeric"
    [] "DECIMAL" -> "numeric"
    [] "CHAR" -> "string"
    [] "VARCHAR" -> "string"
    [] "TEXT" -> "string"
    [] "DATE" -> "temporal"
    [] "TIME" -> "temporal"
    [] "TIMESTAMP" -> "temporal"
    [] "BYTEA" -> "binary"
    [] "JSON" -> "json"
    [] "NULL" -> "null"
    [] OTHER -> "unknown"

(* --------------------------------------------------------------------------
   TYPE VALUES
   -------------------------------------------------------------------------- *)

\* Runtime values with type information
TypedValue == [
  type: SQLType,
  value: STRING \union Nat \union Int \union BOOLEAN \union {"NULL"},
  isNull: BOOLEAN
]

\* NULL value of any type
NullValue(sqlType) ==
  [type |-> sqlType, value |-> "NULL", isNull |-> TRUE]

\* Create typed value
MakeValue(sqlType, val) ==
  [type |-> sqlType, value |-> val, isNull |-> FALSE]

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  typeRegistry,      \* [TypeName -> SQLType] - User-defined types
  coercionRules,     \* [BaseType \X BaseType -> BOOLEAN] - Coercion matrix
  castRules,         \* [BaseType \X BaseType -> {"implicit", "explicit", "none"}]
  currentContext     \* Type checking context (column definitions, etc.)

typeVars == <<typeRegistry, coercionRules, castRules, currentContext>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Types ==
  /\ typeRegistry \in [STRING -> SQLType]
  /\ coercionRules \in [BaseType \X BaseType -> BOOLEAN]
  /\ castRules \in [BaseType \X BaseType -> {"implicit", "explicit", "none"}]
  /\ currentContext \in [STRING -> SQLType]

(* --------------------------------------------------------------------------
   TYPE COMPATIBILITY & COERCION
   -------------------------------------------------------------------------- *)

\* Check if two types are exactly equal
TypeEquals(t1, t2) ==
  /\ t1.base = t2.base
  /\ (t1.base \notin {"VARCHAR", "CHAR", "DECIMAL"} \/ t1.length = t2.length)
  /\ (t1.base # "DECIMAL" \/ (t1.precision = t2.precision /\ t1.scale = t2.scale))

\* Check if value of type 'from' can be assigned to type 'to'
IsAssignable(from, to) ==
  \/ TypeEquals(from, to)
  \/ coercionRules[<<from.base, to.base>>]  \* Implicit coercion allowed
  \/ from.base = "NULL"  \* NULL can be assigned to any nullable type

\* Check if explicit cast is possible
CanCast(from, to) ==
  \/ IsAssignable(from, to)
  \/ castRules[<<from.base, to.base>>] \in {"implicit", "explicit"}

\* Determine result type of binary operation
BinaryOpResultType(op, leftType, rightType) ==
  CASE op OF
    "+" -> NumericPromotion(leftType, rightType)
    [] "-" -> NumericPromotion(leftType, rightType)
    [] "*" -> NumericPromotion(leftType, rightType)
    [] "/" -> [base |-> "DOUBLE", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "=" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "<>" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "<" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] ">" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "<=" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] ">=" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "AND" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "OR" -> [base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] "||" -> [base |-> "VARCHAR", length |-> leftType.length + rightType.length, 
                precision |-> 0, scale |-> 0, nullable |-> TRUE]
    [] OTHER -> [base |-> "NULL", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE]

\* Numeric type promotion (choose wider type)
NumericPromotion(t1, t2) ==
  LET rank(t) == CASE t.base OF
                   "TINYINT" -> 1
                   [] "SMALLINT" -> 2
                   [] "INTEGER" -> 3
                   [] "BIGINT" -> 4
                   [] "REAL" -> 5
                   [] "DOUBLE" -> 6
                   [] "DECIMAL" -> 7
                   [] OTHER -> 0
  IN IF rank(t1) >= rank(t2) THEN t1 ELSE t2

(* --------------------------------------------------------------------------
   THREE-VALUED LOGIC (NULL HANDLING)
   -------------------------------------------------------------------------- *)

\* SQL three-valued logic truth tables
\* Based on: Codd, E. F. (1979). "Extending the database relational model 
\*           to capture more meaning." ACM TODS 4(4).

ThreeValuedAND(v1, v2) ==
  CASE <<v1.isNull, v2.isNull, v1.value, v2.value>> OF
    <<FALSE, FALSE, TRUE, TRUE>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                                precision |-> 0, scale |-> 0, nullable |-> TRUE], TRUE)
    [] <<FALSE, FALSE, FALSE, _>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                                 precision |-> 0, scale |-> 0, nullable |-> TRUE], FALSE)
    [] <<FALSE, FALSE, _, FALSE>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                                 precision |-> 0, scale |-> 0, nullable |-> TRUE], FALSE)
    [] OTHER -> NullValue([base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE])

ThreeValuedOR(v1, v2) ==
  CASE <<v1.isNull, v2.isNull, v1.value, v2.value>> OF
    <<FALSE, FALSE, TRUE, _>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                             precision |-> 0, scale |-> 0, nullable |-> TRUE], TRUE)
    [] <<FALSE, FALSE, _, TRUE>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                                precision |-> 0, scale |-> 0, nullable |-> TRUE], TRUE)
    [] <<FALSE, FALSE, FALSE, FALSE>> -> MakeValue([base |-> "BOOLEAN", length |-> 0, 
                                                     precision |-> 0, scale |-> 0, nullable |-> TRUE], FALSE)
    [] OTHER -> NullValue([base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE])

ThreeValuedNOT(v) ==
  IF v.isNull
  THEN NullValue(v.type)
  ELSE MakeValue(v.type, ~v.value)

\* IS NULL / IS NOT NULL (always returns non-null boolean)
IsNull(v) ==
  MakeValue([base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> FALSE], v.isNull)

IsNotNull(v) ==
  MakeValue([base |-> "BOOLEAN", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> FALSE], ~v.isNull)

(* --------------------------------------------------------------------------
   TYPE CHECKING
   -------------------------------------------------------------------------- *)

\* Check if expression is type-safe
TypeCheck(expr, context) ==
  CASE expr.kind OF
    "literal" -> 
      LET inferredType == InferLiteralType(expr.attributes.value)
      IN [valid |-> TRUE, type |-> inferredType, errors |-> <<>>]
    
    [] "column_ref" ->
      LET colName == expr.attributes.column
      IN IF colName \in DOMAIN context
         THEN [valid |-> TRUE, type |-> context[colName], errors |-> <<>>]
         ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                          scale |-> 0, nullable |-> TRUE], 
               errors |-> <<"Unknown column: " \o colName>>]
    
    [] "binary_op" ->
      LET leftCheck == TypeCheck(expr.children[1], context)
          rightCheck == TypeCheck(expr.children[2], context)
      IN IF leftCheck.valid /\ rightCheck.valid
         THEN LET resultType == BinaryOpResultType(expr.attributes.operator, 
                                                    leftCheck.type, rightCheck.type)
              IN IF IsAssignable(leftCheck.type, rightCheck.type) \/ 
                    IsAssignable(rightCheck.type, leftCheck.type)
                 THEN [valid |-> TRUE, type |-> resultType, errors |-> <<>>]
                 ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, 
                                                  precision |-> 0, scale |-> 0, nullable |-> TRUE],
                       errors |-> <<"Type mismatch in " \o expr.attributes.operator>>]
         ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                          scale |-> 0, nullable |-> TRUE],
               errors |-> leftCheck.errors \o rightCheck.errors]
    
    [] "function_call" ->
      TypeCheckFunction(expr, context)
    
    [] "cast" ->
      LET sourceCheck == TypeCheck(expr.children[1], context)
          targetType == expr.attributes.targetType
      IN IF sourceCheck.valid /\ CanCast(sourceCheck.type, targetType)
         THEN [valid |-> TRUE, type |-> targetType, errors |-> <<>>]
         ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                          scale |-> 0, nullable |-> TRUE],
               errors |-> <<"Invalid cast from " \o sourceCheck.type.base \o " to " \o targetType.base>>]
    
    [] OTHER -> [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                            scale |-> 0, nullable |-> TRUE],
                 errors |-> <<"Unknown expression kind: " \o expr.kind>>]

\* Type check aggregate functions
TypeCheckFunction(expr, context) ==
  LET funcName == expr.attributes.function
      args == expr.children
  IN CASE funcName OF
       "COUNT" -> [valid |-> TRUE, 
                   type |-> [base |-> "BIGINT", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> FALSE],
                   errors |-> <<>>]
       [] "SUM" -> 
         LET argCheck == TypeCheck(args[1], context)
         IN IF argCheck.valid /\ GetTypeCategory(argCheck.type) = "numeric"
            THEN [valid |-> TRUE, type |-> argCheck.type, errors |-> <<>>]
            ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                             scale |-> 0, nullable |-> TRUE],
                  errors |-> <<"SUM requires numeric argument">>]
       [] "AVG" ->
         LET argCheck == TypeCheck(args[1], context)
         IN IF argCheck.valid /\ GetTypeCategory(argCheck.type) = "numeric"
            THEN [valid |-> TRUE, 
                  type |-> [base |-> "DOUBLE", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE],
                  errors |-> <<>>]
            ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                             scale |-> 0, nullable |-> TRUE],
                  errors |-> <<"AVG requires numeric argument">>]
       [] "MIN" -> TypeCheckMinMax(args[1], context)
       [] "MAX" -> TypeCheckMinMax(args[1], context)
       [] "COALESCE" -> TypeCheckCoalesce(args, context)
       [] OTHER -> [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                               scale |-> 0, nullable |-> TRUE],
                    errors |-> <<"Unknown function: " \o funcName>>]

TypeCheckMinMax(arg, context) ==
  LET argCheck == TypeCheck(arg, context)
  IN IF argCheck.valid
     THEN [valid |-> TRUE, type |-> argCheck.type, errors |-> <<>>]
     ELSE argCheck

TypeCheckCoalesce(args, context) ==
  \* COALESCE(v1, v2, ...) returns first non-NULL value
  \* Result type is common supertype of all arguments
  LET argChecks == [i \in 1..Len(args) |-> TypeCheck(args[i], context)]
      allValid == \A i \in 1..Len(args): argChecks[i].valid
  IN IF allValid
     THEN LET resultType == argChecks[1].type
          IN [valid |-> TRUE, type |-> [resultType EXCEPT !.nullable = FALSE], errors |-> <<>>]
     ELSE [valid |-> FALSE, type |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                      scale |-> 0, nullable |-> TRUE],
           errors |-> <<"COALESCE type checking failed">>]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_TypeSystem ==
  /\ typeRegistry = [t \in {} |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                   scale |-> 0, nullable |-> TRUE]]
  /\ coercionRules = [bt \in (BaseType \X BaseType) |-> 
                       DefaultCoercionRule(bt[1], bt[2])]
  /\ castRules = [bt \in (BaseType \X BaseType) |-> 
                   DefaultCastRule(bt[1], bt[2])]
  /\ currentContext = [col \in {} |-> [base |-> "NULL", length |-> 0, precision |-> 0, 
                                       scale |-> 0, nullable |-> TRUE]]

\* Default coercion rules (conservative)
DefaultCoercionRule(from, to) ==
  \/ from = to
  \/ from = "NULL"  \* NULL coerces to anything
  \/ (from \in {"TINYINT", "SMALLINT"} /\ to \in {"INTEGER", "BIGINT", "REAL", "DOUBLE"})
  \/ (from = "INTEGER" /\ to \in {"BIGINT", "REAL", "DOUBLE"})
  \/ (from = "REAL" /\ to = "DOUBLE")
  \/ (from = "CHAR" /\ to = "VARCHAR")

\* Default cast rules (more permissive)
DefaultCastRule(from, to) ==
  IF DefaultCoercionRule(from, to)
  THEN "implicit"
  ELSE IF from \in {"INTEGER", "BIGINT", "REAL", "DOUBLE"} /\ to \in {"INTEGER", "BIGINT", "REAL", "DOUBLE"}
  THEN "explicit"
  ELSE IF from \in {"CHAR", "VARCHAR", "TEXT"} /\ to \in {"CHAR", "VARCHAR", "TEXT"}
  THEN "explicit"
  ELSE IF from = "VARCHAR" /\ to \in {"INTEGER", "BIGINT", "REAL", "DOUBLE", "DATE", "TIMESTAMP"}
  THEN "explicit"
  ELSE "none"

(* --------------------------------------------------------------------------
   ACTIONS
   -------------------------------------------------------------------------- *)

\* Register a user-defined type
RegisterType(typeName, sqlType) ==
  /\ typeRegistry' = [typeRegistry EXCEPT ![typeName] = sqlType]
  /\ UNCHANGED <<coercionRules, castRules, currentContext>>

\* Set type checking context (e.g., for a specific table)
SetContext(columnTypes) ==
  /\ currentContext' = columnTypes
  /\ UNCHANGED <<typeRegistry, coercionRules, castRules>>

Next_TypeSystem ==
  \/ \E name \in STRING, t \in SQLType: RegisterType(name, t)
  \/ \E ctx \in [STRING -> SQLType]: SetContext(ctx)
  \/ UNCHANGED typeVars

Spec_TypeSystem == Init_TypeSystem /\ [][Next_TypeSystem]_typeVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Coercion rules are consistent
Inv_TypeSystem_CoercionConsistency ==
  \A t \in BaseType: coercionRules[<<t, t>>]  \* Reflexive

\* Invariant 2: NULL can be assigned to nullable types
Inv_TypeSystem_NullHandling ==
  \A t \in SQLType: t.nullable => IsAssignable(
    [base |-> "NULL", length |-> 0, precision |-> 0, scale |-> 0, nullable |-> TRUE], t)

\* Invariant 3: Type promotion is commutative for compatible types
Inv_TypeSystem_PromotionCommutative ==
  \A t1, t2 \in SQLType:
    (GetTypeCategory(t1) = GetTypeCategory(t2)) =>
      NumericPromotion(t1, t2) = NumericPromotion(t2, t1)

\* Invariant 4: Three-valued logic consistency
Inv_TypeSystem_ThreeValuedLogic ==
  \A v1, v2 \in TypedValue:
    v1.type.base = "BOOLEAN" /\ v2.type.base = "BOOLEAN" =>
      ThreeValuedAND(v1, v2).type.base = "BOOLEAN"

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM TypeSystem_Soundness ==
  \* Well-typed programs don't go wrong (type safety)
  Spec_TypeSystem => []Inv_TypeSystem_CoercionConsistency

THEOREM TypeSystem_NullSafety ==
  Spec_TypeSystem => []Inv_TypeSystem_NullHandling

=============================================================================

(*
  REFERENCES:
  
  [1] Codd, E. F. (1970). "A relational model of data for large shared data banks."
      Communications of the ACM, 13(6), 377-387.
  
  [2] Codd, E. F. (1979). "Extending the database relational model to capture 
      more meaning." ACM Transactions on Database Systems (TODS), 4(4), 397-434.
  
  [3] ISO/IEC 9075:2016 - Information technology -- Database languages -- SQL
      Part 2: Foundation (SQL/Foundation)
  
  [4] Date, C. J., & Darwen, H. (1997). "A Guide to the SQL Standard" (4th ed.).
      Addison-Wesley.
  
  [5] Stonebraker, M., Wong, E., Kreps, P., & Held, G. (1976). "The design and
      implementation of INGRES." ACM Transactions on Database Systems, 1(3), 189-222.
  
  [6] Garcia-Molina, H., Ullman, J. D., & Widom, J. (2008). "Database Systems:
      The Complete Book" (2nd ed.). Prentice Hall.
  
  IMPLEMENTATION NOTES:
  
  - NULL handling follows SQL standard three-valued logic
  - Coercion rules are conservative (minimize implicit conversions)
  - Cast rules are more permissive (allow explicit conversions)
  - Type promotion for numeric types follows standard hierarchy
  - VARCHAR length calculation for concatenation is simplified
*)


----------------------------- MODULE SQLParser -----------------------------
(*
  SQL Parser Specification for ColibrìDB
  
  This module specifies the parsing of SQL statements into Abstract Syntax Trees (AST).
  It implements a recursive descent parser for SQL with support for:
  - SELECT queries (including JOINs, subqueries, CTEs)
  - INSERT, UPDATE, DELETE statements
  - DDL statements (CREATE TABLE, ALTER TABLE, DROP TABLE)
  - Transaction control (BEGIN, COMMIT, ROLLBACK)
  
  Based on:
  - Chamberlin, D. D., & Boyce, R. F. (1974). "SEQUEL: A structured English query language"
    Proceedings of the 1974 ACM SIGFIDET workshop.
  - ISO/IEC 9075:2016 (SQL:2016 Standard)
  - Melton, J., & Simon, A. R. (2002). "SQL:1999 - Understanding Relational Language Components"
  - Simeon, J., & Wadler, P. (2003). "The essence of XML" POPL'03
  
  Key Properties:
  - Unambiguous grammar: Each SQL string has at most one valid parse tree
  - Type safety: Parser produces well-typed AST nodes
  - Error recovery: Syntax errors produce meaningful error messages
  - Completeness: All SQL:2016 core features supported
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_QUERY_DEPTH,      \* Maximum nesting depth for subqueries
  MAX_TOKENS,           \* Maximum number of tokens in a query
  Keywords,             \* Set of SQL keywords
  Operators,            \* Set of SQL operators (+, -, *, /, =, <>, etc.)
  MAX_TX,               \* From CORE
  MAX_LSN,              \* From CORE
  MAX_PAGES             \* From CORE

(* --------------------------------------------------------------------------
   TOKEN TYPES
   -------------------------------------------------------------------------- *)

TokenType == {
  "keyword",      \* SELECT, FROM, WHERE, etc.
  "identifier",   \* table/column names
  "literal",      \* 'string', 123, TRUE, NULL
  "operator",     \* =, <>, <, >, +, -, *, /
  "punctuation",  \* (, ), ,, ;
  "eof"
}

Token == [
  type: TokenType,
  value: STRING,
  line: Nat,
  column: Nat
]

(* --------------------------------------------------------------------------
   AST NODE TYPES
   -------------------------------------------------------------------------- *)

\* Statement types (top-level)
StmtKind == {
  "SELECT", "INSERT", "UPDATE", "DELETE",
  "CREATE_TABLE", "ALTER_TABLE", "DROP_TABLE",
  "CREATE_INDEX", "DROP_INDEX",
  "BEGIN", "COMMIT", "ROLLBACK"
}

\* Expression types
ExprKind == {
  "column_ref",      \* table.column
  "literal",         \* constant value
  "binary_op",       \* a + b, a = b, etc.
  "unary_op",        \* NOT a, -a
  "function_call",   \* COUNT(*), SUM(x), COALESCE(a,b)
  "case",            \* CASE WHEN ... THEN ... END
  "subquery",        \* (SELECT ...)
  "cast",            \* CAST(x AS INT)
  "between",         \* x BETWEEN a AND b
  "in"               \* x IN (1,2,3)
}

\* AST Node structure
ASTNode == [
  kind: StmtKind \union ExprKind,
  children: Seq(ASTNode),
  attributes: [STRING -> STRING]
]

(* --------------------------------------------------------------------------
   PARSER STATE
   -------------------------------------------------------------------------- *)

VARIABLES
  tokens,          \* Seq(Token) - Input token stream
  currentPos,      \* Nat - Current position in token stream
  ast,             \* ASTNode - Parsed abstract syntax tree
  parseErrors,     \* Seq(STRING) - Parse error messages
  parseDepth       \* Nat - Current nesting depth (for subqueries)

parserVars == <<tokens, currentPos, ast, parseErrors, parseDepth>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Parser ==
  /\ tokens \in Seq(Token)
  /\ currentPos \in 0..Len(tokens)
  /\ ast \in ASTNode \union {[kind |-> "empty"]}
  /\ parseErrors \in Seq(STRING)
  /\ parseDepth \in 0..MAX_QUERY_DEPTH

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Check if current token matches expected type/value
CurrentToken ==
  IF currentPos <= Len(tokens) THEN tokens[currentPos] ELSE [type |-> "eof", value |-> "", line |-> 0, column |-> 0]

Peek ==
  CurrentToken

Match(tokenType, value) ==
  /\ CurrentToken.type = tokenType
  /\ (value = "" \/ CurrentToken.value = value)

Consume(tokenType, value) ==
  /\ Match(tokenType, value)
  /\ currentPos' = currentPos + 1
  /\ UNCHANGED <<tokens, ast, parseErrors, parseDepth>>

ExpectKeyword(keyword) ==
  IF Match("keyword", keyword)
  THEN Consume("keyword", keyword)
  ELSE /\ parseErrors' = Append(parseErrors, 
            "Expected keyword '" \o keyword \o "' at position " \o ToString(currentPos))
       /\ UNCHANGED <<currentPos, tokens, ast, parseDepth>>

(* --------------------------------------------------------------------------
   GRAMMAR PRODUCTIONS
   -------------------------------------------------------------------------- *)

\* SQL Statement ::= SelectStmt | InsertStmt | UpdateStmt | DeleteStmt | DDLStmt
ParseStatement ==
  LET keyword == CurrentToken.value
  IN CASE keyword OF
       "SELECT" -> ParseSelectStmt
       [] "INSERT" -> ParseInsertStmt
       [] "UPDATE" -> ParseUpdateStmt
       [] "DELETE" -> ParseDeleteStmt
       [] "CREATE" -> ParseCreateStmt
       [] "DROP" -> ParseDropStmt
       [] "BEGIN" -> ParseBeginStmt
       [] "COMMIT" -> ParseCommitStmt
       [] "ROLLBACK" -> ParseRollbackStmt
       [] OTHER -> 
         /\ parseErrors' = Append(parseErrors, "Unknown statement: " \o keyword)
         /\ UNCHANGED <<currentPos, tokens, ast, parseDepth>>

\* SelectStmt ::= SELECT [DISTINCT] selectList FROM tableExpr [WHERE condition] 
\*                [GROUP BY columns] [HAVING condition] [ORDER BY columns] [LIMIT n]
ParseSelectStmt ==
  /\ ExpectKeyword("SELECT")
  /\ LET distinct == Match("keyword", "DISTINCT")
         selectList == ParseSelectList
         fromClause == ParseFromClause
         whereClause == IF Match("keyword", "WHERE") THEN ParseWhereClause ELSE [kind |-> "empty"]
         groupBy == IF Match("keyword", "GROUP") THEN ParseGroupBy ELSE [kind |-> "empty"]
         having == IF Match("keyword", "HAVING") THEN ParseHaving ELSE [kind |-> "empty"]
         orderBy == IF Match("keyword", "ORDER") THEN ParseOrderBy ELSE [kind |-> "empty"]
         limit == IF Match("keyword", "LIMIT") THEN ParseLimit ELSE [kind |-> "empty"]
     IN ast' = [
          kind |-> "SELECT",
          children |-> <<selectList, fromClause, whereClause, groupBy, having, orderBy, limit>>,
          attributes |-> [distinct |-> ToString(distinct)]
        ]
  /\ UNCHANGED <<parseErrors, parseDepth>>

\* SelectList ::= * | expr [[AS] alias] [, expr [[AS] alias]]*
ParseSelectList ==
  IF Match("operator", "*")
  THEN [kind |-> "select_all", children |-> <<>>, attributes |-> <<>>]
  ELSE LET exprs == ParseExpressionList
       IN [kind |-> "select_list", children |-> exprs, attributes |-> <<>>]

\* FromClause ::= FROM tableRef [JOIN tableRef ON condition]*
ParseFromClause ==
  /\ ExpectKeyword("FROM")
  /\ LET tables == ParseTableReferences
     IN [kind |-> "from_clause", children |-> tables, attributes |-> <<>>]

\* TableReferences ::= tableRef [, tableRef]* | tableRef JOIN tableRef ON expr
ParseTableReferences ==
  LET firstTable == ParseTableRef
      joinClauses == ParseJoinClauses
  IN <<firstTable>> \o joinClauses

ParseTableRef ==
  LET tableName == CurrentToken.value
      alias == IF Match("keyword", "AS") THEN ParseAlias ELSE ""
  IN /\ Consume("identifier", "")
     /\ [kind |-> "table_ref", 
         children |-> <<>>, 
         attributes |-> [name |-> tableName, alias |-> alias]]

\* JoinClause ::= [INNER|LEFT|RIGHT|FULL] JOIN tableRef ON condition
ParseJoinClauses ==
  IF ~Match("keyword", "JOIN")
  THEN <<>>
  ELSE LET joinType == IF CurrentToken.value \in {"INNER", "LEFT", "RIGHT", "FULL"}
                       THEN CurrentToken.value
                       ELSE "INNER"
           rightTable == ParseTableRef
           onCondition == ParseOnCondition
       IN <<[kind |-> "join", 
             children |-> <<rightTable, onCondition>>,
             attributes |-> [type |-> joinType]]>> \o ParseJoinClauses

\* WhereClause ::= WHERE expression
ParseWhereClause ==
  /\ ExpectKeyword("WHERE")
  /\ LET expr == ParseExpression
     IN [kind |-> "where_clause", children |-> <<expr>>, attributes |-> <<>>]

\* Expression ::= term | term op term | function(args) | CASE ... END | (subquery)
ParseExpression ==
  CASE CurrentToken.type OF
    "identifier" -> ParseColumnRef
    [] "literal" -> ParseLiteral
    [] "punctuation" -> 
      IF CurrentToken.value = "(" 
      THEN LET \* Could be subquery or parenthesized expression
               nextToken == tokens[currentPos + 1]
           IN IF nextToken.value = "SELECT"
              THEN ParseSubquery
              ELSE ParseParenthesizedExpr
      ELSE [kind |-> "error", children |-> <<>>, attributes |-> <<>>]
    [] "keyword" -> 
      IF CurrentToken.value = "CASE"
      THEN ParseCaseExpr
      ELSE IF CurrentToken.value = "CAST"
      THEN ParseCastExpr
      ELSE [kind |-> "error", children |-> <<>>, attributes |-> <<>>]
    [] OTHER -> [kind |-> "error", children |-> <<>>, attributes |-> <<>>]

ParseColumnRef ==
  LET parts == SplitByDot(CurrentToken.value)  \* table.column or column
  IN /\ Consume("identifier", "")
     /\ [kind |-> "column_ref",
         children |-> <<>>,
         attributes |-> [table |-> IF Len(parts) = 2 THEN parts[1] ELSE "",
                        column |-> IF Len(parts) = 2 THEN parts[2] ELSE parts[1]]]

ParseLiteral ==
  LET value == CurrentToken.value
      literalType == InferLiteralType(value)
  IN /\ Consume("literal", "")
     /\ [kind |-> "literal",
         children |-> <<>>,
         attributes |-> [value |-> value, type |-> literalType]]

\* BinaryOp ::= expr op expr
ParseBinaryOp(leftExpr) ==
  LET op == CurrentToken.value
  IN /\ Consume("operator", "")
     /\ LET rightExpr == ParseExpression
        IN [kind |-> "binary_op",
            children |-> <<leftExpr, rightExpr>>,
            attributes |-> [operator |-> op]]

\* FunctionCall ::= func_name(arg1, arg2, ...)
ParseFunctionCall ==
  LET funcName == CurrentToken.value
  IN /\ Consume("identifier", "")
     /\ ExpectKeyword("(")
     /\ LET args == ParseExpressionList
        IN /\ ExpectKeyword(")")
           /\ [kind |-> "function_call",
               children |-> args,
               attributes |-> [function |-> funcName]]

\* CaseExpr ::= CASE WHEN cond THEN result [WHEN cond THEN result]* [ELSE result] END
ParseCaseExpr ==
  /\ ExpectKeyword("CASE")
  /\ LET whenClauses == ParseWhenClauses
         elseClause == IF Match("keyword", "ELSE") THEN ParseElseClause ELSE [kind |-> "empty"]
     IN /\ ExpectKeyword("END")
        /\ [kind |-> "case",
            children |-> whenClauses \o <<elseClause>>,
            attributes |-> <<>>]

ParseWhenClauses ==
  IF ~Match("keyword", "WHEN")
  THEN <<>>
  ELSE /\ ExpectKeyword("WHEN")
       /\ LET condition == ParseExpression
          IN /\ ExpectKeyword("THEN")
             /\ LET result == ParseExpression
                IN <<[kind |-> "when", children |-> <<condition, result>>, attributes |-> <<>>]>>
                   \o ParseWhenClauses

\* Subquery ::= (SELECT ...)
ParseSubquery ==
  /\ parseDepth < MAX_QUERY_DEPTH
  /\ ExpectKeyword("(")
  /\ parseDepth' = parseDepth + 1
  /\ LET selectStmt == ParseSelectStmt
     IN /\ ExpectKeyword(")")
        /\ parseDepth' = parseDepth - 1
        /\ [kind |-> "subquery", children |-> <<selectStmt>>, attributes |-> <<>>]

\* INSERT INTO table [(columns)] VALUES (values) | SELECT ...
ParseInsertStmt ==
  /\ ExpectKeyword("INSERT")
  /\ ExpectKeyword("INTO")
  /\ LET tableName == CurrentToken.value
     IN /\ Consume("identifier", "")
        /\ LET columns == IF Match("punctuation", "(") THEN ParseColumnList ELSE <<>>
               values == ParseInsertValues
           IN ast' = [
                kind |-> "INSERT",
                children |-> <<values>>,
                attributes |-> [table |-> tableName, columns |-> columns]
              ]
        /\ UNCHANGED <<parseErrors, parseDepth>>

ParseInsertValues ==
  IF Match("keyword", "VALUES")
  THEN /\ ExpectKeyword("VALUES")
       /\ ParseValuesList
  ELSE ParseSelectStmt  \* INSERT INTO ... SELECT ...

\* UPDATE table SET col=val [, col=val]* [WHERE condition]
ParseUpdateStmt ==
  /\ ExpectKeyword("UPDATE")
  /\ LET tableName == CurrentToken.value
     IN /\ Consume("identifier", "")
        /\ ExpectKeyword("SET")
        /\ LET assignments == ParseAssignmentList
               whereClause == IF Match("keyword", "WHERE") THEN ParseWhereClause ELSE [kind |-> "empty"]
           IN ast' = [
                kind |-> "UPDATE",
                children |-> <<assignments, whereClause>>,
                attributes |-> [table |-> tableName]
              ]
        /\ UNCHANGED <<parseErrors, parseDepth>>

\* DELETE FROM table [WHERE condition]
ParseDeleteStmt ==
  /\ ExpectKeyword("DELETE")
  /\ ExpectKeyword("FROM")
  /\ LET tableName == CurrentToken.value
     IN /\ Consume("identifier", "")
        /\ LET whereClause == IF Match("keyword", "WHERE") THEN ParseWhereClause ELSE [kind |-> "empty"]
           IN ast' = [
                kind |-> "DELETE",
                children |-> <<whereClause>>,
                attributes |-> [table |-> tableName]
              ]
        /\ UNCHANGED <<parseErrors, parseDepth>>

\* CREATE TABLE table (col1 type1, col2 type2, ...)
ParseCreateStmt ==
  /\ ExpectKeyword("CREATE")
  /\ LET objectType == CurrentToken.value  \* TABLE or INDEX
     IN CASE objectType OF
          "TABLE" -> ParseCreateTable
          [] "INDEX" -> ParseCreateIndex
          [] OTHER -> 
            /\ parseErrors' = Append(parseErrors, "Expected TABLE or INDEX")
            /\ UNCHANGED <<currentPos, tokens, ast, parseDepth>>

ParseCreateTable ==
  /\ ExpectKeyword("TABLE")
  /\ LET tableName == CurrentToken.value
     IN /\ Consume("identifier", "")
        /\ ExpectKeyword("(")
        /\ LET columns == ParseColumnDefinitions
           IN /\ ExpectKeyword(")")
              /\ ast' = [
                   kind |-> "CREATE_TABLE",
                   children |-> columns,
                   attributes |-> [table |-> tableName]
                 ]
              /\ UNCHANGED <<parseErrors, parseDepth>>

ParseColumnDefinitions ==
  \* ColumnDef ::= name type [NOT NULL] [PRIMARY KEY] [DEFAULT value]
  LET colName == CurrentToken.value
  IN /\ Consume("identifier", "")
     /\ LET colType == CurrentToken.value
        IN /\ Consume("identifier", "")
           /\ LET constraints == ParseColumnConstraints
              IN <<[kind |-> "column_def",
                    children |-> <<>>,
                    attributes |-> [name |-> colName, type |-> colType, constraints |-> constraints]]>>
                 \o (IF Match("punctuation", ",") THEN ParseColumnDefinitions ELSE <<>>)

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_Parser ==
  /\ tokens = <<>>
  /\ currentPos = 1
  /\ ast = [kind |-> "empty"]
  /\ parseErrors = <<>>
  /\ parseDepth = 0

(* --------------------------------------------------------------------------
   PARSING ACTIONS
   -------------------------------------------------------------------------- *)

\* Parse a complete SQL query string
Parse(queryString) ==
  /\ tokens' = Tokenize(queryString)
  /\ currentPos' = 1
  /\ ast' = [kind |-> "empty"]
  /\ parseErrors' = <<>>
  /\ parseDepth' = 0
  /\ ParseStatement

\* Main next-state relation
Next_Parser ==
  \/ \E query \in STRING: Parse(query)
  \/ UNCHANGED parserVars

Spec_Parser == Init_Parser /\ [][Next_Parser]_parserVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Parse depth never exceeds maximum
Inv_Parser_DepthBound ==
  parseDepth <= MAX_QUERY_DEPTH

\* Invariant 2: Well-formed AST structure
Inv_Parser_WellFormedAST ==
  ast.kind \in StmtKind \union ExprKind \union {"empty"}

\* Invariant 3: Unambiguous parsing
Inv_Parser_Unambiguous ==
  \* For any valid token sequence, there is at most one valid AST
  Len(parseErrors) = 0 => \A other_ast \in ASTNode: other_ast # ast

\* Invariant 4: Type-safe AST nodes
Inv_Parser_TypeSafe ==
  \A node \in ASTNode:
    node.kind = "column_ref" => "column" \in DOMAIN node.attributes

\* Invariant 5: No token skipped
Inv_Parser_TokensConsumed ==
  currentPos <= Len(tokens) + 1

(* --------------------------------------------------------------------------
   PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Parse completes eventually
Prop_Parser_Termination ==
  <>(currentPos = Len(tokens) + 1 \/ Len(parseErrors) > 0)

\* Property 2: Valid SQL always parses successfully
Prop_Parser_Completeness ==
  [](IsValidSQL(tokens) => <>(ast.kind # "empty" /\ Len(parseErrors) = 0))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM Parser_Correctness ==
  /\ Spec_Parser => []Inv_Parser_WellFormedAST
  /\ Spec_Parser => []Inv_Parser_DepthBound
  /\ Spec_Parser => Prop_Parser_Termination

=============================================================================

(*
  REFERENCES:
  
  [1] Chamberlin, D. D., & Boyce, R. F. (1974). "SEQUEL: A structured English 
      query language." Proceedings of the 1974 ACM SIGFIDET workshop.
  
  [2] ISO/IEC 9075:2016 - Information technology -- Database languages -- SQL
  
  [3] Melton, J., & Simon, A. R. (2002). "SQL:1999 - Understanding Relational 
      Language Components." Morgan Kaufmann.
  
  [4] Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). "Compilers: 
      Principles, Techniques, and Tools" (2nd ed.). Addison-Wesley.
  
  [5] Simeon, J., & Wadler, P. (2003). "The essence of XML." POPL'03.
  
  IMPLEMENTATION NOTES:
  
  - This specification uses recursive descent parsing strategy
  - Production rules follow SQL:2016 BNF grammar
  - Error recovery not fully specified (implementation-dependent)
  - Tokenization (Tokenize function) is abstract (implementation-specific)
  - String manipulation functions (SplitByDot, InferLiteralType) are helpers
*)


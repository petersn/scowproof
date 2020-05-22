
module ScowproofParse where

import System.IO
import Control.Monad
import Data.List
import Data.Functor
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import ScowproofTerms (VariableName)

type OptionalExprAnnot = Maybe Expr

data TypedName = TypedName VariableName OptionalExprAnnot deriving (Show, Eq, Ord)
data MatchArmExpr = MatchArmExpr Expr Expr deriving (Show, Eq, Ord)

data Literal =
    LitNat Integer
    deriving (Show, Eq, Ord)

data Expr =
      ExprVar VariableName
    | ExprApp Expr Expr
    | ExprAbs [TypedName] Expr
    | ExprLet TypedName Expr Expr
    | ExprPi [TypedName] Expr
    | ExprArrow Expr Expr
    | ExprFix VariableName [TypedName] OptionalExprAnnot Expr
    -- The three Maybes are: as, in, return
    | ExprMatch Expr (Maybe VariableName) (Maybe Expr) (Maybe Expr) [MatchArmExpr]
    | ExprAnnot Expr Expr
    | ExprLit Literal
    deriving (Show, Eq, Ord)

data InductiveConstructorExpr = InductiveConstructorExpr VariableName [TypedName] Expr deriving (Show, Eq, Ord)

data Command =
      CmdInfer Expr
    | CmdCheck Expr Expr
    | CmdEval Expr
    | CmdAlphaCanon Expr
    deriving (Show, Eq, Ord)

data Vernac =
      VernacDefinition VariableName [TypedName] OptionalExprAnnot Expr
    | VernacAxiom VariableName Expr
    | VernacInductive VariableName [TypedName] OptionalExprAnnot [InductiveConstructorExpr]
    | VernacCommand Command
    deriving (Show, Eq, Ord)

languageDef = emptyDef {
	Token.commentStart    = "/*",
	Token.commentEnd      = "*/",
	Token.commentLine     = "//",
	Token.identStart      = letter,
	Token.identLetter     = alphaNum <|> oneOf "_'",
	Token.reservedNames   = [
		"let", "fixpoint", "axiom", "inductive", "infer", "check", "eval", "alphacanon",
        "forall", "fun", "fix", "match", "as", "in", "return"
	],
	Token.reservedOpNames = []
}

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
symbol     = Token.symbol     lexer

parens     = Token.parens     lexer -- parses surrounding parentheses
natural    = Token.natural    lexer -- parses a natural number
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

parseExprAtom :: Parser Expr
parseExprAtom =
    -- This try is necessary here e.g. "(a : b)" fails to parse as an expr, but is an annotation.
    try (parens parseExpr)
    <|> parseVar
    <|> parseFun
    <|> parseFix
    <|> parseLet
    <|> parsePi
    <|> parseMatch
    <|> parseAnnot
    <|> parseNat
    where
        parseVar = ExprVar <$> intercalate "::" <$> sepBy1 identifier (try $ symbol "::")
        parseFun = do
            reserved "fun"
            binders <- parseAtLeastOneBinder
            symbol "=>"
            expr <- parseExpr
            return $ ExprAbs binders expr
        parseFix = do
            reserved "fix"
            name <- identifier
            binders <- parseAtLeastOneBinder
            annot <- parseOptionalTypeAnnotation
            symbol "{"
            body <- parseExpr
            symbol "}"
            return $ ExprFix name binders annot body
        parseLet = do
            reserved "let"
            name <- identifier
            symbol "="
            bindingValue <- parseExpr
            reserved "in"
            result <- parseExpr
            return $ ExprLet (TypedName name Nothing) bindingValue result
        parsePi = do
            reserved "forall"
            binders <- parseAtLeastOneBinder 
            symbol ","
            expr <- parseExpr
            return $ ExprPi binders expr
        parseMatch = do
            reserved "match"
            scrutinee <- parseExpr
            asClause <- optionMaybe (reserved "as" >> identifier)
            inClause <- optionMaybe (reserved "in" >> parseExpr)
            returnClause <- optionMaybe (reserved "return" >> parseExpr)
            symbol "{"
            arms <- sepEndBy parseMatchArm semi
            symbol "}"
            return $ ExprMatch scrutinee asClause inClause returnClause arms
        parseAnnot = parens (do
                expr1 <- parseExpr
                symbol ":"
                expr2 <- parseExpr
                return $ ExprAnnot expr1 expr2
            )
        parseNat = ExprLit <$> LitNat <$> natural

operators = [
		[Infix (return ExprApp) AssocLeft],
		[Infix (reservedOp "->" >> return ExprArrow) AssocRight]
	]

parseExpr :: Parser Expr
parseExpr = buildExpressionParser operators parseExprAtom

-- The binder parsing rules are a bit complicated.
-- The following examples are all allowed:
--   ""  "a"  "a b"  "(a : nat) b"  "a (b c : nat) (d)"
-- Right now I do not support:
--   "a : nat"  "a b : nat" 
-- However, I'd like to (as Coq does), but I think it might require more backtracking elsewhere.
-- e.g. I'd like to support "fun x : nat => x".
parseBinders :: Parser [TypedName]
parseBinders = join <$> many (parens binderGroup <|> unannotatedVar)
    where
        binderGroup = do
            identifiers <- many1 identifier
            symbol ":"
            expr <- parseExpr
            return [TypedName name (Just expr) | name <- identifiers]
        unannotatedVar = do
            name <- identifier
            return [TypedName name Nothing]

parseAtLeastOneBinder :: Parser [TypedName]
parseAtLeastOneBinder = do
    binders <- parseBinders
    if null binders then fail "no binders" else return binders

parseOptionalTypeAnnotation :: Parser OptionalExprAnnot
parseOptionalTypeAnnotation =
    -- This try is necessary here e.g. "let a := b;" could start to parse "a :" as an annotation.
    try (symbol ":" >> Just <$> parseExpr)
    <|> return Nothing

parseInductiveConstructor :: Parser InductiveConstructorExpr
parseInductiveConstructor = do
    name <- identifier
    binders <- parseBinders
    symbol ":"
    expr <- parseExpr
    return $ InductiveConstructorExpr name binders expr

parseMatchArm :: Parser MatchArmExpr
parseMatchArm = do
    pat <- parseExpr
    symbol "=>" -- Do I need to think hard here about partial consumption?
    result <- parseExpr
    return $ MatchArmExpr pat result

parseVernac :: Parser Vernac
parseVernac =
    parseDefinition
    <|> parseFixpoint
    <|> parseAxiom
    <|> parseInductive
    <|> parseInfer
    <|> parseCheck
    <|> parseEval
    <|> parseAlphaCanon
    where
        parseDefinition = do
            reserved "let"
            name <- identifier
            binders <- parseBinders
            annot <- parseOptionalTypeAnnotation
            symbol "="
            expr <- parseExpr
            semi
            return $ VernacDefinition name binders annot expr
        -- Fixpoints actually desugar into definitions immediately.
        parseFixpoint = do
            reserved "fixpoint"
            name <- identifier
            binders <- parseAtLeastOneBinder
            annot <- parseOptionalTypeAnnotation
            symbol "{"
            body <- parseExpr
            symbol "}"
            return $ VernacDefinition name [] Nothing (ExprFix name binders annot body)
        parseAxiom = do
            reserved "axiom"
            name <- identifier
            symbol ":"
            expr <- parseExpr
            semi
            return $ VernacAxiom name expr
        parseInductive = do
            reserved "inductive"
            name <- identifier
            binders <- parseBinders
            annot <- parseOptionalTypeAnnotation
            symbol "{"
            constructors <- sepEndBy parseInductiveConstructor semi
            symbol "}"
            return $ VernacInductive name binders annot constructors
        parseInfer = do
            reserved "infer"
            expr <- parseExpr
            semi
            return $ VernacCommand (CmdInfer expr)
        parseCheck = do
            reserved "check"
            expr1 <- parseExpr
            symbol ":"
            expr2 <- parseExpr
            semi
            return $ VernacCommand (CmdCheck expr1 expr2)
        parseEval = do
            reserved "eval"
            expr <- parseExpr
            semi
            return $ VernacCommand (CmdEval expr)
        parseAlphaCanon = do
            reserved "alphacanon"
            expr <- parseExpr
            semi
            return $ VernacCommand (CmdAlphaCanon expr)

parseProgramBlock :: Parser [Vernac]
parseProgramBlock = do
    vernacs <- many parseVernac
    eof
    return vernacs

parseFile :: String -> IO [Vernac]
parseFile file = do
	program  <- readFile file
	case parse (whiteSpace >> parseProgramBlock) "" program of
		Left e  -> print e >> fail "parse error"
		Right r -> return r

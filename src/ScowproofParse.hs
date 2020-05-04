
module ScowproofParse where

import System.IO
import Control.Monad
import Data.List
import Data.Functor
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

type VariableName = String
type OptionalAnnot = Maybe Expr

data Binder = Binder VariableName OptionalAnnot deriving Show

data MatchArm = MatchArm Expr Expr deriving Show

data Literal =
    LitNat Integer
    deriving Show

data Expr =
    ExprVar String
    | ExprApp Expr Expr
    | ExprAbs [Binder] Expr
    | ExprLet Binder Expr Expr
    | ExprPi [Binder] Expr
    | ExprArrow Expr Expr
    | ExprFix String [Binder] OptionalAnnot Expr
    | ExprMatch Expr (Maybe Expr) (Maybe Expr) (Maybe Expr) [MatchArm]
    | ExprAnnot Expr Expr
    | ExprLit Literal
    deriving Show

data InductiveConstructor = InductiveConstructor VariableName [Binder] Expr deriving Show

data Vernac =
    VernacDefinition VariableName [Binder] OptionalAnnot Expr
    | VernacAxiom VariableName Expr
    | VernacInductive VariableName [Binder] OptionalAnnot [InductiveConstructor]
    | VernacInfer Expr
    | VernacCheck Expr Expr
    | VernacEval Expr
    deriving Show

languageDef = emptyDef {
	Token.commentStart    = "/*",
	Token.commentEnd      = "*/",
	Token.commentLine     = "//",
	Token.identStart      = letter,
	Token.identLetter     = alphaNum,
	Token.reservedNames   = [
		"let", "fixpoint", "axiom", "inductive", "infer", "check", "eval",
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

parseOptionalTypeAnnotation :: Parser OptionalAnnot
parseOptionalTypeAnnotation =
    -- This try is necessary here e.g. "let a := b;" could start to parse "a :" as an annotation.
    try (symbol ":" >> Just <$> parseExpr)
    <|> return Nothing

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
            return $ ExprLet (Binder name Nothing) bindingValue result
        parsePi = do
            reserved "forall"
            binders <- parseAtLeastOneBinder 
            symbol ","
            expr <- parseExpr
            return $ ExprPi binders expr
        parseMatch = do
            reserved "match"
            scrutinee <- parseExpr
            asClause <- optionMaybe (reserved "as" >> parseExpr)
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

-- Because a single binder like (x y : nat) can produce multiple Binders,
-- this function has a slightly surprising type.
parseSingleBinderIntoBinderList :: Parser [Binder]
parseSingleBinderIntoBinderList = parens binderGroup <|> unannotatedVar
    where
        binderGroup = do
            identifiers <- many1 identifier
            symbol ":"
            expr <- parseExpr
            return [Binder name (Just expr) | name <- identifiers]
        unannotatedVar = do
            name <- identifier
            return [Binder name Nothing]

-- The binder parsing rules are a bit complicated.
-- The following examples are all allowed:
--   ""  "a"  "a b"  "(a : nat) b"  "a (b c : nat) (d)"
-- Right now I do not support:
--   "a : nat"  "a b : nat" 
-- However, I'd like to (as Coq does), but I think it might require more backtracking elsewhere.
-- e.g. I'd like to support "fun x : nat => x".
parseBinders :: Parser [Binder]
parseBinders = join <$> many parseSingleBinderIntoBinderList

parseAtLeastOneBinder :: Parser [Binder]
parseAtLeastOneBinder = do
    binders <- parseBinders
    if null binders then fail "no binders" else return binders

pipeSeparated :: Parser a -> Parser [a]
pipeSeparated p = optional (symbol "|") >> sepBy p (symbol "|")

parseInductiveConstructor :: Parser InductiveConstructor
parseInductiveConstructor = do
    name <- identifier
    binders <- parseBinders
    symbol ":"
    expr <- parseExpr
    return $ InductiveConstructor name binders expr

parseMatchArm :: Parser MatchArm
parseMatchArm = do
    pat <- parseExpr
    symbol "=>" -- Do I need to think hard here about partial consumption?
    result <- parseExpr
    return $ MatchArm pat result

parseVernac :: Parser Vernac
parseVernac =
    parseDefinition
    <|> parseFixpoint
    <|> parseAxiom
    <|> parseInductive
    <|> parseInfer
    <|> parseCheck
    <|> parseEval
    where
        parseDefinition = do
            reserved "let"
            name <- identifier
            binders <- parseBinders
            annot <- parseOptionalTypeAnnotation
            symbol ":="
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
            return $ VernacInfer expr
        parseCheck = do
            reserved "check"
            expr1 <- parseExpr
            symbol ":"
            expr2 <- parseExpr
            semi
            return $ VernacCheck expr1 expr2
        parseEval = do
            reserved "eval"
            expr <- parseExpr
            semi
            return $ VernacEval expr


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

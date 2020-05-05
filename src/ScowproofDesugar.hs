
module ScowproofDesugar where

import Text.Read
import Data.List
import Data.Maybe
import qualified Data.Map as Map

import ScowproofParse
import ScowproofKernel

desugarTypedName :: TypedName -> Binder
desugarTypedName (TypedName name optionalExprAnnot) = Binder name $ desugarExpr <$> optionalExprAnnot

desugarMatchArm :: MatchArmExpr -> MatchArm
desugarMatchArm (MatchArmExpr pat result) = MatchArm (innerName pat) (foldBinders pat) (desugarExpr result)
    where
        innerName (ExprVar name) = name
        innerName (ExprApp inner _) = innerName inner
        -- Quadratic time, but who cares.
        foldBinders (ExprVar name) = []
        foldBinders (ExprApp inner (ExprVar name)) =
            foldBinders inner ++ [Binder name Nothing]
        foldBinders (ExprApp inner (ExprAnnot (ExprVar name) ty)) =
            foldBinders inner ++ [Binder name (Just $ desugarExpr ty)]

-- In Coq an in clause is required to be an inductive constructor, followed by enough _s to saturate
-- the parameters, followed by enough identifiers to saturate the arity. These identifiers are then
-- bound in the scope of *just* the return clause. In scowproof we skip the _s part of the protocol,
-- because that part can just be statically known given the name of the constructor.
-- Therefore, the *only* sort of expression we accept here is a sequence of nested applications, like:
--   (ExprApp
--     (ExprApp
--       (ExprVar "inductive::constructor")
--       (ExprVar "y1")
--     )
--     (ExprVar "y2")
--   )
desugarInClause :: Maybe Expr -> InClause
desugarInClause Nothing = InAbsent
desugarInClause (Just expr) = InPresent (constructorName expr) (arityNames expr)
    where
        constructorName (ExprApp fn arg) = constructorName fn
        constructorName (ExprVar name) = name
        constructorName _ = fail "in-clause failed have the right form"
        -- Quadratic time, but who cares.
        arityNames (ExprVar name) = []
        arityNames (ExprApp inner (ExprVar name)) =
            arityNames inner ++ [name]
        arityNames _ = fail "in-clause failed have the right form"

foldrHelper :: (Binder -> Term -> Term) -> TypedName -> Term -> Term
foldrHelper constructor typedName term = constructor (desugarTypedName typedName) term

desugarExpr :: Expr -> Term

desugarExpr (ExprVar "Set") = TermSortType 0
desugarExpr (ExprVar "Prop") = TermSortProp
desugarExpr (ExprVar name)
    | Just t <- stripPrefix "Type" name, Just n <- readMaybe t = TermSortType n
    | otherwise = TermVar name

desugarExpr (ExprApp fn arg)             = TermApp (desugarExpr fn) (desugarExpr arg)
desugarExpr (ExprAbs arguments body)     = foldr (foldrHelper TermAbs) (desugarExpr body) arguments
--desugarExpr (ExprLet typedName val body) = TermLet (desugarTypedName typedName) (desugarExpr val) (desugarExpr body)
desugarExpr (ExprLet typedName val body) =
    (TermApp
        (TermAbs (desugarTypedName typedName) (desugarExpr body))
        (desugarExpr val)
    )
desugarExpr (ExprPi arguments expr)      = foldr (foldrHelper TermPi) (desugarExpr expr) arguments
desugarExpr (ExprArrow from to)          = TermPi (Binder "_" (Just $ desugarExpr from)) (desugarExpr to)
desugarExpr (ExprFix fixName arguments optionalExprAnnot body) =
    TermFix fixName (desugarTypedName $ head arguments) (desugarExpr <$> optionalExprAnnot) unfoldedBody
    where unfoldedBody = foldr (foldrHelper TermAbs) (desugarExpr body) $ drop 1 arguments

-- Here we desugar:
--   match m as x in I y1 y2 y3 return P { ... m ... }
-- Into:
--   let x = m in
--     match x in I y1 y2 y3 return P { ... m ... }
-- (Note that this let currently is, in turn, desugared into a function application.)
desugarExpr (ExprMatch scrutinee Nothing inClause returnClause matchArms) =
    TermMatch
        (desugarExpr scrutinee)
        (desugarInClause inClause) (desugarExpr <$> returnClause)
        (desugarMatchArm <$> matchArms)
desugarExpr (ExprMatch scrutinee (Just asName) inClause returnClause matchArms) =
    desugarExpr (ExprLet
        (TypedName asName Nothing)
        scrutinee
        (ExprMatch (ExprVar asName) Nothing inClause returnClause matchArms)
    )

desugarExpr (ExprAnnot expr ty) = TermAnnot (desugarExpr expr) (desugarExpr ty)
desugarExpr (ExprLit (LitNat n)) = iterate wrapWithSucc (TermVar "nat::O") !! fromIntegral n
    where wrapWithSucc t = (TermApp (TermVar "nat::S") t)

data GlobalScope = GlobalScope {
    globalTerms :: Map.Map ScowproofKernel.VariableName Term,
    globalInductives :: Map.Map ScowproofKernel.VariableName Inductive,
    globalCommands :: [Command]
} deriving (Show, Eq, Ord)

definitionToTerm :: Vernac -> Maybe Term
definitionToTerm (VernacDefinition name arguments optionalExprAnnot body) =
    Just $ foldr (foldrHelper TermAbs) (desugarExpr body) arguments
definitionToTerm _ = Nothing

makeGlobalScope :: [Vernac] -> GlobalScope
makeGlobalScope vernacs = GlobalScope {
    globalTerms = Map.fromList [
        (name, t) |
        def@(VernacDefinition name _ _ _) <- vernacs,
        let Just t = definitionToTerm def
    ],
    globalInductives = Map.fromList [],
    globalCommands = [cmd | VernacCommand cmd <- vernacs]
}

newLine :: Int -> String
newLine d = "\n" ++ replicate (2 * d) ' '

prettyBinder :: Int -> Binder -> String
prettyBinder d (Binder name Nothing) = name
prettyBinder d (Binder name (Just ty)) = "(" ++ name ++ " : " ++ prettyTerm d ty ++ ")"

prettyTerm :: Int -> Term -> String
prettyTerm d (TermVar "nat") = "ℕ"
prettyTerm d (TermVar name) = name
prettyTerm d (TermApp e1 e2) = "(" ++ prettyTerm d e1 ++ " " ++ prettyTerm d e2 ++ ")"
prettyTerm d (TermAbs binder body) = "fun " ++ prettyBinder d binder ++ " => " ++ newLine (d + 1) ++ prettyTerm (d + 1) body
--prettyTerm d (TermLet binder e1 e2) = "let " ++ prettyBinder d binder ++ " = " ++ prettyTerm d e1 ++ " in " ++ prettyTerm d e2

prettyTerm d (TermPi (Binder "_" (Just ty)) e) = prettyTerm d ty ++ " -> " ++ prettyTerm d e
prettyTerm d (TermPi binder e) = "∀ " ++ prettyBinder d binder ++ ", " ++ prettyTerm d e

prettyTerm d (TermFix hypothesis binder Nothing body) =
    "fix " ++ prettyBinder d binder ++ " { " ++ newLine (d + 1) ++ prettyTerm (d + 1) body ++ " }"
prettyTerm d (TermFix hypothesis binder (Just ty) body) =
    "fix " ++ prettyBinder d binder ++ " : " ++ prettyTerm d ty ++ " {" ++ newLine (d + 1) ++ prettyTerm (d + 1) body ++ newLine d ++ "}"

prettyTerm d (TermMatch scrutinee inClause returnClause matchArms) =
    "match " ++ prettyTerm d scrutinee ++ inText ++ returnText ++ " {" ++ newLine (d + 1) ++ prettiedArms ++ newLine d ++ "}"
    where
        prettiedArms = intercalate (";" ++ newLine (d + 1)) $ prettyArm <$> matchArms
        prettyArm (MatchArm constructorName arguments result) =
            constructorName ++ (prettyBinder (d + 1) <$> arguments >>= (" " ++)) ++ " => " ++ prettyTerm d result
        inText
            | InPresent constructorName arityNames <- inClause =
                " in " ++ intercalate " " (constructorName : arityNames)
            | otherwise = ""
        returnText
            | Just e <- returnClause = " return " ++ prettyTerm d e
            | otherwise = ""

prettyTerm d (TermAnnot e ty) = "(" ++ prettyTerm d e ++ " : " ++ prettyTerm d ty ++ ")"
prettyTerm d (TermSortType n) = "𝕋" ++ show n
prettyTerm d TermSortProp = "ℙ"

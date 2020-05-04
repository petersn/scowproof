
module ScowproofDesugar where

import Text.Read
import Data.List
import qualified Data.Map as Map

import ScowproofParse
import ScowproofKernel

desugarTypedName :: TypedName -> Binder
desugarTypedName (TypedName name optionalExprAnnot) = Binder name $ desugarExpr <$> optionalExprAnnot

foldrHelper :: (Binder -> Term -> Term) -> TypedName -> Term -> Term
foldrHelper constructor typedName term = constructor (desugarTypedName typedName) term

desugarExpr :: Expr -> Term

desugarExpr (ExprVar "Set") = TermSortType 0
desugarExpr (ExprVar "Prop") = TermSortProp
desugarExpr (ExprVar name)
    | isPrefixOf "Type" name = case readMaybe (drop 4 name) of
        Just n -> TermSortType n
        Nothing -> TermVar name
    | otherwise = TermVar name

desugarExpr (ExprApp fn arg)             = TermApp (desugarExpr fn) (desugarExpr arg)
desugarExpr (ExprAbs arguments body)     = foldr (foldrHelper TermAbs) (desugarExpr body) arguments
desugarExpr (ExprLet typedName val body) = TermLet (desugarTypedName typedName) (desugarExpr val) (desugarExpr body)
desugarExpr (ExprPi arguments expr)      = foldr (foldrHelper TermPi) (desugarExpr expr) arguments
desugarExpr (ExprArrow from to)          = TermPi (Binder "_" (Just $ desugarExpr from)) (desugarExpr to)

desugarExpr (ExprFix fixName arguments optionalExprAnnot body) =
    TermFix fixName (desugarTypedName $ head arguments) (desugarExpr <$> optionalExprAnnot) unfoldedBody
    where
        unfoldedBody = foldr (foldrHelper TermAbs) (desugarExpr body) $ drop 1 arguments
desugarExpr (ExprMatch scrutinee asClause inClause returnClause matchArms) =
    TermMatch
        (desugarExpr scrutinee)
        (desugarExpr <$> asClause) (desugarExpr <$> inClause) (desugarExpr <$> returnClause)
        (desugarMatchArm <$> matchArms)
    where
        desugarMatchArm = undefined -- TODO

desugarExpr (ExprAnnot expr ty) = TermAnnot (desugarExpr expr) (desugarExpr ty)
desugarExpr (ExprLit (LitNat n)) = iterate wrap (TermVar "nat::O") !! fromIntegral n
    where
        wrap t = (TermApp (TermVar "nat::S") t)

data GlobalScope = GlobalScope {
    globalTerms :: Map.Map ScowproofKernel.VariableName Term,
    globalInductives :: Map.Map ScowproofKernel.VariableName Inductive,
    globalVernacs :: [Vernac]
} deriving (Show, Eq, Ord)

makeGlobalScope :: [Vernac] -> GlobalScope
makeGlobalScope vernacs = GlobalScope {}

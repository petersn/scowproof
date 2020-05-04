
module ScowproofKernel where

import Data.Maybe
import qualified Data.Map as Map

type VariableName = String
type OptionalTypeAnnot = Maybe Term
type UniverseIndex = Integer
type ValCtx = Map.Map VariableName Term
type TypeCtx = Map.Map VariableName Term

data Binder = Binder VariableName OptionalTypeAnnot deriving (Show, Eq, Ord)
data MatchArm = MatchArm VariableName [Binder] Term deriving (Show, Eq, Ord)

data Term =
    TermVar VariableName
    | TermApp Term Term
    | TermAbs Binder Term
    | TermLet Binder Term Term
    | TermPi Binder Term
    | TermFix VariableName Binder OptionalTypeAnnot Term
    -- The three Maybes are: as, in, return
    | TermMatch Term (Maybe Term) (Maybe Term) (Maybe Term) [MatchArm]
    | TermAnnot Term Term
    | TermSortType UniverseIndex
    | TermSortProp
    deriving (Show, Eq, Ord)

data Inductive = Inductive deriving (Show, Eq, Ord)

data NormalizationStrategy = CBV | WHNF deriving (Show, Eq, Ord)

normalize :: NormalizationStrategy -> ValCtx -> Term -> Term
normalize _ vc (TermVar name) = fromJust $ Map.lookup name vc

infer :: ValCtx -> TypeCtx -> Term -> Term
infer _ tc (TermVar name) = fromJust $ Map.lookup name tc

check :: ValCtx -> TypeCtx -> Term -> Term -> Bool
check ctx _ = undefined

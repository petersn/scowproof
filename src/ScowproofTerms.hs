
module ScowproofTerms where

import qualified Data.Map as Map

type VariableName = String
type OptionalTypeAnnot = Maybe Term
type UniverseIndex = Integer
type ValCtx = Map.Map VariableName Term
type TypeCtx = Map.Map VariableName Term

data Binder = Binder VariableName OptionalTypeAnnot deriving (Show, Eq, Ord)
data MatchArm = MatchArm VariableName [Binder] Term deriving (Show, Eq, Ord)

data InClause =
      InPresent VariableName [VariableName]
    | InAbsent
    deriving (Show, Eq, Ord)

data Term =
      TermVar VariableName
    | TermApp Term Term
    | TermAbs Binder Term
--    | TermLet Binder Term Term
    | TermPi Binder Term
    | TermFix VariableName Binder OptionalTypeAnnot Term
    -- The (Maybe Term) is the return clause.
    | TermMatch Term InClause (Maybe Term) [MatchArm]
    | TermAnnot Term Term
    | TermSortType UniverseIndex
    | TermSortProp
    deriving (Show, Eq, Ord)

data Inductive = Inductive deriving (Show, Eq, Ord)

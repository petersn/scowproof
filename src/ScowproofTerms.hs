
module ScowproofTerms where

import qualified Data.Map as Map

type VariableName = String
type OptionalTypeAnnot = Maybe Term
type UniverseIndex = Integer
type ValCtx = Map.Map VariableName Term
type TypeCtx = Map.Map VariableName Term

data Binder = Binder VariableName OptionalTypeAnnot deriving (Show, Eq, Ord)
data MatchArm = MatchArm VariableName [VariableName] Term deriving (Show, Eq, Ord)

data InClause =
      InPresent VariableName [VariableName]
    | InAbsent
    deriving (Show, Eq, Ord)

data Term =
      TermVar VariableName
    | TermApp Term Term
    | TermAbs Binder Term
    | TermPi Binder Term
    | TermFix VariableName Binder OptionalTypeAnnot Term
    | TermMatch Term InClause (Maybe Term) [MatchArm]
    | TermAnnot Term Term
    | TermSortType UniverseIndex
    | TermSortProp
    deriving (Show, Eq, Ord)

data InductiveConstructor = InductiveConstructor VariableName Term deriving (Show, Eq, Ord)
data Inductive = Inductive {
    inductiveName :: VariableName,
    inductiveParameters :: [Binder],
    inductiveArity :: OptionalTypeAnnot,
    inductiveConstructors :: [InductiveConstructor]
    --Inductive VariableName [Binder] OptionalTypeAnnot [InductiveConstructor]
} deriving (Show, Eq, Ord)

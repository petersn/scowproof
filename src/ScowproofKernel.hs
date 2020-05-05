
module ScowproofKernel where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.State as State

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

annotUpdate :: OptionalTypeAnnot -> Set.Set VariableName -> Set.Set VariableName
annotUpdate Nothing set = set
annotUpdate (Just ty) set = set `Set.union` freeVars ty

-- Because the constructorName is guaranteed (during inference/normalization) to
-- always be a reference to a global inductive constructor, we omit it.
matchArmFreeVars :: MatchArm -> Set.Set VariableName
matchArmFreeVars (MatchArm constructorName binders result) =
    freeVars result `Set.difference` Set.fromList [name | Binder name _ <- binders]

freeVars :: Term -> Set.Set VariableName
freeVars (TermVar name) = Set.singleton name
freeVars (TermApp e1 e2) = freeVars e1 `Set.union` freeVars e2
-- Note that in (fun (x : x) => x) we actually *do* have x free in the type.
-- Thus, in the following case we union in (freeVars ty) outside of the deletion.
freeVars (TermAbs (Binder argName typeAnnot) e) = annotUpdate typeAnnot (Set.delete argName $ freeVars e)
freeVars (TermPi  (Binder argName typeAnnot) e) = annotUpdate typeAnnot (Set.delete argName $ freeVars e)
-- The general form of a fix:
--   fix hypName (argName : argAnnot) : returnAnnot { body }
--          A        B          ɑ            β         ɣ
-- There are two sources of binding (A, B) and three sources of free variables (ɑ, β, ɣ)
-- Table of what's allowed to bind to what:
--   ɑ can't reference A or B
--   β can reference B, but not A
--   ɣ can reference A and B
-- This motivates the following order for inserting/deleting free variables, which is the only correct one.
freeVars (TermFix hypName (Binder argName argAnnot) returnAnnot body) =
    annotUpdate argAnnot $
    Set.delete argName $
    annotUpdate returnAnnot $
    Set.delete hypName $
    freeVars body
-- The general form of a match:
--   match scrutinee in inClause return returnClause {
--     constructor x y z => result;
--     ...
--   }
-- The variables bound in the inClause are only visible in the returnClause.
-- Additionally, we don't include the constructors, because they're all guaranteed globally bound.
-- Other than those two caveats, the computation is straight forward.
freeVars (TermMatch scrutinee inClause returnClause matchArms) =
    foldr Set.union (
        freeVars scrutinee `Set.union`
        (returnClauseVars `Set.difference` inClauseVars)
    ) (matchArmFreeVars <$> matchArms)
    where
        returnClauseVars
            | Just returnExpr <- returnClause = freeVars returnExpr
            | otherwise = Set.empty
        inClauseVars
            | InPresent _ names <- inClause = Set.fromList names
            | otherwise = Set.empty
freeVars (TermAnnot e ty) = freeVars e `Set.union` freeVars ty
freeVars (TermSortType _) = Set.empty
freeVars TermSortProp = Set.empty

type FreshState = State.State Int

subst :: VariableName -> Term -> Term -> FreshState Term
subst s e t@(TermVar n)
    | s == n = return e
    | otherwise = return t
subst s e (TermApp e1 e2) = do
    e1 <- subst s e e1
    e2 <- subst s e e2
    return $ TermApp e1 e2
subst s e (TermApp e1 e2) = do
    e1 <- subst s e e1
    e2 <- subst s e e2
    return $ TermApp e1 e2

--subst x y (TermAbs (Binder n Nothing) e)
--    | n ==



{-

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

-}

fresh :: FreshState String
fresh = do
    i <- State.get
    State.put (i + 1)
    return $ "#" ++ show i

data NormalizationStrategy = CBV | WHNF deriving (Show, Eq, Ord)

normalize :: NormalizationStrategy -> ValCtx -> Term -> FreshState Term
normalize _ vc (TermVar name) = return $ fromJust $ Map.lookup name vc

normalize ns vc (TermAnnot e ty) = do
    e <- n e
    ty <- n ty
    return $ (TermAnnot e ty)
        where n = normalize ns vc

--normalize CBV vc (TermApp fn arg) = normalize CBV fn
--normalize WHNF vc (TermApp fn arg) =

-- Passed through.
normalize _ _ t@(TermSortType _) = return $ t
normalize _ _ t@TermSortProp = return $ t
-- For some reason we don't normalize inside of products.
-- I'm copying this behavior from Bauer's Spartan type theory.
normalize _ _ t@(TermPi _ _) = return $ t

infer :: ValCtx -> TypeCtx -> Term -> Term
infer _ tc (TermVar name) = fromJust $ Map.lookup name tc

check :: ValCtx -> TypeCtx -> Term -> Term -> Bool
check ctx _ = undefined

{-# language ImplicitParams #-}

module ScowproofKernel where

import Data.Maybe
import Control.Monad.Except
import qualified Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.State as State
import qualified System.IO.Unsafe
import Debug.Trace

import ScowproofTerms
import ScowproofDesugar

type ExceptStr = Except String

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
freeVars (TermApp fn arg) = freeVars fn `Set.union` freeVars arg
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
        returnClauseVars = case returnClause of
            Just returnExpr -> freeVars returnExpr
            Nothing -> Set.empty
        inClauseVars = case inClause of
            InPresent _ names -> Set.fromList names
            InAbsent -> Set.empty
freeVars (TermAnnot e ty) = freeVars e `Set.union` freeVars ty
freeVars (TermSortType _) = Set.empty
freeVars TermSortProp = Set.empty

alphaAssign :: (?renamings :: Map.Map VariableName VariableName) => VariableName -> VariableName
alphaAssign oldName = Map.findWithDefault oldName oldName ?renamings

indexToName :: Int -> String
indexToName nextIndex = "@" ++ show nextIndex

alphaCanonBinder :: (?nextIndex :: Int, ?renamings :: Map.Map VariableName VariableName) => Binder -> Binder
alphaCanonBinder (Binder name optionalTy) = Binder (indexToName ?nextIndex) (alphaCanonicalizeInner <$> optionalTy)

alphaCanonUnderBinder :: (?nextIndex :: Int, ?renamings :: Map.Map VariableName VariableName) => Binder -> Term -> Term
alphaCanonUnderBinder (Binder name optionalTy) t =
    let ?nextIndex = ?nextIndex + 1
        ?renamings = (Map.insert name (indexToName ?nextIndex) ?renamings) in alphaCanonicalizeInner t

alphaCanonUnderNameList :: (?nextIndex :: Int, ?renamings :: Map.Map VariableName VariableName) => [VariableName] -> Term -> ([VariableName], Term)
alphaCanonUnderNameList names t = (names', t')
    where
        lastIndex = ?nextIndex + length names
        names' = indexToName <$> [?nextIndex .. lastIndex - 1]
        t' = let
                ?nextIndex = lastIndex
                ?renamings = Data.List.foldl' (\m (name, name') -> Map.insert name name' m) ?renamings (zip names names')
            in alphaCanonicalizeInner t

alphaCanonicalizeInner :: (?nextIndex :: Int, ?renamings :: Map.Map VariableName VariableName) => Term -> Term
alphaCanonicalizeInner (TermVar name) = TermVar (alphaAssign name)
alphaCanonicalizeInner (TermApp fn arg) = TermApp (alphaCanonicalizeInner fn) (alphaCanonicalizeInner arg)
alphaCanonicalizeInner (TermAbs binder body) = TermAbs (alphaCanonBinder binder) (alphaCanonUnderBinder binder body)
alphaCanonicalizeInner (TermPi binder body)  = TermPi  (alphaCanonBinder binder) (alphaCanonUnderBinder binder body)
alphaCanonicalizeInner (TermFix hypName binder@(Binder argName argAnnot) returnAnnot body) = TermFix hypName' binder' returnAnnot' body'
    where
        hypName' = indexToName ?nextIndex -- alphaAssign hypName
        -- Canonicalize the binder's type ascription under no binders.
        binder' = Binder (indexToName (?nextIndex + 1)) (alphaCanonicalizeInner <$> argAnnot)
        -- Canonicalize the return annotation under just the binder.
        returnAnnot' = (let ?nextIndex = ?nextIndex + 1 in alphaCanonUnderBinder binder <$> returnAnnot)
        --returnAnnot' = alphaCanonUnderBinder binder <$> returnAnnot
        -- We don't have to worry about the insertion order here, because well-formedness checking guarantees that the names are distinct.
        argName' = case binder' of Binder x _ -> x
        innerRenamings = Map.insert hypName hypName' $ Map.insert argName argName' ?renamings
        -- Canonicalize the body under both hypName and the binder.
        body' =
            let ?nextIndex = ?nextIndex + 2
                ?renamings = innerRenamings in alphaCanonicalizeInner body
alphaCanonicalizeInner (TermMatch scrutinee inClause returnClause matchArms) = TermMatch scrutinee' inClause' returnClause' matchArms'
    where
        scrutinee' = alphaCanonicalizeInner scrutinee
        (inClause', returnClauseRenamings) = case inClause of
            InPresent constructorName vars -> let
                    vars' = indexToName <$> [?nextIndex .. ?nextIndex + length vars]
                in
                    (
                        InPresent constructorName $ vars',
                        Map.fromList (zip vars vars') `Map.union` ?renamings
                    )
            InAbsent -> (InAbsent, ?renamings)
        returnClause' = let ?renamings = returnClauseRenamings in alphaCanonicalizeInner <$> returnClause
        -- We have to sort by constructor name here to avoid being sensitive to that.
        matchArms' = Data.List.sortOn (\(MatchArm constructorName _ _) -> constructorName) [
                let (names, body') = alphaCanonUnderNameList [name | Binder name _ <- binders] body in
                MatchArm constructorName [Binder name Nothing | name <- names] body' |
                MatchArm constructorName binders body <- matchArms
            ]
alphaCanonicalizeInner (TermAnnot e ty) = TermAnnot (alphaCanonicalizeInner e) (alphaCanonicalizeInner ty)
alphaCanonicalizeInner e@(TermSortType _) = e
alphaCanonicalizeInner e@TermSortProp = e

alphaCanonicalize :: ValCtx -> Term -> Term
alphaCanonicalize vc t = let
        ?nextIndex = 0
        ?renamings = Map.fromList [(name, name) | (name, _) <- Map.toList vc]
    in alphaCanonicalizeInner t
--alphaCanonicalize vc x = fst $ State.runState (alphaCanonicalizeInner x) startingMapping
--    where startingMapping = Map.fromList [(name, name) | (name, _) <- Map.toList vc]

type FreshState = State.State Int

fresh :: String -> FreshState String
fresh name = do
    i <- State.get
    State.put (i + 1)
    return $ (fst $ span (/= '#') name) ++ "#" ++ show i

subst :: VariableName -> Term -> Term -> Term
subst old new t@(TermVar name)
    | name == old = new
    | otherwise = t
subst old new (TermApp fn arg) = TermApp (r fn) (r arg)
    where r = subst old new
subst old new (TermAbs (Binder name optionalTy) body)
    | old == name = TermAbs binder' body
    | otherwise   = TermAbs binder' (r body)
    where
        r = subst old new
        binder' = Binder name (r <$> optionalTy)
-- Ugh, I don't like this duplication...
subst old new (TermPi (Binder name optionalTy) body)
    | old == name = TermPi binder' body
    | otherwise   = TermPi binder' (r body)
    where
        r = subst old new
        binder' = Binder name (r <$> optionalTy)

-- There are many edge cases here.
-- In our outer well-formedness checking we demand that the parameter not shadow the fix's name.
-- So, the most pathological remaining cases are like:
--   fix f (x : f) : f { f }
--   fix f (x : x) : x { x }
-- What happens if we try to subst x to y or f to y in the above?
-- The answer is that we should get:
--   fix f (x : f) : f { f }   (x to y) becomes   fix f (x : f) : f { f }
--   fix f (x : x) : x { x }   (x to y) becomes   fix f (x : y) : x { x }
--   fix f (x : f) : f { f }   (f to y) becomes   fix f (x : y) : y { f }
--   fix f (x : x) : x { x }   (f to y) becomes   fix f (x : x) : x { x }
-- The binding rules are as follows:
--   fix 1 (2 : a) : b { c }
-- Inside of a: [] -- neither 1 nor 2 is visible.
-- Inside of b: [2] -- only 2 is visible.
-- Inside of c: [1, 2] -- both 1 and 2 are visible, with 2 ta
-- We therefore have to handle three cases: (old == 1), (old == 2), and otherwise.
subst old new (TermFix recName (Binder recArgName optionalRecArgTy) optionalTy body)
    -- The recName is bound inside of the body,
    | old == recName    = TermFix recName binder' (r <$> optionalTy) body
    | old == recArgName = TermFix recName binder' optionalTy body
    | otherwise         = TermFix recName binder' (r <$> optionalTy) (r body)
    where
        r = subst old new
        binder' = Binder recArgName (r <$> optionalRecArgTy)

subst old new (TermMatch scrutinee inClause returnClause matchArms) =
    TermMatch (r scrutinee) inClause returnClause (substInArm <$> matchArms)
    where
        r = subst old new
        substInArm arm@(MatchArm constructorName binders body)
            | old `elem` [name | Binder name _ <- binders] = arm
            | otherwise = MatchArm constructorName binders (r body)

subst old new (TermAnnot e ty) = TermAnnot (r e) (r ty)
    where r = subst old new
subst old new t@(TermSortType _) = t
subst old new t@TermSortProp = t

data NormalizationStrategy = CBV | WHNF deriving (Show, Eq, Ord)

normalizeBinder :: NormalizationStrategy -> ValCtx -> Binder -> FreshState Binder
normalizeBinder ns vc b@(Binder _ Nothing) = return b
normalizeBinder ns vc (Binder name (Just ty)) = do
    ty <- normalize ns vc ty
    return $ Binder name (Just ty)

normalizeOptionalTypeAnnot :: NormalizationStrategy -> ValCtx -> OptionalTypeAnnot -> FreshState OptionalTypeAnnot
-- A type annotation is never in head position, and therefore WHNF normalization should do nothing.
normalizeOptionalTypeAnnot WHNF _ = return
normalizeOptionalTypeAnnot CBV vc = traverse $ normalize CBV vc

deleteKeys :: (Ord k) => [k] -> Map.Map k a -> Map.Map k a
deleteKeys keys m = foldr Map.delete m keys

--etaExpandFix :: Term -> Term
--etaExpandFix fix@(TermFix recName b@(Binder recArgName _) optionalTypeAnnot body) =
--    TermAbs b (TermApp (TermAbs (Binder recName Nothing) body) fix)

formLetIn :: Binder -> Term -> Term -> Term
formLetIn binder x y = TermApp (TermAbs binder y) x

normalize :: NormalizationStrategy -> ValCtx -> Term -> FreshState Term
--normalize ns vc t = normalize' ns vc (traceStop ("Normalizing (ctx=" ++ (show $ Map.keys vc) ++ ") " ++ ScowproofDesugar.prettyTerm 0 t) t)
normalize = normalize'

normalize' :: NormalizationStrategy -> ValCtx -> Term -> FreshState Term
--normalize' ns vc (Map.findWithDefault t name vc)
normalize' ns vc t@(TermVar name) = case Map.lookup name vc of
    Just r -> normalize' ns vc r
    Nothing -> return t
normalize' ns vc (TermApp fn arg) = do
    fn <- normalize ns vc fn
    normedArg <- argNorm ns
    case fn of
        TermAbs (Binder name _) body -> normalize ns vc (subst name normedArg body)
        TermFix recName argBinder@(Binder recArgName _) optionalTypeAnnot body ->
            -- I think doing these substitutions non-simultaneously is okay due to recArgName being fresh.
            normalize ns vc (subst recArgName normedArg (subst recName fn body))
            where
                -- These inserts should never conflict, if the term passed our well-formedness check.
                innerVc = Map.insert recArgName normedArg (Map.insert recName fn vc)
            --let inner = formLetIn argBinder normedArg body in
            --normalize ns vc (formLetIn (Binder recName Nothing) fn inner)
            -- (TermApp (etaExpandFix fn) arg)
        _ -> return $ TermApp fn normedArg
        {-
        TermAbs (Binder name _) body -> normalize ns (Map.insert name normedArg vc) body
        TermFix recName argBinder@(Binder recArgName _) optionalTypeAnnot body ->
            normalize ns innerVc body
            where
                -- These inserts should never conflict, if the term passed our well-formedness check.
                innerVc = Map.insert recArgName normedArg (Map.insert recName fn vc)
            --let inner = formLetIn argBinder normedArg body in
            --normalize ns vc (formLetIn (Binder recName Nothing) fn inner)
            -- (TermApp (etaExpandFix fn) arg)
        _ -> return $ TermApp fn normedArg
        -}
    where
        argNorm WHNF = return arg
        argNorm CBV = normalize ns vc arg
normalize' ns vc (TermAbs (Binder name ty) body) = do
    newName <- fresh name
    normedTy <- case ns of
        WHNF -> return ty
        CBV -> normalizeOptionalTypeAnnot ns vc ty
    --let vc' = Map.insert name (TermVar newName) vc
    --normedBody <- normalize ns vc' body
    let normedBody = subst name (TermVar newName) body
    return $ TermAbs (Binder newName normedTy) normedBody

{-
(
    (fix f arg {body})
    val
)
->
(
    let f = (fix f arg {body}) in
    let arg = val in
    body
)
->
(
    (fun f =>
        (fun arg => body) val
    )
    (fix f arg {body})
)
-}

-- For some reason Bauer doesn't normalize inside of products in Spartan type theory, but I do.
normalize' WHNF vc t@(TermPi binder ty) = return t
normalize' CBV vc (TermPi binder ty) = TermPi <$> normalizeBinder CBV vc binder <*> normalize CBV vc ty

normalize' WHNF vc t@(TermFix recName binder optionalTy body) = do
    newRecName <- fresh recName
    return $ TermFix newRecName binder optionalTy (subst recName (TermVar newRecName) body)
-- XXX: FIXME: This CBV is still wrong! I need to subst recName!
normalize' CBV vc t@(TermFix recName binder optionalTy body) =
    TermFix recName <$> normalizeBinder CBV vc binder <*> normalizeOptionalTypeAnnot CBV vc optionalTy <*> normalize CBV vc body
--normalize' CBV vc t@(TermFix recName binder optionalTypeAnnot body) =
--    TermFix recName <$> normalizeBinder CBV vc binder <*> normalizeOptionalTypeAnnot CBV vc optionalTypeAnnot <*> normalize CBV vc body

normalize' ns vc t@(TermMatch scrutinee inClause returnClause matchArms) = do
    scrutinee' <- normalize ns vc scrutinee
    case [
            (binders, applied) |
            MatchArm constructorName binders body <- matchArms,
            -- Should I maybe store my binders in pre-reversed order?
            -- Also, how do I do this with a "let Just applied = ..." instead? That gives an irrefutable pattern issue.
            Just applied <- [matchAppSpine constructorName (reverse binders) scrutinee' body]
        ] of
            -- Here the return value is still in head position, so we must keep normalizing, even in WHNF.
            (binders, result) : _ -> normalize ns (armContext binders) result
            -- Here the match arms won't be in head position, so we potentially stop normalizing them.
            [] -> do
                let vcReturn = deleteKeys (inVariables inClause) vc
                returnClause' <- normalizeOptionalTypeAnnot ns vcReturn returnClause
                matchArms' <- mapM (normalizeArm ns) matchArms
                return $ TermMatch scrutinee' inClause returnClause' matchArms'
                where
                    inVariables (InPresent _ vars) = vars
                    inVariables InAbsent = []
                    normalizeArm WHNF arm = return arm
                    normalizeArm CBV (MatchArm constructorName binders body) = do
                        body' <- normalize ns (armContext binders) body
                        return $ MatchArm constructorName binders body'
    where
        --matchAppSpine' a b c d =
        --    trace ("(Matching " ++ show c ++ " with " ++ show a ++ " " ++ show b ++ " in ctx: " ++ show (Map.keys vc) ++ ")") (matchAppSpine a b c d)
        matchAppSpine :: VariableName -> [Binder] -> Term -> Term -> Maybe Term
        matchAppSpine constructorName [] (TermVar constructorName2) body
            | (constructorName == constructorName2) = Just body
            | otherwise = Nothing
        matchAppSpine constructorName (binder:binders) (TermApp fn arg) body = do
            next <- matchAppSpine constructorName binders fn body
            return $ TermApp (TermAbs binder next) arg
        -- Be careful here; I maybe want to error out on some ill-formed cases here.
        matchAppSpine _ _ _ _ = Nothing
        armContext binders = deleteKeys [name | Binder name _ <- binders] vc

normalize' WHNF vc (TermAnnot e ty) = TermAnnot <$> normalize WHNF vc e <*> return ty
normalize' CBV  vc (TermAnnot e ty) = TermAnnot <$> normalize CBV vc e <*> normalize CBV vc ty

{-
nat::S [x, y, z] => body

(App
    (App
        (App
            (Var nat::S)
            a
        )
        b
    )
    c
)

let z = c in
let y = b in
let x = a in
    (<- normalize ns vc body)
-}

-- Passed through.
normalize' _ _ t@(TermSortType _) = return t
normalize' _ _ t@TermSortProp = return t

traceVal msg x = traceStop (msg ++ ": " ++ show x) x

traceStop :: String -> a -> a
traceStop msg x = System.IO.Unsafe.unsafePerformIO $ do
    seq (length msg) (return ())
    putStrLn msg
    _ <- getChar
    return x

normalizeOnce :: NormalizationStrategy -> ValCtx -> Term -> Term
normalizeOnce ns vc t = fst $ State.runState (normalize ns vc t) 0

coerceToProduct = id

isSort :: Term -> Bool
isSort (TermSortType _) = True
isSort TermSortProp = True
isSort _ = False

infer :: ValCtx -> TypeCtx -> Term -> ExceptStr Term
infer vc tc (TermVar name) = case (Map.lookup name vc, Map.lookup name tc) of
    (_, Just ty) -> return ty
    (Just t, _) -> infer vc tc t
    _ -> throwError $ "No type or definition for variable: " ++ name
infer vc tc (TermApp fn arg) = do
    fnType <- coerceToProduct <$> infer vc tc fn
    (Binder argName optionalArgTy, fnResultTy) <- case fnType of
        TermPi binder body -> return (binder, body)
        _ -> throwError "Function types must be products"
    argTy <- case optionalArgTy of
        Just ty -> return ty
        _ -> throwError "Function types in applications must infer with concrete argument types"
    argTypeCorrect <- check vc tc arg argTy
    when (not argTypeCorrect) (throwError "Application ill-typed")
    return $ subst argName arg fnResultTy
infer vc tc (TermAbs (Binder argName (Just argTy)) body) = do
    argSort <- infer vc tc argTy
    when (not (isSort argSort)) (throwError "Abstraction argument types must live in a sort")
    resultTy <- infer vc (Map.insert argName argTy tc) body
    return $ TermPi (Binder argName (Just argTy)) resultTy
infer vc tc (TermAbs _ _) = throwError "Abstractions must have an argument type"
infer vc tc (TermPi (Binder argName (Just argTy)) body) = do
    argSort <- infer vc tc argTy
    when (not (isSort argSort)) (throwError "Product argument types must live in a sort")
    resultSort <- infer vc (Map.insert argName argTy tc) body
    when (not (isSort resultSort)) (throwError "Product result types must live in a sort")
    return $ resultSort
infer vc tc (TermPi _ _) = throwError "Products must have an argument type"
infer _ _ (TermSortType universeIndex) = return $ TermSortType (universeIndex + 1)
-- Does this make sense?
infer _ _ TermSortProp = return $ TermSortType 0

-- Do I need the TypeCtx? Like, can I alpha canonicalize something that only has a typing?
compareTerms :: ValCtx -> Term -> Term -> Bool
compareTerms vc a b = normed a == normed b
    where normed t = alphaCanonicalize vc $ normalizeOnce CBV vc t

check :: ValCtx -> TypeCtx -> Term -> Term -> ExceptStr Bool
--check ctx _ = undefined
check vc tc e ty = do
    inferredTy <- infer vc tc e
    return $ compareTerms vc ty inferredTy

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

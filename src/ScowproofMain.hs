
import qualified Data.Map as Map
import qualified System.Environment
import qualified Control.Monad.Except

import qualified ScowproofParse
import qualified ScowproofKernel
import qualified ScowproofDesugar

runCommand :: ScowproofDesugar.GlobalScope -> ScowproofParse.Command -> IO ()
runCommand globalScope (ScowproofParse.CmdInfer expr) = do
    putStrLn $ "Infer: " ++ ScowproofDesugar.prettyTerm 7 term
    case errOrResultTerm of
        Left msg -> putStrLn $ "Error: " ++ msg
        Right resultTerm -> putStrLn $ "=      " ++ ScowproofDesugar.prettyTerm 7 resultTerm
    where
        term = ScowproofDesugar.desugarExpr expr
        valCtx = Map.fromList $ ScowproofDesugar.globalTerms globalScope
        typeCtx = ScowproofKernel.globalTyping globalScope
        errOrResultTerm = Control.Monad.Except.runExcept $ ScowproofKernel.infer valCtx typeCtx term
runCommand globalScope (ScowproofParse.CmdCheck termExpr typeExpr) = putStrLn "Check not implemented"
runCommand globalScope (ScowproofParse.CmdEval expr) = do
    putStrLn $ "Eval: " ++ ScowproofDesugar.prettyTerm 6 term
    putStrLn $ "=     " ++ ScowproofDesugar.prettyTerm 6 resultTerm
    where
        term = ScowproofDesugar.desugarExpr expr
        valCtx = Map.fromList $ ScowproofDesugar.globalTerms globalScope
        resultTerm = ScowproofKernel.normalizeOnce ScowproofKernel.WHNF valCtx term
runCommand globalScope (ScowproofParse.CmdAlphaCanon expr) = do
    putStrLn $ "Alpha canonicalize:\n  " ++ ScowproofDesugar.prettyTerm 2 term
    putStrLn $ "= " ++ ScowproofDesugar.prettyTerm 2 resultTerm
    where
        term = ScowproofDesugar.desugarExpr expr
        valCtx = Map.fromList $ ScowproofDesugar.globalTerms globalScope
        typeCtx = ScowproofKernel.globalTyping globalScope
        resultTerm = ScowproofKernel.alphaCanonicalize valCtx typeCtx term

main :: IO ()
main = do
    args <- System.Environment.getArgs
    ast <- ScowproofParse.parseFile $ head args

    -- putStrLn "\n=== AST:"
    -- putStrLn $ show ast

    let globalScope = ScowproofDesugar.makeGlobalScope ast
    -- putStrLn "\n=== Global scope:"
    -- putStrLn $ show globalScope

    -- Make a root context.
    --let rootContext = Map.fromList [entry vernac | vernac <- ast, isDefinition vernac]
    --        where
    --            entry (VernacDefinition )
    --            isDefinition (VernacDefinition _ _ _ _) = True
    --            isDefinition _ = False

    putStrLn "===== Terms ====="
    let printExpr (name, term) = putStrLn $ name ++ " = " ++ ScowproofDesugar.prettyTerm 0 term in
        mapM_ printExpr $ ScowproofDesugar.globalTerms globalScope

    putStrLn "\n===== Commands ====="
    mapM_ (runCommand globalScope) $ ScowproofDesugar.globalCommands globalScope

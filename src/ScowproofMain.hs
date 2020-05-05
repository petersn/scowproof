
import qualified Data.Map as Map
import qualified System.Environment

import qualified ScowproofParse
import qualified ScowproofKernel
import qualified ScowproofDesugar

runCommand :: ScowproofParse.Command -> IO ()
runCommand cmd = putStrLn "Yay"

main :: IO ()
main = do
    args <- System.Environment.getArgs
    ast <- ScowproofParse.parseFile $ head args

    putStrLn "\n=== AST:"
    putStrLn $ show ast

    let globalScope = ScowproofDesugar.makeGlobalScope ast
    putStrLn "\n=== Global scope:"
    putStrLn $ show globalScope

    -- Make a root context.
    --let rootContext = Map.fromList [entry vernac | vernac <- ast, isDefinition vernac]
    --        where
    --            entry (VernacDefinition )
    --            isDefinition (VernacDefinition _ _ _ _) = True
    --            isDefinition _ = False

    putStrLn "\n===== Terms ====="
    let printExpr (name, term) = putStrLn $ name ++ " = " ++ ScowproofDesugar.prettyTerm 0 term in
        mapM_ printExpr $ Map.toList (ScowproofDesugar.globalTerms globalScope)

    putStrLn "\n===== Commands ====="
    mapM_ runCommand $ ScowproofDesugar.globalCommands globalScope

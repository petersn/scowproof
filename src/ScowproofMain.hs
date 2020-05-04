
import qualified Data.Map as Map
import qualified System.Environment

import qualified ScowproofParse
import qualified ScowproofKernel
import qualified ScowproofDesugar

main :: IO ()
main = do
    args <- System.Environment.getArgs
    ast <- ScowproofParse.parseFile $ head args

    putStrLn "AST:"
    putStrLn $ show ast

    let globalScope = ScowproofDesugar.makeGlobalScope ast
    putStrLn $ show globalScope

    -- Make a root context.
    --let rootContext = Map.fromList [entry vernac | vernac <- ast, isDefinition vernac]
    --        where
    --            entry (VernacDefinition )
    --            isDefinition (VernacDefinition _ _ _ _) = True
    --            isDefinition _ = False

    return ()


import qualified System.Environment
import qualified ScowproofParse



main :: IO ()
main = do
    args <- System.Environment.getArgs
    ast <- ScowproofParse.parseFile $ head args
    putStrLn "AST:";
    putStrLn $ show ast
    return ()

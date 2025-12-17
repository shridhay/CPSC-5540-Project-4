module Main (main) where
import Verifier.Verify 
import Verifier.SEE
import System.Environment 
import System.IO.Error (catchIOError)

main :: IO ()
main = do
    as <- getArgs
    case as of 
      [filename, nstr] -> do 
        let n = read nstr :: Int
        prog <- (readFile filename)
        result <- (verify prog n)
        output result        
      _ ->
        putStrLn "Usage: see <program.imp> <loop-bound>"

output :: VerifyResult -> IO ()
output SAT = putStrLn "SAT"
output (ParseError msg) = putStrLn ("Parse Error: " ++ msg)
output (Unknown msg) = putStrLn ("Unknown: " ++ msg)
output (Counterexample model) = putStrLn model 

module Main (main) where
import Verifier.SEE (executeSEE, Result(..))
import System.Environment 
import System.IO.Error (catchIOError)

main :: IO ()
main = do
    as <- getArgs
    case as of 
      [filename, nstr] -> do 
        let n = read nstr :: Int
        prog <- (readFile filename)
        result <- (executeSEE prog n)
        output result        
      _ ->
        putStrLn "Usage: SEE <path/to/program.imp> <loop-limit>"

output :: Result -> IO ()
output Verified = putStrLn "SAT"
output (NotVerified counterexamples) = mapM_ putStrLn counterexamples
output (ParseError msg) = putStrLn ("Parse Error: " ++ msg)
output (Unknown msg) = putStrLn ("Unknown: " ++ msg)
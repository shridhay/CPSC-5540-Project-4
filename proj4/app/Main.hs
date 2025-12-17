module Main (main) where

import Verifier.Verify (verify)
import System.Environment 
import System.IO.Error (catchIOError)

main :: IO ()
main = do
    as <- getArgs
    case as of 
      [filename, intstr] -> do
        progstr <- catchIOError (readFile filename) (\_ -> error "Could not read file")
        let n = read intstr :: Int
        result <- verify progstr n
        print result  
      _ ->
        error "Usage: see <program.imp> <loop-bound>"

-- main :: IO ()
-- main = do
--     as <- getArgs
--     prog <- readFile (head as)
--     result <- catchIOError (verify prog) (return . Unknown . show)
--     case result of
--       Verified -> putStrLn "Verified"
--       NotVerified -> putStrLn "Not verified"
--       Unknown msg -> putStrLn ("Verifier returned unknown: " ++ msg)

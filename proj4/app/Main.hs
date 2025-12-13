module Main (main) where

import Verifier.Verify (verify, VerifyResult(..), Violation(..))
import System.Environment 
import System.IO.Error (catchIOError)

main :: IO ()
main = do
    as <- getArgs
    case as of 
      [filename, intstr] -> do
        progstr <- catchIOError (readFile filename)
        let n = read intstr :: Int
        result <- verify progstr n
      _ ->
      error "Usage: see <program.imp> <loop-bound>"



    -- prog <- readFile (head as)
    -- result <- catchIOError (verify prog) (return . Unknown . show)
    -- case result of
    --   Verified -> putStrLn "Verified"
    --   NotVerified -> putStrLn "Not verified"
    --   Unknown msg -> putStrLn ("Verifier returned unknown: " ++ msg)
-- main :: IO ()
-- main = do
--     as <- getArgs
--     prog <- readFile (head as)
--     result <- catchIOError (verify prog) (return . Unknown . show)
--     case result of
--       Verified -> putStrLn "Verified"
--       NotVerified -> putStrLn "Not verified"
--       Unknown msg -> putStrLn ("Verifier returned unknown: " ++ msg)

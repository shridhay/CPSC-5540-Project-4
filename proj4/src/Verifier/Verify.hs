module Verifier.Verify (verify) where

import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Lazy.Char8 as LC

import SMTLIB.Backends (QueuingFlag (..), command, command_, initSolver)
import qualified SMTLIB.Backends.Z3 as Z3

verify :: String -> IO (Maybe String)
verify z3string = do
  Z3.with Z3.defaultConfig $ \handle -> do
    solver <- initSolver Queuing (Z3.toBackend handle)
    res <- command solver (B.stringUtf8 z3string)
    case (LC.unpack res) of
      "sat\n" -> do
        model <- command solver (B.stringUtf8 "(get-model)")
        return (Just (LC.unpack model))
      "unsat\n" -> 
        return Nothing
      other -> 
        return (Just ("Unknown Z3 result: " ++ other))

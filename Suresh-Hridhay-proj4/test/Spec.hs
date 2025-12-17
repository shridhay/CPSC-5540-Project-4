import Verifier.Verify
import Verifier.SEE

import Data.List (findIndices)
import Data.Maybe (fromMaybe)
import GHC.IO.Handle (hFlush)
import GHC.IO.StdHandles (stdout)
import GHC.Utils.Misc (uncurry3)
import System.Directory (listDirectory)
import System.Exit (die)
import System.IO.Error (catchIOError)
import System.Timeout (timeout)

main :: IO ()
main = do
  putStrLn "Does Nothing"
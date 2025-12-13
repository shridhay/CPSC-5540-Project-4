module Verifier.SEE  (SymState(..), SymVal(..), symExec) where

import Language
import Verifier.GC 
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State.Lazy

type SymVar = Name

type PC = Assertion

data SymVal = SymInt Name
            | SymArr Name
            deriving (Eq, Show)

data SymState = SymState { 
                vars :: Map Name SymVal, 
                pc :: Assertion } 
            deriving (Show)

evalArith :: SymState -> ArithExp -> ArithExp
evalArith state (Num n) = Num n
evalArith state (Var x) =
    case Map.lookup x (vars state) of
      Just (SymInt name) -> Var name
      _ -> Var x
evalArith state (Add l r) = Add (evalArith state l) (evalArith state r)
evalArith state (Sub l r) = Sub (evalArith state l) (evalArith state r)
evalArith state (Mul l r) = Mul (evalArith state l) (evalArith state r)
evalArith state (Div l r) = Div (evalArith state l) (evalArith state r)
evalArith state (Mod l r) = Mod (evalArith state l) (evalArith state r)
evalArith state (Parens p) = Parens (evalArith state p)

freshSymVar :: String -> State Int Name
freshVar prefix = do
  n <- get
  put (n + 1)
  return (prefix ++ "--SYM--temp--" ++ show n)

evalBool :: SymState -> BoolExp -> BoolExp
evalBool state (BCmp b) = BCmp b
evalBool state (BNot b) = BNot (evalBool state b)
evalBool state (BDisj b1 b2) = BDisj (evalBool state b1) (evalBool state b2)
evalBool state (BConj b1 b2) = BConj (evalBool state b1) (evalBool state b2)
evalBool state (BParens b) = BParens (evalBool state b)

evalComp :: SymState -> Comparison -> Comparison
evalComp state (Eq a1 a2)  = Eq (evalArith state a1) (evalArith state a2)
evalComp state (Neq a1 a2) = Neq (evalArith state a1) (evalArith state a2)
evalComp state (Le a1 a2)  = Le (evalArith state a1) (evalArith state a2)
evalComp state (Ge a1 a2)  = Ge (evalArith state a1) (evalArith state a2)
evalComp state (Lt a1 a2)  = Lt (evalArith state a1) (evalArith state a2)
evalComp state (Gt a1 a2)  = Gt (evalArith state a1) (evalArith state a2)
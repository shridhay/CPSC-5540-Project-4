module Verifier.SEE  (SymState(..), SymVal(..), symExec) where
import Verifier.Verify (verify, Result(..))
import Language
import Verifier.GC 
import Data.Map (Map)
import qualified Data.Map as Map 
import Control.Monad.State.Lazy

type SymVar = Name
type PC = Assertion

data SymVal = SymInt Name
            | SymArr (Map ArithExp SymVal) 
            deriving (Eq, Show)

data SymState = SymState { 
                vars :: Map Name SymVal, 
                pc :: Assertion}
              deriving (Show)

data Result = Verified | NotVerified | Unknown String
              deriving (Eq, Show)

evalArith :: SymState -> ArithExp -> ArithExp
evalArith state (Num n) = Num n
evalArith state (Var varName) =
    case Map.lookup varName (vars state) of
      Just (SymInt name) -> Var name
      _ -> Var varName 
evalArith state (Read arrName idx) =
    case Map.lookup arrName (vars state) of
        Just (SymArr arrMap) -> 
            let evalIdx = evalArith state idx
            in case Map.lookup evalIdx arrMap of
                Just (SymInt name) -> Var name
                Nothing -> Read arrName evalIdx
        _ -> Read arrName (evalArith state idx)

evalArith state (Add l r) = Add (evalArith state l) (evalArith state r)
evalArith state (Sub l r) = Sub (evalArith state l) (evalArith state r)
evalArith state (Mul l r) = Mul (evalArith state l) (evalArith state r)
evalArith state (Div l r) = Div (evalArith state l) (evalArith state r)
evalArith state (Mod l r) = Mod (evalArith state l) (evalArith state r)
evalArith state (Parens p) = Parens (evalArith state p)

freshVar :: String -> State Int Name
freshVar prefix = do
  n <- get
  put (n + 1)
  return (prefix ++ "--SYMtemp--" ++ show n)

freshSymVar :: String -> State Int Name
freshSymVar prefix = do
  n <- get
  put (n + 1)
  return (prefix ++ "--SYM--" ++ show n)

evalBool :: SymState -> BoolExp -> BoolExp
evalBool state (BCmp b)      = BCmp (evalComp state b)
evalBool state (BNot b)      = BNot (evalBool state b)
evalBool state (BDisj b1 b2) = BDisj (evalBool state b1) (evalBool state b2)
evalBool state (BConj b1 b2) = BConj (evalBool state b1) (evalBool state b2)
evalBool state (BParens b)   = BParens (evalBool state b)

evalComp :: SymState -> Comparison -> Comparison
evalComp state (Eq a1 a2)  = Eq (evalArith state a1) (evalArith state a2)
evalComp state (Neq a1 a2) = Neq (evalArith state a1) (evalArith state a2)
evalComp state (Le a1 a2)  = Le (evalArith state a1) (evalArith state a2)
evalComp state (Ge a1 a2)  = Ge (evalArith state a1) (evalArith state a2)
evalComp state (Lt a1 a2)  = Lt (evalArith state a1) (evalArith state a2)
evalComp state (Gt a1 a2)  = Gt (evalArith state a1) (evalArith state a2)

boolToAssertion :: BoolExp -> Assertion
boolToAssertion (BCmp c)      = ACmp c
boolToAssertion (BNot b)      = ANot (boolToAssertion b)
boolToAssertion (BDisj b1 b2) = ADisj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BConj b1 b2) = AConj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BParens b)   = AParens (boolToAssertion b)

evalAssertion :: SymState -> Assertion -> Assertion
evalAssertion state (ACmp c)       = ACmp (evalComp state c)
evalAssertion state (ANot a)       = ANot (evalAssertion state a)
evalAssertion state (ADisj a1 a2)  = ADisj (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AConj a1 a2)  = AConj (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AImpl a1 a2)  = AImpl (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AForall ns a) = AForall ns (evalAssertion state a)
evalAssertion state (AExists ns a) = AExists ns (evalAssertion state a)
evalAssertion state (AParens a)    = AParens (evalAssertion state a)

wpToZ3 :: Assertion -> String
wpToZ3 a = varMapToZ3String (getVar a) ++ "(assert (not " ++ assertToZ3 a ++ "))(check-sat)"

getVar :: Assertion -> Map Name SymVal
getVar (ACmp c) = getVarCmp c
getVar (ANot a) = getVar a
getVar (ADisj a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AConj a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AImpl a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AForall n a) = Map.union (getVarNameList n) (getVar a) 
getVar (AExists n a) = Map.union (getVarNameList n) (getVar a)
getVar (AParens a) = getVar a

getVarCmp :: Comparison -> Map Name SymVal
getVarCmp (Eq a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Neq a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Le a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Ge a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Lt a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Gt a1 a2) = Map.union (getVarArith a1) (getVarArith a2)

getVarArith :: ArithExp -> Map Name SymVal
getVarArith (Num _) = Map.empty 
getVarArith (Var n) = Map.singleton n (SymInt n)
getVarArith (Read n a) = Map.union (Map.singleton n (SymArr Map.empty)) (getVarArith a)
getVarArith (Add a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Sub a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Mul a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Div a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Mod a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Parens a) = getVarArith a

getVarNameList :: [Name] -> Map Name SymVal
getVarNameList [] = Map.empty
getVarNameList [n] = Map.singleton n (SymInt n)
getVarNameList (n:ns) = Map.union (Map.singleton n (SymInt n)) (getVarNameList ns) 

assertToZ3 :: Assertion -> String
assertToZ3 (ACmp comparison) = comparisonToZ3 comparison
assertToZ3 (ANot a) = "(not " ++ assertToZ3 a ++ ")"
assertToZ3 (ADisj a1 a2) = "(or " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AConj a1 a2) = "(and " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AImpl a1 a2) = "(=> " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AForall n a) = "(forall (" ++ forallVarString n ++ ") " ++ assertToZ3 a ++ ")"
assertToZ3 (AExists n a) = "(exists (" ++ forallVarString n ++ ") " ++ assertToZ3 a ++ ")"
assertToZ3 (AParens p) = assertToZ3 p

forallVarString :: [Name] -> String 
forallVarString [] = ""
forallVarString [n] = "(" ++ n ++ " Int)"
forallVarString (n:ns) = "(" ++ n ++ " Int)" ++ forallVarString ns

comparisonToZ3 :: Comparison -> String
comparisonToZ3 (Eq a1 a2) = "(= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Neq a1 a2) = "(not (= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ "))"
comparisonToZ3 (Le a1 a2) = "(<= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Ge a1 a2) = "(>= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Lt a1 a2) = "(< " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Gt a1 a2) = "(> " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"

arithToZ3 :: ArithExp -> String
arithToZ3 (Num n) = show n
arithToZ3 (Var v) = v 
arithToZ3 (Read a i) = "(select " ++ a ++ " " ++ arithToZ3 i ++ ")"
arithToZ3 (Add a1 a2) = "(+ " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Sub a1 a2) = "(- " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Mul a1 a2) = "(* " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Div a1 a2) = "(div " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Mod a1 a2) = "(mod " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Parens a) = arithToZ3 a

symValasString :: SymVal -> String
symValasString (SymInt _) = "Int"
symValasString (SymArr _) = "(Array Int Int)"

symValoZ3String :: Name -> SymVal -> String
symValoZ3String k v = "(declare-const " ++ k ++ " " ++ (symValasString v) ++ ")"

varMapToZ3String :: Map Name SymVal -> String
varMapToZ3String m = (Map.foldr (++) "" (Map.mapWithKey symValoZ3String m))

symExecM :: SymState -> Block -> State Int [SymState]
symExecM state [] = return [state]
symExecM state (stmt:stmts) = 
  case stmt of
    Assign var expr -> do
      symName <- freshSymVar var
      let evalExpr = evalArith state expr
          newState = state { vars = Map.insert var (SymInt symName) (vars state) }
      symExecM newState stmts

    AssertStmt assertion -> do 
      let assertionEval = evalAssertion state assertion
          newState = state { pc = AConj (pc state) assertionEval }
      symExecM newState stmts
      




symExec :: SymState -> Block -> [SymState]
symExec state block = evalState (symExecM state block) 0

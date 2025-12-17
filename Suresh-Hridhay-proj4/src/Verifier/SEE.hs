module Verifier.SEE (Result(..), executeSEE, SymState(..), SymVal(..), symExec) where
import Parser.Parser
import Verifier.Verify (verify)
import Language
import Data.Map (Map)
import qualified Data.Map as Map 
import Control.Monad.State.Lazy

data SymVal = SymInt Name
            | SymArr Name (Map ArithExp SymVal) 
            deriving (Eq, Show, Ord)

data SymState = SymState { 
                vars :: Map Name SymVal, 
                pc :: Assertion,
                loopLimit :: Int}
              deriving (Show)

data Result = Verified 
            | NotVerified [String]
            | ParseError String
            | Unknown String
            deriving (Eq, Show)

evalArith :: SymState -> ArithExp -> ArithExp
evalArith state (Num n) = Num n
evalArith state (Var varName) =
    case (Map.lookup varName (vars state)) of
      Just (SymInt name) -> Var name
      _ -> Var varName 
evalArith state (Read arrName idx) =
    case (Map.lookup arrName (vars state)) of
        Just (SymArr _ arrMap) -> 
            case (Map.lookup (evalArith state idx) arrMap) of
              Just (SymInt name) -> Var name
              Nothing -> Read arrName (evalArith state idx)
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
  return (prefix ++ "--temp--" ++ show n)

evalBool :: SymState -> BoolExp -> BoolExp
evalBool state (BCmp b) = BCmp (evalComparison state b)
evalBool state (BNot b) = BNot (evalBool state b)
evalBool state (BDisj b1 b2) = BDisj (evalBool state b1) (evalBool state b2)
evalBool state (BConj b1 b2) = BConj (evalBool state b1) (evalBool state b2)
evalBool state (BParens b) = BParens (evalBool state b)

evalComparison :: SymState -> Comparison -> Comparison
evalComparison state (Eq a1 a2) = Eq (evalArith state a1) (evalArith state a2)
evalComparison state (Neq a1 a2) = Neq (evalArith state a1) (evalArith state a2)
evalComparison state (Le a1 a2) = Le (evalArith state a1) (evalArith state a2)
evalComparison state (Ge a1 a2) = Ge (evalArith state a1) (evalArith state a2)
evalComparison state (Lt a1 a2) = Lt (evalArith state a1) (evalArith state a2)
evalComparison state (Gt a1 a2) = Gt (evalArith state a1) (evalArith state a2)

boolToAssertion :: BoolExp -> Assertion
boolToAssertion (BCmp c) = ACmp c
boolToAssertion (BNot b) = ANot (boolToAssertion b)
boolToAssertion (BDisj b1 b2) = ADisj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BConj b1 b2) = AConj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BParens b) = AParens (boolToAssertion b)

evalAssertion :: SymState -> Assertion -> Assertion
evalAssertion state (ACmp c) = ACmp (evalComparison state c)
evalAssertion state (ANot a) = ANot (evalAssertion state a)
evalAssertion state (ADisj a1 a2) = ADisj (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AConj a1 a2) = AConj (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AImpl a1 a2) = AImpl (evalAssertion state a1) (evalAssertion state a2)
evalAssertion state (AForall ns a) = AForall ns (evalAssertion state a)
evalAssertion state (AExists ns a) = AExists ns (evalAssertion state a)
evalAssertion state (AParens a) = AParens (evalAssertion state a)

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
getVarArith (Read n a) = Map.union (Map.singleton n (SymArr n Map.empty)) (getVarArith a)
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
symValasString (SymArr _ _) = "(Array Int Int)"

symValoZ3String :: Name -> SymVal -> String
symValoZ3String k v = "(declare-const " ++ k ++ " " ++ (symValasString v) ++ ")"

varMapToZ3String :: Map Name SymVal -> String
varMapToZ3String m = (Map.foldr (++) "" (Map.mapWithKey symValoZ3String m))

assertionToZ3 :: Assertion -> String
assertionToZ3 a = varMapToZ3String (getVar a) ++ "(assert " ++ assertToZ3 a ++ ")(check-sat)"

executeSEE :: String -> Int -> IO Result
executeSEE progString loopLimit = do
  case (parseProg progString) of
    Just prog -> do
      let paths = runProgram prog loopLimit
      counterexamples <- checkPaths paths
      if null counterexamples
        then return Verified
        else return (NotVerified counterexamples)
    Nothing -> return (ParseError "Parsing failed")
    
checkPaths :: [SymState] -> IO [String]
checkPaths [] = return []
checkPaths (state:rest) = do
  let pathConditions = pc state
      z3String = assertionToZ3 pathConditions
  res <- verify z3String
  restRes <- checkPaths rest
  case res of
    Nothing -> return restRes  
    Just model -> return (model : restRes)  

assumeTrue :: Assertion
assumeTrue = (ACmp (Eq (Num 0) (Num 0)))

paramToSymVal :: Params -> (Name, SymVal)
paramToSymVal (IntParam name) = (name, SymInt name)
paramToSymVal (ArrParam name) = (name, SymArr name Map.empty)

initialState :: [Params] -> Int -> SymState
initialState params n = 
  let initialVars = Map.fromList (map paramToSymVal params)
      initialPC = assumeTrue
  in SymState initialVars initialPC n

addPreconditions :: SymState -> [Assertion] -> SymState
addPreconditions state [] = state
addPreconditions state (pre:pres) = 
  let newState = state { pc = AConj (pc state) (evalAssertion state pre) }
  in addPreconditions newState pres

runProgram :: Program -> Int -> [SymState]
runProgram (name, params, preconditions, assertions, block) n =
  symExec (addPreconditions (initialState params n) preconditions) block

symExec :: SymState -> Block -> [SymState]
symExec state block = evalState (symExecM state block) 0

symExecM :: SymState -> Block -> State Int [SymState]
symExecM state [] = return [state]
symExecM state (stmt:stmts) = 
  case stmt of
    AssertStmt assertion -> do 
      let assertionEval = evalAssertion state assertion
          nextState = state { pc = AConj (pc state) (ANot assertionEval) }
      symExecM nextState stmts

    Assign x e -> do
      tmp <- freshVar x
      let expr = evalArith state e
          constraint = ACmp (Eq (Var tmp) expr)
          nextState = state 
            { vars = Map.insert x (SymInt tmp) (vars state)
            , pc = AConj (pc state) constraint}
      symExecM nextState stmts

    Write a i v -> do
      tmpA <- freshVar (a ++ "--arr--")
      let idx = evalArith state i
          expr = evalArith state v
          constraint = ACmp (Eq (Var tmpA) expr)
          newArr = case (Map.lookup a (vars state)) of
            Just (SymArr name arrMap) -> SymArr name (Map.insert idx (SymInt tmpA) arrMap)
            _ -> SymArr a (Map.singleton idx (SymInt tmpA))
          nextState = state 
            { vars = Map.insert a newArr (vars state)
            , pc = AConj (pc state) constraint}
      symExecM nextState stmts

    If b c1 c2 -> do
      let conditionExpr = evalBool state b
          ifTrueState = state { pc = AConj (pc state) (boolToAssertion conditionExpr) }
          ifFalseState = state { pc = AConj (pc state) (ANot (boolToAssertion conditionExpr)) }
      truePaths <- (symExecM ifTrueState c1)
      falsePaths <- (symExecM ifFalseState c2)
      ifTrueList <- mapM (\x -> symExecM x stmts) truePaths
      ifFalseList <- mapM (\x -> symExecM x stmts) falsePaths
      return (concat ifTrueList ++ concat ifFalseList)

    ParAssign x1 x2 e1 e2 -> do
      temp1 <- freshVar x1
      temp2 <- freshVar x2
      let evalE1 = evalArith state e1
          evalE2 = evalArith state e2
          nextState = state 
            { vars = Map.union (Map.fromList [(x1, SymInt temp1), (x2, SymInt temp2)]) (vars state)
            , pc = (AConj (AConj (pc state) (ACmp (Eq (Var temp1) evalE1))) (ACmp (Eq (Var temp2) evalE2)))
            }
      symExecM nextState stmts

    While g invs cmds -> do
      let condExpr = evalBool state g
          condAssertion = boolToAssertion condExpr
      if loopLimit state <= 0
        then do
          let exitState = state { pc = AConj (pc state) (ANot condAssertion) }
          symExecM exitState stmts
        else do
          let exitState = state { pc = AConj (pc state) (ANot condAssertion) }
          exitPaths <- symExecM exitState stmts
          let enterState = state 
                { pc = AConj (pc state) condAssertion, loopLimit = loopLimit state - 1}
          bodyPaths <- symExecM enterState cmds
          iterPathsList <- mapM (\x -> symExecM x (stmt:stmts)) bodyPaths
          return (exitPaths ++ concat iterPathsList)
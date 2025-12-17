module Language (ArithExp(..), Assertion(..), Block, BoolExp(..), Comparison(..), Program, Statement(..), Name, Params(..)) where

type Name = String

data ArithExp = Num Int
              | Var Name
              | Read Name ArithExp
              | Add ArithExp ArithExp
              | Sub ArithExp ArithExp
              | Mul ArithExp ArithExp
              | Div ArithExp ArithExp
              | Mod ArithExp ArithExp
              | Parens ArithExp
              deriving (Eq, Ord, Show)

data Comparison = Eq ArithExp ArithExp
                | Neq ArithExp ArithExp
                | Le ArithExp ArithExp
                | Ge ArithExp ArithExp
                | Lt ArithExp ArithExp
                | Gt ArithExp ArithExp
                deriving (Show)

data BoolExp = BCmp Comparison
             | BNot BoolExp
             | BDisj BoolExp BoolExp
             | BConj BoolExp BoolExp
             | BParens BoolExp
             deriving (Show)

data Assertion = ACmp Comparison
               | ANot Assertion
               | ADisj Assertion Assertion
               | AConj Assertion Assertion
               | AImpl Assertion Assertion
               | AForall [Name] Assertion
               | AExists [Name] Assertion
               | AParens Assertion
               deriving (Show)

data Statement = Assign Name ArithExp
               | ParAssign Name Name ArithExp ArithExp
               | Write Name ArithExp ArithExp
               | If BoolExp Block Block
               | While BoolExp [Assertion] Block
               | AssertStmt Assertion
               deriving (Show)

data Params = IntParam Name
           | ArrParam Name
           deriving (Eq, Ord, Show)

type Block = [Statement]

type Program = (Name, [Params], [Assertion], [Assertion], Block)

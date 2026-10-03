module Test.Coverage where

import Control.Exception
import System.Environment
import System.Exit

import Common
import Cxt
import Cxt.Type
import Errors
import Evaluation
import Metacontext
import Parser
import Pretty
import Value
import Syntax

import qualified Presyntax as P
import DefinitionElaboration
import qualified Data.Map as M
import Data.IORef 
import Data.Char (isSpace)
import Definition (Def(DefFunc))
import Errors (TopLevelError(..))
import System.IO.Unsafe
import Elaboration


preludeSrc = unlines
  [ "data Nat where"
  , "| zero : Nat"
  , "| suc  : Nat -> Nat"

  , "data Id : {A : U} (x y : A) -> U where"
  , "| refl : {A : U} (x : A) -> Id x x"

  , "data Vec : (A : U) -> Nat -> U where"
  , "| vnil : {A : U} -> Vec A zero"
  , "| vcons : {A : U} {n : Nat} -> A -> Vec A n -> Vec A (suc n)"

  , "def add : Nat -> Nat -> Nat"
  , "| zero    n = n"
  , "| (suc m) n = suc (add m n)"

  , "def symm : {A : U} {x y : A} -> Id x y -> Id y x"
  , "| (refl x) = refl x"

  , "def trans : {A : U} {x : A} (y : A) {z : A} -> Id x y -> Id y z -> Id x z"
  , "| y (refl x) (refl x1) = refl x"

  , "def append : {A : U} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (add n m)"
  , "| vnil         ys = ys"
  , "| (vcons x xs) ys = vcons x (append xs ys)"

  , "def J : (A : U) (P : (x : A) (y : A) -> Id x y -> U)"
  , "    (m : (x : A) -> P x x (refl x))"
  , "    (a : A) (b : A) (p : Id a b) -> P a b p"
  , "| A P m a b (refl x) = m x"
  ]


preludeDefs :: Defs
preludeDefs = unsafePerformIO $ do
  prelude <- parseStringProgram "(Prelude)" preludeSrc
  fst <$> checkProg "prelude" (M.empty, emptyQITInfo) prelude

infixl 5 +>
(+>) :: Cxt -> (Name, Ty) -> Cxt
(+>) cxt (x, ty) = bind cxt x (evalCxt cxt ty)

initCxt = (emptyCxt (initialPos "Test")) { defs = preludeDefs }

-- `splitCxt` Test
-------------------


-- Split Nat 
cxtNat :: Cxt
cxtNat = initCxt 
  +> ("n", Call "Nat") 
  +> ("m", Call "Nat") 
  +> ("v", Call "Vec" `eApp` Call "Nat" `eApp` Var 1)

testSplitNat :: IO ()
testSplitNat = do
  putStrLn "Splitting the following context at level 0:"
  putStrLn (showCxt cxtNat)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtNat 0 of
    Nothing -> putStrLn "Failed to split cxtNat"
    Just splits -> putStrLn . unlines $ showCxt <$> splits

-- Split Vec
cxtVec1 :: Cxt 
cxtVec1 = initCxt 
  +> ("A", U) 
  +> ("n", Call "Nat") 
  +> ("v", Call "Vec" `eApp` Var 1 `eApp` Var 0) 

testSplitVec1 :: IO ()
testSplitVec1 = do
  putStrLn "Splitting the following context at level 2:"
  putStrLn (showCxt cxtVec1)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtVec1 2 of
    Nothing -> putStrLn "Failed to split cxtVec1"
    Just splits -> putStrLn . unlines $ showCxt <$> splits

cxtVec2 :: Cxt
cxtVec2 = initCxt 
  +> ("A", U) 
  +> ("v", Call "Vec" `eApp` Var 0 `eApp` Call "zero")

testSplitVec2 :: IO ()
testSplitVec2 = do
  putStrLn "Splitting the following context at level 1:"
  putStrLn (showCxt cxtVec2)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtVec2 1 of
    Nothing -> putStrLn "Failed to split cxtVec2"
    Just splits -> putStrLn . unlines $ showCxt <$> splits

cxtVec3 :: Cxt
cxtVec3 = initCxt 
  +> ("A", U) 
  +> ("n", Call "Nat") 
  +> ("v", Call "Vec" `eApp` Var 1 `eApp` (Call "suc" `eApp` Var 0))

testSplitVec3 :: IO ()
testSplitVec3 = do
  putStrLn "Splitting the following context at level 2:"
  putStrLn (showCxt cxtVec3)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtVec3 2 of
    Nothing -> putStrLn "Failed to split cxtVec3"
    Just splits -> putStrLn . unlines $ showCxt <$> splits

-- Split Id 

cxtId1 :: Cxt
cxtId1 = initCxt 
  +> ("A", U) 
  +> ("x", Var 0) 
  +> ("y", Var 0) 
  +> ("p", Call "Id" `iApp` Var 2 `eApp` Var 1 `eApp` Var 0)

testSplitId1 :: IO ()
testSplitId1 = do
  putStrLn "Splitting the following context at level 3:"
  putStrLn (showCxt cxtId1)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtId1 3 of
    Nothing -> putStrLn "Failed to split cxtId1"
    Just splits -> putStrLn . unlines $ showCxt <$> splits

cxtId2 :: Cxt
cxtId2 = initCxt
  +> ("A", U) 
  +> ("f", Pi "_" Expl (Var 0) (Var 1))
  +> ("g", Pi "_" Expl (Var 1) (Var 2))
  +> ("x", Var 2) 
  +> ("y", Var 3)
  +> ("p", Call "Id" `iApp` Var 4 `eApp` (Var 3 `eApp` Var 1) `eApp` (Var 2 `eApp` Var 0))

-- This should fail
testSplitId2 :: IO ()
testSplitId2 = do
  putStrLn "Splitting the following context at level 5:"
  putStrLn (showCxt cxtId2)
  putStrLn "\nResulting contexts:"
  case splitCxt cxtId2 5 of
    Nothing -> putStrLn "Failed to split cxtId2"
    Just splits -> putStrLn . unlines $ showCxt <$> splits
    
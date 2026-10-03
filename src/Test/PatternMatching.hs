module Test.PatternMatching where

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
import Elaboration

import qualified Presyntax as P
import DefinitionElaboration
import qualified Data.Map as M
import Data.IORef 
import Data.Char (isSpace)
import Definition (Def(DefFunc))
import Errors (TopLevelError(..))
import System.IO.Unsafe


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


-- TODO 
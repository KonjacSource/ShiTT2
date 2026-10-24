
module Main where

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
import Cxt.Type
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

  , "data False : U where"

  , "def the : (A : U) -> A -> A"
  , "| A x = x"

  , "data Sum : U -> U -> U where"
  , "| inl : {A B : U} -> A -> Sum A B"
  , "| inr : {A B : U} -> B -> Sum A B"

  , "data Ex : (A : U) -> (A -> U) -> U where"
  , "| ex : {A : U} {P : A -> U} (x : A) -> P x -> Ex A P"

  , "data Pair : (A B : U) -> U where"
  , "| pair : {A B : U} -> A -> B -> Pair A B"
  
  ]

--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-implicit-args [--help|nf|type|load]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type",
  "  load filepath : read & load a file"]

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw = do
  reset
  prelude <- parseStringProgram "(Prelude)" preludeSrc
  predefs <- checkProg preludeSrc M.empty emptyQITInfo prelude
  defsR <- newIORef predefs

  let elab = do
        (t, file) <- getRaw
        withGlobal' defsR $ do
          infer (emptyCxt (initialPos file)) t
            `catch` \e -> displayError file e >> throwIO e

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, a) <- elab
      withGlobal' defsR $ do
        putStrLn $ showTm0 $ nf [] t
        putStrLn "  :"
        putStrLn $ showTm0 $ quote 0 a
    ["type"] -> do
      (t, a) <- elab
      withGlobal' defsR $ do
        putStrLn "  :"
        putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, a) <- elab
      withGlobal' defsR $ do
        displayMetas
        putStrLn $ showTm0 t
    ["load", fp] -> do 
      src <- readFile fp 
      prog <- parseStringProgram fp src
      (defs, qiti) <- readIORef defsR
      (defs', qiti') <- checkProg src defs qiti prog
      writeIORef defsR (defs', qiti')
      done <- allSolved
      if done then 
        putStrLn $ "Successfully load " ++ fp
      else do
        putStrLn "Unsolved metas."
        withGlobal' defsR $ displayMetas
    ["load"] -> do 
      putStrLn "Expecting a file."
    ["repl"] -> repl' predefs
      
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

loadFile :: String -> IO ()
loadFile fp = mainWith (pure ["load", fp]) parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

repl :: IO () 
repl = do 
  reset
  prelude <- parseStringProgram "(Prelude)" preludeSrc
  predefs <- checkProg preludeSrc M.empty emptyQITInfo prelude
  defsR <- newIORef predefs
  repl' predefs


repl' :: (Defs, QITInfo) -> IO () 
repl' (ori_defs, qiti) = do
  reset
  prelude <- parseStringProgram "(Prelude)" preludeSrc
  predefs <- checkProg preludeSrc M.empty emptyQITInfo prelude
  defsR <- newIORef predefs

  loop defsR where

  elab defsR s = do
    t <- parseString s 
    withGlobal' defsR (infer (emptyCxt (initialPos s)) t)
      `catch` \e -> displayError s e >> throwIO TopLevelError

  loop defsR = do   
    putStr "repl> "
    cmd <- getLine
    case splitArgs cmd of 
      [":h"] -> do 
        putStrLn "Available commands:"
        putStrLn "  :h           - show this help message"
        putStrLn "  :q           - quit"
        putStrLn "  :l <file>    - load a file"
        putStrLn "  :r           - reset (not reload) to original definitions"
        putStrLn "  :metas       - display unsolved metas"
        putStrLn "  :meta <id>   - display meta with given id"
        putStrLn "  :func <name> - display function definition"
        putStrLn "  :t <expr>    - typecheck expression"
        putStrLn "  :nf <expr>   - typecheck expression and print its normal form"
        loop defsR
      ":t":(unwords -> expr) -> do
        (t, a) <- elab defsR expr
        withGlobal' defsR $ do
          putStrLn $ showTm0 $ quote 0 a
          loop defsR
      ":nf":(unwords -> expr)   -> do
        (t, a) <- elab defsR expr
        withGlobal' defsR $ do
          putStrLn $ showTm0 $ nf [] t
          putStrLn "  :"
          putStrLn $ showTm0 $ quote 0 a
          loop defsR
      [":q"] -> putStrLn "Bye!"
      [":l", fp] -> do
        src <- readFile fp 
        prog <- parseStringProgram fp src
        (defs, qiti) <- readIORef defsR
        state'@(defs', qiti') <- checkProg src defs qiti prog `catch` ((\e -> loop defsR >> exitSuccess) :: Error -> IO (Defs, QITInfo))
        writeIORef defsR state'
        done <- allSolved
        if done then 
          putStrLn $ "Successfully load " ++ fp
        else do
          putStrLn "Unsolved metas."
          withGlobal' defsR $ displayMetas
        loop defsR
      [":r"] -> do 
        writeIORef defsR (ori_defs, emptyQITInfo)
        loop defsR
      [":metas"] -> do
        withGlobal' defsR $ do
          displayMetas
        loop defsR
      [":meta", mid] -> do 
        withGlobal' defsR $ do
          mn <- readIO mid
          let m = lookupMeta $ MetaVar mn
          case m of 
            Unsolved -> putStrLn $ "Meta ?" ++ show mn ++ " is unsolved."
            Solved v -> putStrLn $ "Meta ?" ++ show mn ++ " = " ++ showTm0 (quote 0 v)
        loop defsR
      [":func", fname] -> do 
        -- print function definition
        withGlobal' defsR $ do
          case M.lookup fname ?defs of
            Just (DefFunc f) -> putStrLn $ showFunc f 
            _ -> putStrLn $ "Function " ++ fname ++ " not found."
        loop defsR
      _ -> do 
        putStrLn "Unknown command."
        loop defsR
    `catch` \TopLevelError -> loop defsR
 
ex2 :: IO ()
ex2 = main' "nf" $ unlines 
  [ "let v1 = vcons zero (vcons (suc zero) vnil);"
  , "let v2 = vcons (suc (suc zero)) (vcons zero vnil);"
  , "append v1 v2"
  ]

-- | from https://hackage-content.haskell.org/package/Cabal-3.16.0.0/docs/src/Distribution.Simple.Setup.Common.html#splitArgs
splitArgs :: String -> [String]
splitArgs = space []
  where
    space :: String -> String -> [String]
    space w [] = word w []
    space w (c : s)
      | isSpace c = word w (space [] s)
    space w ('"' : s) = string w s
    space w s = nonstring w s

    string :: String -> String -> [String]
    string w [] = word w []
    string w ('"' : s) = space w s
    string w ('\\' : '"' : s) = string ('"' : w) s
    string w (c : s) = string (c : w) s

    nonstring :: String -> String -> [String]
    nonstring w [] = word w []
    nonstring w ('"' : s) = string w s
    nonstring w (c : s) = space (c : w) s

    word [] s = s
    word w s = reverse w : s

testExamples :: IO ()
testExamples = do
  putStrLn "Running tests..."
  putStrLn ">> Loading Example.shitt..."
  loadFile "examples/Example.shitt" >> reset
  loadFile "examples/stlc.shitt" >> reset
  loadFile "examples/qit_test.shitt" >> reset
  loadFile "examples/qiit_stlc.shitt" >> reset
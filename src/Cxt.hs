module Cxt where

import Common
import Cxt.Type
import Evaluation
import Pretty
import Syntax
import Value
import qualified Data.Map as M
import Definition
import Control.Monad (join)
import Debug.Trace (trace)
import GHC.Stack
import qualified Data.Set as S

-- Elaboration context
--------------------------------------------------------------------------------

emptyQITInfo :: QITInfo
emptyQITInfo = QITInfo M.empty M.empty M.empty M.empty M.empty

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Source, a)) (bds :> Bound) pos

-- | Insert a new binding.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Inserted, a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, Source, a)) (bds :> Defined) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: HasGlobal => Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

-- Printing stuff
--------------------
cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _) -> x) . types

showVal :: HasGlobal => Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quoteCxt cxt v) []

showSp :: HasGlobal => Cxt -> Spine -> String
showSp cxt sp = join $ map (\(v, i) -> paren i (showVal cxt v)) (reverse sp) where
  paren Impl s = "{" ++ s ++ "} "
  paren Expl s = "(" ++ s ++ ") "

showTm :: HasCallStack => Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

showCxt :: HasGlobal => Cxt -> String
showCxt ctx@(Cxt values _ types _ _) = "\n" ++ go values types where 
  go [] [] = ""
  go (v:vs) ((x, ori, t):ts) = 
    go vs ts ++ "\n" ++

    x ++ " : " ++ showVal ctx (updateVal ctx t) ++ " := " ++
    showVal ctx (updateVal ctx v)
  go _ _ = error "impossible"
showFunc :: FuncDef -> String 
showFunc (FuncDef funcName fty cls) = "def " ++ funcName ++ " : " ++ showTm0 fty ++ join (map showCls cls) where 
  showCls (Clause ps rhs) = 
    "\n| " ++ join (map showPat ps) ++ "= " ++ prettyTm 0 (genNames ps) rhs [] 
  -- TODO : Make this better
  showPat (p, i) = paren i p where 
    paren Impl p = "{" ++ showPat' p ++ "} " 
    paren Expl p = "(" ++ showPat' p ++ ") "
    showPat' :: Pattern' Empty -> String
    showPat' (PatVar x) = x 
    showPat' (PatCon c ps) = c ++ " " ++ join (map showPat ps)
    showPat' (PatFunc f ps) = f ++ " " ++ join (map showPat ps)
  
  genNames :: PatternTele Empty -> [Name]
  genNames [] = [] 
  genNames (p:ps) = case fst p of 
    PatVar x -> genNames ps ++ [x]
    PatCon _ ps' -> genNames ps ++ genNames ps'
    PatFunc f ps' -> genNames ps ++ genNames ps'


instance Show Cxt where
  show = show . cxtNames
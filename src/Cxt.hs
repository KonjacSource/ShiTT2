
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

-- Elaboration context
--------------------------------------------------------------------------------

cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _) -> x) . types

showVal :: HasCallStack => Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quoteCxt cxt v) []

showTm :: HasCallStack => Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

showCxt :: Cxt -> String
showCxt ctx@(Cxt values _ types _ _ defs) = "\n" ++ go values types where 
  go [] [] = ""
  go (v:vs) ((x, ori, t):ts) = 
    go vs ts ++ "\n" ++

    x ++ " : " ++ showVal ctx (updateVal ctx t) ++ " := " ++
    showVal ctx (updateVal ctx v)

showFunc :: FuncDef -> String 
showFunc (FuncDef funcName fty cls) = "def " ++ funcName ++ " : " ++ showTm0 fty ++ join (map showCls cls) where 
  showCls (Clause ps rhs) = 
    "\n| " ++ join (map showPat ps) ++ "= " ++ prettyTm 0 (genNames ps) rhs [] 
  -- TODO : Make this better
  showPat (p, i) = paren i p where 
    paren Impl p = "{" ++ showPat' p ++ "} " 
    paren Expl p = "(" ++ showPat' p ++ ") "
    showPat' (PatVar x) = x 
    showPat' (PatCon c ps) = c ++ " " ++ join (map showPat ps)
  genNames [] = [] 
  genNames (p:ps) = case fst p of 
    PatVar x -> genNames ps ++ [x]
    PatCon _ ps' -> genNames ps ++ genNames ps'


instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt s = Cxt [] 0 [] [] s M.empty

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos defs) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Source, a)) (bds :> Bound) pos defs

-- | Insert a new binding.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l types bds pos defs) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Inserted, a)) (bds :> Bound) pos defs

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos defs) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, Source, a)) (bds :> Defined) pos defs 

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (defs cxt) (VVar (lvl cxt) : env cxt) (lvl cxt + 1) t)

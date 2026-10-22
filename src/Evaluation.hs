{-# LANGUAGE DeriveFunctor #-}

module Evaluation where

import Common
import Metacontext
import Syntax
import Value
import Cxt.Type
import Data.List (nub)
import Definition
import qualified Data.Map as M
import GHC.Stack (HasCallStack)
import Text.Printf (printf)
import Data.Bifunctor (Bifunctor(first))


data MatchResult a
  = MatchSuc Env   -- ^ Match succeeded
  | MatchStuck (MatchBlocker a)
  -- ^ Match stuck on a variable or function or unsolved meta, return the blocker info, this will be used in coverage checking.
  | MatchFailed    -- ^ c != c'
  deriving Functor

data MatchBlocker a
  = BVar Lvl a -- Stucking variable. Mark for QIT checking
  | BFunc FuncDef
  | BFlex MetaVar
  | BAbsurd  -- Stucking on an absurd term (nothing to do with absurd pattern)
  | BLamCase
  deriving Functor

-- | Note: Although pattern matching in this project always occurs at the top level,
-- | we may extend the system to add modules or inline `match` expressions.
match1 :: Defs -> Env -> Pattern -> Val -> MatchResult PatternWithMark
match1 defs env pat val = case (pat, val) of
  (PatVar x, v)             -> MatchSuc (v : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def   -> fmap (PatCon c) (match defs env ps args)
    | otherwise             -> MatchFailed
  (PatCon _ _, VAbsurd _)   -> MatchStuck BAbsurd
  (PatCon _ _, VRigid x _)  -> MatchStuck (BVar x (PatMark ()))
  (PatCon _ _, VFunc f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VFlex m _)   -> MatchStuck (BFlex m)
  (PatCon _ _, VU)          -> MatchFailed
  (PatCon _ _, VData _ _)   -> MatchFailed
  (PatCon _ _, VLam {})     -> MatchFailed
  (PatCon _ _, VPi {})      -> MatchFailed
  -- (PatCon _ _, VProp)       -> MatchFailed
  (PatCon _ _, VPropTm)     -> MatchFailed
  (PatCon _ _, VPrim _ _)   -> MatchFailed
  (PatCon _ _, VProj {})    -> MatchFailed
  (PatCon c ps, VPathCons p args) 
    | length ps == length args && c == eqNameDef p ->  fmap (PatCon c) (match defs env ps args)
  (PatCon c ps, VPathCons p args) -> MatchFailed 
  (PatFunc f ps, VFunc f' args)
    | length ps == length args && f == funcName f' -> fmap (PatFunc f) (match defs env ps args)
  (PatFunc f ps, VHold f' args)
    | length ps == length args && f == funcName f' -> fmap (PatFunc f) (match defs env ps args)
  (PatFunc f ps, _) -> MatchFailed -- for apd clause, we consider function names as codes 

match :: Defs -> Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
match defs env pats vals = go defs env pats (reverse vals) where
  go :: Defs -> Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
  go defs env [] [] = MatchSuc env
  go defs env pats@((p, i):ps) vals@(((force defs -> a, i'):as))
    | i == i' =
      case match1 defs env p a of
        MatchFailed -> MatchFailed
        MatchStuck l -> MatchStuck $ fmap (\ p -> (p, i) : map (first toPatternWithMark) ps) l
        MatchSuc env' -> fmap ((toPatternWithMark p, i) :) (go defs env' ps as)
  go _ _ ps vs = error $ "match: impossible\n when matching: " ++ show ps ++ " against " ++ show vs

infixl 8 $$
($$) :: HasCallStack => (Defs, Closure) -> Val -> Val
($$) (defs, Closure env t) u = eval defs (env :> u) t

vApp :: HasCallStack => Defs -> Val -> Val -> Icit -> Val
vApp defs t u i = case force defs t of
  VLam _ _ t  -> (defs, t) $$ u
  VFlex  m sp -> VFlex  m (sp :> (u, i))
  VRigid x sp     -> VRigid x (sp :> (u, i))
  -- env is used here,  when t is a meta solution, so that env = [], then t must be a closed term. so sp is empty too.
  VFunc f sp
    | length sp + 1 < arity f -> evalFun defs [] f (funcClauses f) (sp :> (u, i))
    | otherwise -> 
        let (rest, sp') = splitAt (length sp + 1 - arity f) (sp :> (u,i)) in
          vAppSp defs (evalFun defs [] f (funcClauses f) sp') rest
  VHold f sp -> VHold f (sp :> (u,i))
  VCons c sp -> VCons c (sp :> (u,i))
  VPathCons c sp -> VPathCons c (sp :> (u, i))
  VData d sp -> VData d (sp :> (u,i))
  VPrim Cast vs -> VPrim Cast (vs :> (u, i)) -- TODO: OTT computational rules
  VPrim p vs  -> VPrim p (vs :> (u, i))
  t           -> error $ "IMPOSSIBLE: " ++ show t

-- | Make sure `(length sp) <= arity f`
evalFun :: HasCallStack => Defs -> Env -> FuncDef -> [Clause] -> Spine -> Val
evalFun defs env f [] sp = VHold f sp -- No matchable clause yet.
evalFun defs env f (c:cs) sp
  | length sp < arity f = VFunc f sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match defs env (clausePatterns c) sp of
        MatchFailed -> evalFun defs env f cs sp --Failed
        MatchStuck _ -> VHold f sp       -- Stucked
        MatchSuc env' -> eval defs env' (clauseRhs c) -- Succeeded

-- Return Nothing if stucked or no matching clause
evalFun' :: HasCallStack => Defs -> Env -> FuncDef -> Spine -> Maybe Val
evalFun' defs env f sp = go (funcClauses f) where
  go [] = Nothing
  go (c:cs)
    | length sp < arity f = Nothing -- Wait
    | otherwise = -- `length sp == arity f`
        case match defs env (clausePatterns c) sp of
          MatchFailed -> go cs --Failed
          MatchStuck _ -> Nothing       -- Stucked
          MatchSuc env' -> Just $ eval defs env' (clauseRhs c) -- Succeeded

vAppSp :: Defs -> Val -> Spine -> Val
vAppSp defs t = \case
  []           -> t
  sp :> (u, i) -> vApp defs (vAppSp defs t sp) u i

vMeta :: HasCallStack => Env -> MetaVar -> Val
vMeta env m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: HasCallStack => Defs -> Env -> Val -> [BD] -> Val
vAppBDs defs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vApp defs (vAppBDs defs env v bds) t Expl
  (env :> t , bds :> Defined) -> vAppBDs defs env v bds
  _                           -> error "impossible"

eval :: HasCallStack => Defs -> Env -> Tm -> Val
eval defs env = \case
  Var x               -> env !! unIx x
  App t u i           -> vApp defs (eval defs env t) (eval defs env u) i
  Lam x i t           -> VLam x i (Closure env t)
  Pi x i a b          -> VPi x i (eval defs env a) (Closure env b)
  Let _ _ t u         -> eval defs (env :> eval defs env t) u
  U                   -> VU
  Absurd t            -> VAbsurd (eval defs env t)
  Meta m              -> vMeta env m
  InsertedMeta m bds  -> vAppBDs defs env (vMeta env m) bds
  Call f              -> case M.lookup f defs of
                          Just (DefFunc f)
                            | arity f == 0 && not (null $ funcClauses f) -> eval defs env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                            | otherwise -> VFunc f []
                          Just (DefData d) -> VData d []
                          Just (DefEq  eq) -> VPathCons eq []
                          Just (DefCons c) -> VCons c []
                          Nothing -> error $ "eval: impossible " ++ show f
  -- Prop                -> VProp
  PropTm              -> VPropTm
  Prim Cast           -> VPrim Cast []
  Prim p              -> VPrim p []
  Proj t x            -> VProj (eval defs env t) x []

evalCxt :: HasCallStack => Cxt -> Tm -> Val
evalCxt ctx = eval (defs ctx) (env ctx)

force :: Defs -> Val -> Val
force defs = \case
  VFlex m sp | Solved t <- lookupMeta m -> force defs (vAppSp defs t sp) -- t is in empty env
  t -> t

force' :: Cxt -> Val -> Val
force' = force . defs

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: Defs -> Lvl -> Tm -> Spine -> Tm
quoteSp defs l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp defs l t sp) (quote defs l u) i

quote :: HasCallStack => Defs -> Lvl -> Val -> Tm
quote defs l t = case force defs t of
  VFlex m sp -> quoteSp defs l (Meta m) sp
  VRigid x sp  -> quoteSp defs l (Var (lvl2Ix l x)) sp
  VLam x i t   -> Lam x i (quote defs (l + 1) ((defs, t) $$ VVar l))
  VPi x i a b  -> Pi x i (quote defs l a) (quote defs (l + 1) ((defs, b) $$ VVar l))
  VU           -> U
  VAbsurd v    -> Absurd (quote defs l v)

  VCons c sp   -> quoteSp defs l (Call (consName c)) sp
  VFunc f sp   -> quoteSp defs l (Call (funcName f)) sp
  VHold f sp   -> quoteSp defs l (Call (funcName f)) sp
  VData d sp   -> quoteSp defs l (Call (dataName d)) sp
  VPathCons f sp -> quoteSp defs l (Call (eqNameDef f)) sp
  -- VProp        -> Prop
  VPropTm      -> PropTm
  VPrim p sp   -> quoteSp defs l (Prim p) sp
  VProj v x sp -> quoteSp defs l (Proj (quote defs l v) x) sp

-- return the levels of bound variables introduced by the clause
countVarPat :: Lvl -> Clause -> (Int, [Lvl])
countVarPat (Lvl l) (Clause ps _) = (cnt ps, make (cnt ps)) where
  cnt :: [(Pattern, Icit)] -> Int
  cnt [] = 0
  cnt ((p, _):ps) = case p of
    PatVar _     -> 1 + cnt ps
    PatCon _ ps' -> cnt ps' + cnt ps
    PatFunc _ ps' -> cnt ps' + cnt ps
  make :: Int -> [Lvl]
  make 0 = []
  make n = Lvl (l + n - 1) : make (n - 1)

quoteCxt :: Cxt -> Val -> Tm
quoteCxt cxt = quote (defs cxt) (lvl cxt)

nf :: HasCallStack => Defs -> Env -> Tm -> Tm
nf defs env t = quote defs (Lvl (length env)) (eval defs env t)

fvSp :: Defs -> Lvl -> Spine -> [Lvl]
fvSp def dep = \case
  [] -> []
  ((v, _):vs) -> fv def dep v ++ fvSp def dep vs

fv :: Defs -> Lvl -> Val -> [Lvl]
fv def dep = nub . \case
  VFlex _ sp -> fvSp def dep sp
  VRigid l sp -> l : fvSp def dep sp
  VLam x _ b -> filter (< dep) $ fv def (dep + 1) ((def, b) $$ (VVar dep))
  VPi x _ t b -> fv def dep t ++ filter (< dep) (fv def (dep + 1) ((def, b) $$ (VVar dep)))
  VAbsurd v -> fv def dep v
  VCons _ sp -> fvSp def dep sp
  VFunc _ sp -> fvSp def dep sp
  VHold _ sp -> fvSp def dep sp
  VData _ sp -> fvSp def dep sp
  VPathCons _ sp -> fvSp def dep sp
  VU -> []
  VPrim _ sp -> fvSp def dep sp
  -- VProp -> []
  VPropTm -> error "fv: impossible"
  VProj v x sp -> fv def dep v ++ fvSp def dep sp
  -- fv is only used in PMunification case "x = t", if type of x is a prop, then x should be a prop term already.


-- dep is the old context depth, we will assign new levels to variables in pattern
p2v :: (Defs, QITInfo) -> Lvl -> Pattern -> Val
p2v (defs, qiti) dep = fst . go1 dep where

  go1 :: Lvl -> Pattern -> (Val, Lvl)
  go1 l = \case
    PatVar _ -> (VVar l, l+1)
    PatCon c ps -> case M.lookup c defs of
      Just (DefCons c) ->
        let (l', r) = go l ps in
          (VCons c l', r)
      Just (DefEq eq) -> 
        let (l', r) = go l ps in
          (VPathCons eq l', r)
      _ -> error "p2v: impossible"
    PatFunc f ps -> case M.lookup f defs of
      Just (DefFunc f) ->
        let (l', r) = go l ps in
          (vAppSp defs (VFunc f []) l', r)
      _ -> error "p2v: impossible"

  go :: Lvl -> [(Pattern, Icit)] -> (Spine, Lvl)
  go l [] = ([], l)
  go l ((p,i):ps) =
    let (p', l') = go1 l p
        (ps', l'') = go l' ps
    in (ps' ++ [(p', i)], l'')

updateVal :: Cxt -> Val -> Val
updateVal ctx = evalCxt ctx . quote (defs ctx) (lvl ctx)

updateSp :: Cxt -> Spine -> Spine
updateSp ctx = \case
  []           -> []
  sp :> (v, i) -> updateSp ctx sp :> (updateVal ctx v, i)

varr :: Cxt -> VTy -> VTy -> VTy
varr ctx a b = VPi "_" Expl a (Closure (env ctx) $ quote (defs ctx) (lvl ctx + 1) b)


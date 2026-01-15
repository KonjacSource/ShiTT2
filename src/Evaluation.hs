
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


data MatchResult
  = MatchSuc Env   -- ^ Match succeeded
  | MatchStuck MatchBlocker
  -- ^ Match stuck on a variable or function or unsolved meta, return the blocker info, this will be used in coverage checking.
  | MatchFailed    -- ^ c != c'

data MatchBlocker = BVar Lvl | BFunc FuncDef | BFlex MetaVar | BAbsurd | BLamCase

-- | Note: Although pattern matching in this project always occurs at the top level,
-- | we may extend the system to add modules or inline `match` expressions.
match1 :: Defs -> Env -> Pattern -> Val -> MatchResult
match1 defs env pat val = case (pat, val) of
  (PatVar x, v) -> MatchSuc (v : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def -> match defs env ps args
    | otherwise -> MatchFailed
  (PatCon _ _, VU)          -> MatchFailed
  (PatCon _ _, VData _ _)   -> MatchFailed
  (PatCon _ _, VLam {})     -> MatchFailed
  (PatCon _ _, VPi {})      -> MatchFailed
  (PatCon _ _, VAbsurd _)  -> MatchStuck BAbsurd
  (PatCon _ _, VLamCase {}) -> MatchStuck BLamCase
  (PatCon _ _, VLamCaseHold {}) -> MatchStuck BLamCase
  (PatCon _ _, VRigid x _)  -> MatchStuck (BVar x)
  (PatCon _ _, VFunc f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VFlex m _) -> MatchStuck (BFlex m)

match :: Defs -> Env -> [(Pattern, Icit)] -> Spine -> MatchResult
match defs env pats vals = go defs env pats (reverse vals) where
  go defs env [] [] = MatchSuc env
  go defs env pats@((p, i):ps) vals@(((force defs -> a, i'):as))
    | i == i' =
      case match1 defs env p a of
        MatchFailed -> MatchFailed
        MatchStuck l -> MatchStuck l
        MatchSuc env' -> go defs env' ps as
  go _ _ ps vs = error $ "match: impossible\n when matching: " ++ show ps ++ " against " ++ show vs

infixl 8 $$
($$) :: HasCallStack => (Defs, Closure) -> Val -> Val
($$) (defs, Closure env t) ~u = eval defs (env :> u) t

vApp :: HasCallStack => Defs -> Val -> Val -> Icit -> Val
vApp defs t ~u i = case force defs t of
  VLam _ _ t  -> (defs, t) $$ u
  VFlex  m sp -> VFlex  m (sp :> (u, i))
  VRigid x sp     -> VRigid x (sp :> (u, i))
  -- env is used here,  when t is a meta solution, so that env = [], then t must be a closed term. so sp is empty too.
  VFunc f sp
    | length sp + 1 < arity f -> evalFun defs [] f (funcClauses f) (sp :> (u, i))
    | otherwise -> let (sp', rest) = splitAt (arity f) (sp :> (u,i)) in
        vAppSp defs (evalFun defs [] f (funcClauses f) sp') rest
  VHold f sp -> VHold f (sp :> (u,i))
  VLamCase env cls sp
    | length sp + 1 < arity cls -> evalLamCase defs env cls (sp :> (u, i))
    | otherwise -> let (sp', rest) = splitAt (arity cls) (sp :> (u,i)) in
        vAppSp defs (evalLamCase defs env cls sp') rest
  VLamCaseHold env cls sp -> VLamCaseHold env cls (sp :> (u,i))
  VCons c sp -> VCons c (sp :> (u,i))
  VData d sp -> VData d (sp :> (u,i))
  t           -> error "IMPOSSIBLE"

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

-- TODO: refactor with evalFun
evalLamCase :: HasCallStack => Defs -> Env -> [Clause] -> Spine -> Val
evalLamCase defs env [] sp = VLamCaseHold env [] sp -- No matchable clause
evalLamCase defs env (c:cs) sp
  | length sp < arity (c:cs) = VLamCase env (c:cs) sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match defs env (clausePatterns c) sp of
        MatchFailed -> evalLamCase defs env cs sp --Failed
        MatchStuck _ -> VLamCaseHold env (c:cs) sp       -- Stucked
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

evalLamCase' :: HasCallStack => Defs -> Env -> [Clause] -> Spine -> Maybe Val
evalLamCase' defs env cls sp = go cls where
  go [] = Nothing
  go (c:cs)
    | length sp < arity cls = Nothing -- Wait
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
  Var x              -> env !! unIx x
  App t u i          -> vApp defs (eval defs env t) (eval defs env u) i
  Lam x i t          -> VLam x i (Closure env t)
  Pi x i a b         -> VPi x i (eval defs env a) (Closure env b)
  Let _ _ t u        -> eval defs (env :> eval defs env t) u
  U                  -> VU
  Absurd t           -> VAbsurd (eval defs env t)
  Meta m             -> vMeta env m
  InsertedMeta m bds -> vAppBDs defs env (vMeta env m) bds
  Call f             -> case M.lookup f defs of
                          Just (DefFunc f)
                            | arity f == 0 && not (null $ funcClauses f) -> eval defs env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                            | otherwise-> VFunc f []
                          Just (DefData d) -> VData d []
                          Just (DefCons c) -> VCons c []
                          Nothing -> error $ "eval: impossible " ++ show f
  LamCase clauses -> VLamCase env clauses []

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

quoteSp :: Defs -> Env -> Lvl -> Tm -> Spine -> Tm
quoteSp defs env l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp defs env l t sp) (quote defs env l u) i

quote :: HasCallStack => Defs -> Env -> Lvl -> Val -> Tm
quote defs env l t = case force defs t of
  VFlex m sp -> quoteSp defs env l (Meta m) sp
  VRigid x sp  -> quoteSp defs env l (Var (lvl2Ix l x)) sp
  VLam x i t   -> Lam x i (quote defs (VVar l : env) (l + 1) ((defs, t) $$ VVar l))
  VPi x i a b  -> Pi x i (quote defs env l a) (quote defs (VVar l : env) (l + 1) ((defs, b) $$ VVar l))
  VU           -> U
  VAbsurd v    -> Absurd (quote defs env l v)

  VLamCase     env cls sp -> LamCase (map (quoteClause defs env l) cls)
  VLamCaseHold env cls sp -> LamCase (map (quoteClause defs env l) cls)

  VCons c sp   -> quoteSp defs env l (Call (consName c)) sp
  VFunc f sp   -> quoteSp defs env l (Call (funcName f)) sp
  VHold f sp   -> quoteSp defs env l (Call (funcName f)) sp
  VData d sp   -> quoteSp defs env l (Call (dataName d)) sp

quoteClause :: Defs -> Env -> Lvl -> Clause -> Clause
quoteClause defs env l (Clause ps rhs) = Clause ps rhs' where
  (cnt, vls) = countVarPat l (Clause ps rhs)
  rhs' = quote defs (map VVar vls ++ env) (l + Lvl cnt) (eval defs (map VVar vls ++ env) rhs)

-- return the levels of bound variables introduced by the clause
countVarPat :: Lvl -> Clause -> (Int, [Lvl])
countVarPat (Lvl l) (Clause ps _) = (cnt ps, make (cnt ps)) where
  cnt :: [(Pattern, Icit)] -> Int
  cnt [] = 0
  cnt ((p, _):ps) = case p of
    PatVar _     -> 1 + cnt ps
    PatCon _ ps' -> cnt ps' + cnt ps
  make :: Int -> [Lvl]
  make 0 = []
  make n = Lvl (l + n - 1) : make (n - 1)

quoteCxt :: Cxt -> Val -> Tm
quoteCxt cxt = quote (defs cxt) (env cxt) (lvl cxt)

nf :: HasCallStack => Defs -> Env -> Tm -> Tm
nf defs env t = quote defs env (Lvl (length env)) (eval defs env t)

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
  VLamCase _ cls sp -> fvSp def dep sp ++ filter (< dep) (do
      c@(Clause ps rhs) <- cls
      let (cnt, vls) = countVarPat dep c
      fv def (dep + Lvl cnt) (eval def (map VVar vls) rhs))
  VLamCaseHold env cls sp -> fv def dep (VLamCase env cls sp)
  VCons _ sp -> fvSp def dep sp
  VFunc _ sp -> fvSp def dep sp
  VHold _ sp -> fvSp def dep sp
  VData _ sp -> fvSp def dep sp
  VU -> []

-- dep is the old context depth, we will assign new levels to variables in pattern
p2v :: Defs -> Lvl -> Pattern -> Val
p2v defs dep = fst . go1 dep where

  go1 :: Lvl -> Pattern -> (Val, Lvl)
  go1 l = \case
    PatVar _ -> (VVar l, l+1)
    PatCon c ps -> case M.lookup c defs of
      Just (DefCons c) ->
        let (l', r) = go l ps in
          (VCons c l', r)
      _ -> error "p2v: impossible"

  go :: Lvl -> [(Pattern, Icit)] -> (Spine, Lvl)
  go l [] = ([], l)
  go l ((p,i):ps) =
    let (p', l') = go1 l p
        (ps', l'') = go l' ps
    in (ps' ++ [(p', i)], l'')


updateVal :: Cxt -> Val -> Val
updateVal ctx = evalCxt ctx . quote (defs ctx) (env ctx) (lvl ctx)

updateSp :: Cxt -> Spine -> Spine
updateSp ctx = \case
  []           -> []
  sp :> (v, i) -> updateSp ctx sp :> (updateVal ctx v, i)

varr :: Cxt -> VTy -> VTy -> VTy
varr ctx a b = VPi "_" Expl a (Closure (env ctx) $ quote (defs ctx) (VVar (lvl ctx) : env ctx) (lvl ctx + 1) b)
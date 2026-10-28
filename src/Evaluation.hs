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
  = BVar Lvl a -- ^ Stucking variable. Mark for QIT checking
  | BFunc FuncDef
  | BFlex MetaVar
  | BAbsurd  -- ^ Stucking on an absurd term (nothing to do with absurd pattern)
  | BLamCase
  | BCast
  deriving Functor

-- | Note: Although pattern matching in this project always occurs at the top level,
-- | we may extend the system to add modules or inline `match` expressions.
match1 :: HasGlobal => Env -> Pattern -> Val -> MatchResult PatternWithMark
match1 env pat val = case (pat, val) of
  (PatVar x, v)             -> MatchSuc (v : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def   -> fmap (PatCon c) (match env ps args)
    | otherwise             -> MatchFailed
  (PatCon _ _, VAbsurd _)   -> MatchStuck BAbsurd
  (PatCon _ _, VRigid x _)  -> MatchStuck (BVar x (PatMark ()))
  (PatCon _ _, VFunc f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _ Nothing) -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _ (Just m)) -> MatchStuck (BFlex m)
  (PatCon _ _, VFlex m _)   -> MatchStuck (BFlex m)
  (PatCon _ _, VType)       -> error "impossible" 
  (PatCon _ _, VData _ _)   -> error "impossible"
  (PatCon _ _, VLam {})     -> error "impossible"
  (PatCon _ _, VPi {})      -> error "impossible"
  (PatCon _ _, VPropTm)     -> error "impossible"
  (PatCon _ _, VPrim Cast _) -> MatchStuck BCast 
  (PatCon _ _, VPrim Apd _)  -> error "impossible"
  (PatCon _ _, VPrim Oeq _)  -> error "impossible"
  (PatCon _ _, VPrim Rfl _)  -> error "impossible"
  (PatCon _ _, VProp)        -> error "impossible" 
  (PatCon _ _, VProj {})     -> undefined -- TODO: Should be a stuck
  (PatCon c ps, VPathCons p args) -- Lean's lesson: large elim over prop level values should not be allowed. 
                                  -- But here is ok, because the only way to match a path constructor is using `apd`, which is in prop verse.
    | length ps == length args && c == eqNameDef p ->  fmap (PatCon c) (match env ps args)
  (PatCon c ps, VPathCons p args) -> MatchFailed 
  (PatFunc f ps, VFunc f' args)
    | length ps == length args && f == funcName f' -> fmap (PatFunc f) (match env ps args)
  (PatFunc f ps, VHold f' args _)
    | length ps == length args && f == funcName f' -> fmap (PatFunc f) (match env ps args)
  (PatFunc f ps, _) -> MatchFailed -- for apd clause, we consider function names as codes 

match :: HasGlobal => Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
match env pats vals = go env pats (reverse vals) where
  go :: HasGlobal => Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
  go env [] [] = MatchSuc env
  go env pats@((p, i):ps) vals@(((force -> a, i'):as))
    | i == i' =
      case match1 env p a of
        MatchFailed -> MatchFailed
        MatchStuck l -> MatchStuck $ fmap (\ p -> (p, i) : map (first toPatternWithMark) ps) l
        MatchSuc env' -> fmap ((toPatternWithMark p, i) :) (go env' ps as)
  go _ ps vs = error $ "match: impossible\n when matching: " ++ show ps ++ " against " ++ show vs

infixl 8 $$
($$) :: HasGlobal => Closure -> Val -> Val
($$) (Closure env t) u = eval (env :> u) t

vApp :: HasGlobal => Val -> Val -> Icit -> Val
vApp t u i = case force t of
  VLam _ _ t  -> t $$ u
  VFlex  m sp -> VFlex  m (sp :> (u, i))
  VRigid x sp     -> VRigid x (sp :> (u, i))
  -- env is used here,  when t is a meta solution, so that env = [], then t must be a closed term. so sp is empty too.
  VFunc f sp
    | length sp + 1 < arity f -> evalFun [] f (funcClauses f) (sp :> (force u, i))
    | otherwise -> 
        let (rest, sp') = splitAt (length sp + 1 - arity f) (sp :> (force u,i)) in
          vAppSp (evalFun [] f (funcClauses f) sp') rest
  VHold f sp m -> VHold f (sp :> (u,i)) m
  VCons c sp -> VCons c (sp :> (u,i))
  VPathCons c sp -> VPathCons c (sp :> (u, i))
  VData d sp -> VData d (sp :> (u,i))
  VPrim Cast vs -> VPrim Cast (vs :> (u, i)) -- TODO: OTT computational rules
  VPrim p vs  -> VPrim p (vs :> (u, i))
  t           -> error $ "IMPOSSIBLE: " ++ show t

-- | Make sure `(length sp) <= arity f`
evalFun :: HasGlobal => Env -> FuncDef -> [Clause] -> Spine -> Val
evalFun env f [] sp = VHold f sp Nothing -- No matchable clause yet.
evalFun env f (c:cs) sp
  | length sp < arity f = VFunc f sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match env (clausePatterns c) sp of
        MatchFailed          -> evalFun env f cs sp --Failed
        MatchStuck (BFlex m) -> VHold f sp (Just m)       -- Stucked by a meta
        MatchStuck _         -> VHold f sp Nothing 
        MatchSuc env'        -> eval env' (clauseRhs c) -- Succeeded

-- Return Nothing if stucked or no matching clause
evalFun' :: HasGlobal => Env -> FuncDef -> Spine -> Maybe Val
evalFun' env f sp = go (funcClauses f) where
  go [] = Nothing
  go (c:cs)
    | length sp < arity f = Nothing -- Wait
    | otherwise = -- `length sp == arity f`
        case match env (clausePatterns c) sp of
          MatchFailed -> go cs --Failed
          MatchStuck _ -> Nothing       -- Stucked
          MatchSuc env' -> Just $ eval env' (clauseRhs c) -- Succeeded

vAppSp :: HasGlobal => Val -> Spine -> Val
vAppSp t = \case
  []           -> t
  sp :> (u, i) -> vApp (vAppSp t sp) u i

vMeta :: HasCallStack => Env -> MetaVar -> Val
vMeta env m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: HasGlobal => Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vApp (vAppBDs env v bds) t Expl
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"

-- TODO: adding rules for `f xxx (cast xx)`, as in cubical agda
eval :: HasGlobal => Env -> Tm -> Val
eval env = \case
  Var x               -> env !! unIx x
  App t u i           -> vApp (eval env t) (eval env u) i
  Lam x i t           -> VLam x i (Closure env t)
  Pi x i a b          -> VPi x i (eval env a) (Closure env b)
  Let _ _ t u         -> eval (env :> eval env t) u
  Type                   -> VType
  Absurd t            -> VAbsurd (eval env t)
  Meta m              -> vMeta env m
  InsertedMeta m bds  -> vAppBDs env (vMeta env m) bds
  Call f              -> case M.lookup f ?defs of
                          Just (DefFunc f)
                            | arity f == 0 && not (null $ funcClauses f) -> eval env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                            | otherwise -> VFunc f []
                          Just (DefData d) -> VData d []
                          Just (DefEq  eq) -> VPathCons eq []
                          Just (DefCons c) -> VCons c []
                          Nothing -> error $ "eval: impossible " ++ show f
  Prop                -> VProp
  PropTm              -> VPropTm
  Prim Cast           -> VPrim Cast []
  Prim p              -> VPrim p []
  Proj t x            -> VProj (eval env t) x []

evalCxt :: HasGlobal => Cxt -> Tm -> Val
evalCxt ctx = eval (env ctx)

force :: HasGlobal => Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp) -- t is in empty env
  VHold f sp (Just m)
    | Solved _ <- lookupMeta m -> vAppSp (VFunc f []) sp
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: HasGlobal => Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp l t sp) (quote l u) i

quote :: HasGlobal => Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp -> quoteSp l (Meta m) sp
  VRigid x sp  -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x i t   -> Lam x i (quote (l + 1) (t $$ VVar l))
  VPi x i a b  -> Pi x i (quote l a) (quote (l + 1) (b $$ VVar l))
  VType        -> Type
  VAbsurd v    -> Absurd (quote l v)

  VCons c sp   -> quoteSp l (Call (consName c)) sp
  VFunc f sp   -> quoteSp l (Call (funcName f)) sp
  VHold f sp _ -> quoteSp l (Call (funcName f)) sp
  VData d sp   -> quoteSp l (Call (dataName d)) sp
  VPathCons f sp -> quoteSp l (Call (eqNameDef f)) sp
  VProp        -> Prop
  VPropTm      -> PropTm
  VPrim p sp   -> quoteSp l (Prim p) sp
  VProj v x sp -> quoteSp l (Proj (quote l v) x) sp

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

quoteCxt :: HasGlobal => Cxt -> Val -> Tm
quoteCxt cxt = quote (lvl cxt)

nf :: HasGlobal => Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

fvSp :: HasGlobal => Lvl -> Spine -> [Lvl]
fvSp dep = \case
  [] -> []
  ((v, _):vs) -> fv dep v ++ fvSp dep vs

fv :: HasGlobal => Lvl -> Val -> [Lvl]
fv dep = nub . \case
  VFlex _ sp -> fvSp dep sp
  VRigid l sp -> l : fvSp dep sp
  VLam x _ b -> filter (< dep) $ fv (dep + 1) (b $$ VVar dep)
  VPi x _ t b -> fv dep t ++ filter (< dep) (fv (dep + 1) (b $$ VVar dep))
  VAbsurd v -> fv dep v
  VCons _ sp -> fvSp dep sp
  VFunc _ sp -> fvSp dep sp
  VHold _ sp _-> fvSp dep sp
  VData _ sp -> fvSp dep sp
  VPathCons _ sp -> fvSp dep sp
  VType -> []
  VPrim _ sp -> fvSp dep sp
  VProp -> []
  VPropTm -> error "fv: impossible"
  VProj v x sp -> fv dep v ++ fvSp dep sp
  -- fv is only used in PMunification case "x = t", if type of x is a prop, then x should be a prop term already.


-- dep is the old context depth, we will assign new levels to variables in pattern
p2v :: HasGlobal =>  Lvl -> Pattern -> Val
p2v dep = fst . go1 dep where

  go1 :: Lvl -> Pattern -> (Val, Lvl)
  go1 l = \case
    PatVar _ -> (VVar l, l+1)
    PatCon c ps -> case M.lookup c ?defs of
      Just (DefCons c) ->
        let (l', r) = go l ps in
          (VCons c l', r)
      Just (DefEq eq) -> 
        let (l', r) = go l ps in
          (VPathCons eq l', r)
      _ -> error "p2v: impossible"
    PatFunc f ps -> case M.lookup f ?defs of
      Just (DefFunc f) ->
        let (l', r) = go l ps in
          (vAppSp (VFunc f []) l', r)
      _ -> error "p2v: impossible"

  go :: Lvl -> [(Pattern, Icit)] -> (Spine, Lvl)
  go l [] = ([], l)
  go l ((p,i):ps) =
    let (p', l') = go1 l p
        (ps', l'') = go l' ps
    in (ps' ++ [(p', i)], l'')

updateVal :: HasGlobal => Cxt -> Val -> Val
updateVal ctx = evalCxt ctx . quote (lvl ctx)

updateSp :: HasGlobal => Cxt -> Spine -> Spine
updateSp ctx = \case
  []           -> []
  sp :> (v, i) -> updateSp ctx sp :> (updateVal ctx v, i)

varr :: HasGlobal => Cxt -> VTy -> VTy -> VTy
varr ctx a b = VPi "_" Expl a (Closure (env ctx) $ quote (lvl ctx + 1) b)


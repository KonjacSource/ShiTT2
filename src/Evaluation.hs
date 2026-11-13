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
import Data.Bifunctor 
import Data.Maybe
import {-# SOURCE #-} ObsEval


data MatchResult a
  = MatchSuc Env   -- ^ Match succeeded
  | MatchStuck (MatchBlocker a)
  -- ^ Match stuck on a variable or function or unsolved meta, return the blocker info, this will be used in coverage checking.
  | MatchFailed    -- ^ c != c'
  deriving Functor

data MatchBlocker a
  = BVar Lvl a -- ^ Stucking variable. Mark for QIT checking
  | BFunc FuncDef
  | BFlex [MetaVar]
  | BAbsurd  -- ^ Stucking on an absurd term (nothing to do with absurd pattern)
  | BLamCase
  | BCast
  | BProj
  deriving Functor

-- | Note: Although pattern matching in this project always occurs at the top level,
--   we may extend the system to add modules or inline `match` expressions.
match1 :: HasGlobal => Env -> Pattern -> Val -> MatchResult PatternWithMark
match1 env pat val = let val_wkfc = force' val in case (pat, force val_wkfc) of
  (PatVar x, v)                        -> MatchSuc (val_wkfc : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def              -> fmap (PatCon c) (match env ps args)
    | otherwise                        -> MatchFailed
  (PatCon _ _, VAbsurd _)              -> MatchStuck BAbsurd
  (PatCon _ _, VRigid x _)             -> MatchStuck (BVar x (PatMark ()))
  (PatCon _ _, VFunc f _)              -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _ (RBlocked m)) -> MatchStuck (BFlex m)
  (PatCon _ _, VHold f _ _)            -> MatchStuck (BFunc f)
  (PatCon _ _, VFlex m _)              -> MatchStuck (BFlex [m])
  (PatCon _ _, VData _ _)              -> error "impossible"
  (PatCon _ _, VLam {})                -> error "impossible"
  (PatCon _ _, VPi {})                 -> error "impossible"
  (PatCon _ _, VPropTm)                -> error "impossible"
  (PatCon _ _, VPrim Cast _ _)         -> MatchStuck BCast
  (PatCon _ _, VPrim Apd _ _)          -> error "impossible"
  (PatCon _ _, VPrim Oeq _ _)          -> error "impossible"
  (PatCon _ _, VPrim Rfl _ _)          -> error "impossible"
  (PatCon _ _, VSort _)                -> error "impossible"
  (PatCon _ _, VMkSig ts)              -> MatchFailed -- No tuple pattern
  (PatCon _ _, VSig {})                -> error "impossible"
  (PatCon _ _, VProj {})               -> MatchStuck BProj
  (PatCon c ps, VPathCons p args) -- Lean's lesson: large elim over prop level values should not be allowed. 
                                  -- But here is ok, because the only way to match a path constructor is using `apd`, which is in prop verse.
    | length ps == length args, c == eqNameDef p -> fmap (PatCon c) (match env ps args)
  (PatCon c ps, VPathCons p args)      -> MatchFailed
  (PatFunc f ps, VFunc f' args)
    | length ps == length args, f == funcName f' -> fmap (PatFunc f) (match env ps args)
  (PatFunc f ps, VHold f' args _)
    | length ps == length args, f == funcName f' -> fmap (PatFunc f) (match env ps args)
  (PatFunc f ps, _)                    -> MatchFailed -- for apd clause, we consider function names as codes 

match :: HasGlobal => Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
match env pats vals = go env pats (reverse vals) where
  go :: HasGlobal => Env -> [(Pattern, Icit)] -> Spine -> MatchResult (PatternTele ())
  go env [] [] = MatchSuc env
  go env pats@((p, i):ps) vals@(((force' -> a, i'):as))
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
  VLam _ _ t      -> t $$ u
  VFlex  m sp     -> VFlex  m (sp :> (u, i))
  VRigid x sp     -> VRigid x (sp :> (u, i))
  -- env is used here,  when t is a meta solution, so that env = [], then t must be a closed term. so sp is empty too.
  VFunc f sp
    | length sp + 1 < arity f -> evalFun [] f (funcClauses f) (sp :> (force' u, i))
    | otherwise   ->
        let (rest, sp') = splitAt (length sp + 1 - arity f) (sp :> (force' u,i)) in
          vAppSp (evalFun [] f (funcClauses f) sp') rest
  VHold f sp m    -> VHold f     (sp :> (u, i)) m
  VCons c sp      -> VCons c     (sp :> (u, i))
  VPathCons c sp  -> VPathCons c (sp :> (u, i))
  VData d sp      -> VData d     (sp :> (u, i))
  VProj v x sp    -> VProj v x   (sp :> (u, i))
  VPrim Cast sp _ -> mkPrim Cast (sp :> (u, i)) -- TODO: OTT computational rules
  VPrim Oeq  sp _ -> mkPrim Oeq  (sp :> (u, i)) -- Oeq is reduced lazily in force, see reduceOeq
  VPrim p sp r    -> VPrim p     (sp :> (u, i)) r
  VAbsurd v       -> VAbsurd v
  t               -> error $ "IMPOSSIBLE: " ++ show t
  where
    mkPrim p sp = VPrim p sp (reducePrim p sp)
    reducePrim :: HasGlobal => Prim -> Spine -> Reduced
    reducePrim Oeq sp@([]:>(a, Impl):>(t, Expl):>(u, Expl)) = case reduceOeq sp of
      Just r  -> RReduced r
      Nothing -> case blockers (force a) ++ blockers (force t) ++ blockers (force u) of
        [] -> RNeutral
        ms -> RBlocked ms
    reducePrim Cast sp@([]:>(a, CastIcit):>(b, CastIcit):>_:>_) = case reduceCast sp of
      Just r  -> RReduced r
      Nothing -> case blockers (force a) ++ blockers (force b) of
        [] -> RNeutral
        ms -> RBlocked ms
    reducePrim _ _ = RNeutral

-- | Make sure `(length sp) <= arity f`
evalFun :: HasGlobal => Env -> FuncDef -> [Clause] -> Spine -> Val
evalFun env f [] sp = VHold f sp RNeutral -- No matchable clause yet.
evalFun env f (c:cs) sp
  | length sp < arity f = VFunc f sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match env (clausePatterns c) sp of
        MatchFailed          -> evalFun env f cs sp --Failed
        MatchStuck (BFlex m) -> VHold f sp (RBlocked m)       -- Stucked by a meta
        MatchStuck _         -> VHold f sp RNeutral
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

class Eval a b | a -> b where 
  eval :: HasGlobal => Env -> a -> b

instance Eval Tm Val where 
  -- TODO: adding rules for `f xxx (cast xx)`, as in cubical agda
  eval env = \case
    Var x               -> env !! unIx x
    App t u i           -> vApp (eval env t) (eval env u) i
    Lam x i t           -> VLam x i (Closure env t)
    Pi x i a b          -> VPi x i (eval env a) (Closure env $ unEl b) (getSort b)
    Let _ _ t u         -> eval (env :> eval env t) u
    Absurd t            -> VAbsurd (eval env t)
    Meta m              -> vMeta env m
    InsertedMeta m bds  -> vAppBDs env (vMeta env m) bds
    Call f              -> case M.lookup f ?defs of
                            Just (DefFunc f)
                              | arity f == 0
                              , not (null $ funcClauses f) -> eval env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                              | otherwise -> VFunc f []
                            Just (DefData d) -> VData d []
                            Just (DefEq  eq) -> VPathCons eq []
                            Just (DefCons c) -> VCons c []
                            Nothing -> error $ "eval: impossible " ++ show f
    TmSort s            -> VSort s
    PropTm              -> VPropTm
    Prim Cast           -> VPrim Cast [] RNeutral
    Prim p              -> VPrim p [] RNeutral
    Sig tys             -> VSig env tys
    MkSig ts            -> VMkSig (map (second (eval env)) ts)
    Proj t x            -> vProj (eval env t) x

instance Eval Type VType where 
  eval env (El t s) = VEl (eval env t) s

vProj :: HasGlobal => Val -> Name -> Val
vProj (force -> VMkSig fs) x = go fs where
  go [] = error "impossible"
  go ((x', v):fs)
    | x == x'   = v
    | otherwise = go fs
vProj v x = VProj v x []

evalCxt :: (HasGlobal, Eval a b) => Cxt -> a -> b
evalCxt ctx = eval (env ctx)

-- Force is not free anymore, it is costly.
class Force c a | a -> c where 
  -- | Weak version of force, keeps the folded form of Oeq, Cast, and VHold.
  --   As force in cctt
  force' :: c => a -> a 
  -- | Fully force, as forceFull in cctt
  force :: c => a -> a

instance Force HasGlobal Val where
  force' v = case v of 
    VPrim Oeq sp (RBlocked m)
      | allSolved' m
      , Just r <- reduceOeq sp -> VPrim Oeq sp (RReduced r)
    VFlex m sp | Solved t <- lookupMeta m -> force' (vAppSp t sp) -- t is in empty env
    VHold f sp (RBlocked m)
      | allSolved' m -> VHold f sp . RReduced $ force (vAppSp (VFunc f []) sp)
    VProj v x sp -> case force v of
      VMkSig fs  -> force (vAppSp (fromJust $ lookup x fs) sp)
      VPropTm    -> VPropTm
      v'         -> VProj v' x sp
    v            -> v

  force v = case force' v of
    VPrim _ _ (RReduced v) -> force v
    VHold _ _ (RReduced v) -> force v
    v' -> v'
  
instance Force HasGlobal VType where 
  force' (VEl t s) = VEl (force' t) (force' s)
  force (VEl t s) = VEl (force t) (force s)

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: HasGlobal => Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []           -> t

  sp :> (u, i) -> App (quoteSp l t sp) (quote l u) i
quoteSpFull :: HasGlobal => Lvl -> Tm -> Spine -> Tm
quoteSpFull l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSpFull l t sp) (quoteFull l u) i

class Quote a b | a -> b where 
  quote :: HasGlobal => Lvl -> a -> b
  quoteFull :: HasGlobal => Lvl -> a -> b

instance Quote Val Tm where
  quote l t = case force' t of -- keep Oeq unreduced
    VFlex m sp     -> quoteSp l (Meta m) sp
    VRigid x sp    -> quoteSp l (Var (lvl2Ix l x)) sp
    VLam x i t     -> Lam x i (quote (l + 1) (t $$ VVar l))
    VPi x i a b bs -> Pi x i (quote l a) (El (quote (l + 1) (b $$ VVar l)) bs)
    VAbsurd v      -> Absurd (quote l v)
    VCons c sp     -> quoteSp l (Call (consName c)) sp
    VFunc f sp     -> quoteSp l (Call (funcName f)) sp
    VHold f sp _   -> quoteSp l (Call (funcName f)) sp
    VData d sp     -> quoteSp l (Call (dataName d)) sp
    VPathCons f sp -> quoteSp l (Call (eqNameDef f)) sp
    VSort s        -> TmSort s
    VPropTm        -> PropTm
    VPrim p sp r   -> quoteSp l (Prim p) sp
    VSig env tys   -> Sig $ quoteTele l env tys
    VMkSig ts      -> MkSig $ map (second (quoteFull l)) ts
    VProj v x sp   -> quoteSp l (Proj (quote l v) x) sp
  
  quoteFull l t = case force t of -- fully reduce Oeq, Cast, and VHold
    VFlex m sp     -> quoteSpFull l (Meta m) sp
    VRigid x sp    -> quoteSpFull l (Var (lvl2Ix l x)) sp
    VLam x i t     -> Lam x i (quoteFull (l + 1) (t $$ VVar l))
    VPi x i a b bs -> Pi x i  (quoteFull l a) (El (quoteFull (l + 1) (b $$ VVar l)) bs)
    VAbsurd v      -> Absurd  (quoteFull l v)
    VCons c sp     -> quoteSpFull l (Call (consName c)) sp
    VFunc f sp     -> quoteSpFull l (Call (funcName f)) sp
    VHold f sp _   -> quoteSpFull l (Call (funcName f)) sp
    VData d sp     -> quoteSpFull l (Call (dataName d)) sp
    VPathCons f sp -> quoteSpFull l (Call (eqNameDef f)) sp
    VSort s        -> TmSort s
    VPropTm        -> PropTm
    VPrim p sp r   -> quoteSpFull l (Prim p) sp
    VSig env tys   -> Sig $ quoteTele l env tys
    VMkSig ts      -> MkSig $ map (second (quoteFull l)) ts
    VProj v x sp   -> quoteSpFull l (Proj (quoteFull l v) x) sp

instance Quote VType Type where
  quote l (VEl t s) = El (quote l t) s
  quoteFull l (VEl t s) = El (quoteFull l t) (force s)

quoteTele :: HasGlobal => Lvl -> Env -> Telescope' -> Telescope'
quoteTele l env = \case
  [] -> []
  (x, t):ts -> (x, quote l (eval env t)) : quoteTele (l + 1) (VVar l : env) ts

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

class Nf a where 
  nf :: HasGlobal => Env -> a -> a

instance Nf Tm  where
  nf env t = quote (Lvl (length env)) (eval env t)

instance Nf Type where 
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
  VPi x _ (VEl t _) b bs -> fv dep t ++ filter (< dep) (fv (dep + 1) (b $$ VVar dep))
  VAbsurd v -> fv dep v
  VCons _ sp -> fvSp dep sp
  VFunc _ sp -> fvSp dep sp
  VHold _ sp _-> fvSp dep sp
  VData _ sp -> fvSp dep sp
  VPathCons _ sp -> fvSp dep sp
  VPrim _ sp _ -> fvSp dep sp
  VSort _ -> []
  VPropTm -> error "fv: impossible"
  VSig env tys -> fvTele dep env tys
  VMkSig ts -> concatMap (fv dep . snd) ts
  VProj v x sp -> fv dep v ++ fvSp dep sp
  -- fv is only used in PMunification case "x = t", if type of x is a prop, then x should be a prop term already.

fvTele :: HasGlobal => Lvl -> Env -> Telescope' -> [Lvl]
fvTele dep env = \case
  [] -> []
  (x, t):ts -> fv dep (unVEl $ eval env t) ++ fvTele (dep + 1) (env :> VVar dep) ts


-- dep is the old context depth, we will assign new levels to variables in pattern
p2v :: HasGlobal =>  Lvl -> Pattern -> Val
p2v dep = fst . go1 dep where

  go1 :: Lvl -> Pattern -> (Val, Lvl)
  go1 l = \case
    PatVar _           -> (VVar l, l+1)
    PatCon c ps        -> case M.lookup c ?defs of
      Just (DefCons c) -> (VCons c l', r)             where (l', r) = go l ps 
      Just (DefEq eq)  -> (VPathCons eq l', r)        where (l', r) = go l ps
      _                -> error "p2v: impossible"
    PatFunc f ps       -> case M.lookup f ?defs of
      Just (DefFunc f) -> (vAppSp (VFunc f []) l', r) where (l', r) = go l ps
      _                -> error "p2v: impossible"

  go :: Lvl -> [(Pattern, Icit)] -> (Spine, Lvl)
  go l [] = ([], l)
  go l ((p,i):ps) = (ps' ++ [(p', i)], l'') where
    (p', l') = go1 l p
    (ps', l'') = go l' ps

updateVal :: HasGlobal => Cxt -> Val -> Val
updateVal ctx = evalCxt ctx . quote (lvl ctx)

updateSp :: HasGlobal => Cxt -> Spine -> Spine
updateSp ctx = \case
  []           -> []
  sp :> (v, i) -> updateSp ctx sp :> (updateVal ctx v, i)

instance Force () Sort where 
  force' = force
  force = \case 
    SMeta m | SSolved s <- lookupSMeta m -> s
            | otherwise -> SMeta m
    IMax s s' -> imax (force s) (force s')
    UMax ss   -> umax (map force ss)
    SType     -> SType
    SProp     -> SProp
    Suc s     -> suc s

suc :: Sort -> Sort
suc s = case force s of
  SType -> SType
  SProp -> SType
  s     -> Suc s

imax :: Sort -> Sort -> Sort
imax a b = case (force a, force b) of
  (SType, SType) -> SType
  (SProp, SType) -> SType
  (_    , SProp) -> SProp
  (s    , s'   ) -> IMax s s'

umax1 :: Sort -> Sort -> Sort
umax1 a b = case (force a, force b) of
  (SType, SType) -> SType
  (SProp, SType) -> SType
  (SType, SProp) -> SType
  (SProp, SProp) -> SProp
  (UMax ss, s)   -> UMax (s:ss)
  (s, UMax ss)   -> UMax (s:ss)
  (s    , s'   ) -> UMax [s, s']

umax :: [Sort] -> Sort
umax = foldr umax1 SProp

mkPi :: Telescope -> Type -> Type
mkPi [] t = t
mkPi ((x, i, a):ts) t = El (Pi x i a (El b bs)) s where
  El b bs = mkPi ts t
  s = imax (getSort a) bs
  
mkPiE :: Telescope' -> Type -> Type
mkPiE ts = mkPi [(x, Expl, a) | (x, a) <- ts]

instance SortOf Telescope' where
  sortOf [] = SProp
  sortOf ((_, t):ts) = umax1 (sortOf t) (sortOf ts)

instance SortOf Sort where 
  sortOf = suc

instance Zonk Tm where 
  zonk = \case 
    Var x               -> Var x
    Call f              -> Call f
    Lam x i t           -> Lam x i (zonk t)
    App t u i           -> App (zonk t) (zonk u) i
    Absurd t            -> Absurd (zonk t)
    Pi x i a b          -> Pi x i (zonk a) (zonk b)
    Let x a t u         -> Let x (zonk a) (zonk t) (zonk u)
    Meta m              -> case lookupMeta m of 
      Solved v          -> zonk $ quote 0 v
      Unsolved          -> Meta m
    InsertedMeta m bds  -> case lookupMeta m of
      Solved v          -> let l     = length bds
                               idEnv = [ VVar (Lvl k) | k <- [l - 1, l - 2 .. 0] ]
                           in zonk $ quote (Lvl l) (vAppBDs idEnv v bds)
      Unsolved          -> InsertedMeta m bds
    TmSort s            -> TmSort s
    PropTm              -> PropTm
    Prim p              -> Prim p
    Proj t x            -> Proj (zonk t) x
    Sig ts              -> Sig [(x, zonk a) | (x, a) <- ts]
    MkSig ts            -> MkSig [(x, zonk t) | (x, t) <- ts]

instance Zonk Type where 
  zonk (El t s) = El (zonk t) (zonk s)

instance Zonk Sort where 
  zonk = \case 
    SMeta m     -> case lookupSMeta m of 
      SSolved s -> zonk s
      SUnsolved -> SMeta m
    IMax s s'   -> IMax (zonk s) (zonk s')
    UMax ss     -> UMax (map zonk ss)
    SType       -> SType
    SProp       -> SProp
    Suc s       -> Suc (zonk s)

zonkSp :: HasGlobal => Spine -> Spine
zonkSp = \case
  [] -> []
  sp :> (v, i) -> zonkSp sp :> (zonk v, i)

-- | Zonking a closure needs no level: zonk the captured values and the body term.
zonkCls :: HasGlobal => Closure -> Closure
zonkCls (Closure env t) = Closure (map zonk env) (zonk t)

instance Zonk Val where
  zonk v = case force' v of
    VFlex m sp      -> VFlex m (zonkSp sp)
    VRigid x sp     -> VRigid x (zonkSp sp)
    VLam x i t      -> VLam x i (zonkCls t)
    VPi x i a b bs  -> VPi x i (zonk a) (zonkCls b) (zonk bs)
    VAbsurd v       -> VAbsurd (zonk v)
    VCons c sp      -> VCons c (zonkSp sp)
    VFunc f sp      -> VFunc f (zonkSp sp)
    VHold f sp m    -> VHold f (zonkSp sp) m
    VData d sp      -> VData d (zonkSp sp)
    VPathCons f sp  -> VPathCons f (zonkSp sp)
    VPrim p sp r    -> VPrim p (zonkSp sp) r
    VSig env ts     -> VSig (map zonk env) [(x, zonk t) | (x, t) <- ts]
    VMkSig ts       -> VMkSig [(x, zonk t) | (x, t) <- ts]
    VProj v x sp    -> VProj (zonk v) x (zonkSp sp)
    VSort s         -> VSort (zonk s)
    VPropTm         -> VPropTm

instance Zonk VType where 
  zonk (VEl t s) = VEl (zonk t) (zonk s)

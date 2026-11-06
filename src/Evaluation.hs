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
  | BProj
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
  (PatCon _ _, VData _ _)   -> error "impossible"
  (PatCon _ _, VLam {})     -> error "impossible"
  (PatCon _ _, VPi {})      -> error "impossible"
  (PatCon _ _, VPropTm)     -> error "impossible"
  (PatCon _ _, VPrim Cast _) -> MatchStuck BCast
  (PatCon _ _, VPrim Apd _)  -> error "impossible"
  (PatCon _ _, VPrim Oeq _)  -> error "impossible"
  (PatCon _ _, VPrim Rfl _)  -> error "impossible"
  (PatCon _ _, VSort _)       -> error "impossible"
  (PatCon _ _, VMkSig ts)    -> MatchFailed -- No tuple pattern
  (PatCon _ _, VSig {})      -> error "impossible"
  (PatCon _ _, VProj {})     -> MatchStuck BProj
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
  VLam _ _ t     -> t $$ u
  VFlex  m sp    -> VFlex  m (sp :> (u, i))
  VRigid x sp    -> VRigid x (sp :> (u, i))
  -- env is used here,  when t is a meta solution, so that env = [], then t must be a closed term. so sp is empty too.
  VFunc f sp
    | length sp + 1 < arity f -> evalFun [] f (funcClauses f) (sp :> (force u, i))
    | otherwise ->
        let (rest, sp') = splitAt (length sp + 1 - arity f) (sp :> (force u,i)) in
          vAppSp (evalFun [] f (funcClauses f) sp') rest
  VHold f sp m   -> VHold f (sp :> (u,i)) m
  VCons c sp     -> VCons c (sp :> (u,i))
  VPathCons c sp -> VPathCons c (sp :> (u, i))
  VData d sp     -> VData d (sp :> (u,i))
  VProj v x sp   -> VProj v x (sp :> (u, i))
  VPrim Cast vs  -> VPrim Cast (vs :> (u, i)) -- TODO: OTT computational rules
  VPrim Oeq  vs  -> vOeq (vs :> (u, i))
  VPrim p vs     -> VPrim p (vs :> (u, i))
  VAbsurd v      -> VAbsurd v
  t              -> error $ "IMPOSSIBLE: " ++ show t

vOeq :: HasGlobal => Spine -> Val
vOeq ([]:>(a, Impl):>(t, Expl):>(u, Expl)) = case (force a, force t, force u) of 
  (a, t, u) -> VPrim Oeq ([]:>(a, Impl):>(t, Expl):>(u, Expl))
vOeq vs = VPrim Oeq vs

-- | Generating a sigma type, recording the equality between two telescopes.
-- | Δ1 = (x_0 : A_0) (x_1 : A_1[x_0]) ... (x_(n-1) : A_(n-1)[x_<(n-1)])
-- | Δ2 = (x_0 : B_0) (x_1 : B_1[x_0]) ... (x_(n-1) : B_(n-1)[x_<(n-1)])     -- field names must agree
-- | we get
--   sig
--   { x_0 : A_0 ~{s_0} B_0
--   ; x_1 : (x_0 : A_0) -> A_1[x_0] ~{s_1} B_1[y_0]
--   ; x_2 : (x_0 : A_0) (x_1 : A_1[x_0]) -> A_2[x_0, x_1] ~{s_2} B_2[y_0, y_1]
--   ...}
--   where s_j is the sort of both A_j and B_j, f_j is the j-th field of this sig, and
--     y_j = cast {A_j[x_<j]} {B_j[y_<j]} (f_j x_<j) x_j   if s_j = Type
--     y_j = ..                                              if s_j = Prop  (cast for prop is postulated)
--   Each y_j is bound once by a `let` in front of the equation, so the field types stay linear in size.
-- | Nothing if it does not reduce: the field names differ, or some field sorts are not solved yet or differ.
oeqTeleTy :: HasGlobal => (Env, Telescope') -> (Env, Telescope') -> Maybe VTy
oeqTeleTy (envA, as) (envB, bs)
  | fieldNames == map fst bs
  , and [ known s && s == s' | (s, s') <- fieldSorts ] = Just $ VSig famEnv [ (x, eqField k) | (k, x) <- zip [0 ..] fieldNames ]
  | otherwise = Nothing
  where
    n          = length as
    fieldNames = map fst as
    -- the sorts of the j-th fields of Δ1 and Δ2
    fieldSorts = zipWith (\(_, a) (_, b) -> (force (getSort a), force (getSort b))) as bs
    -- TODO: If there is meta in s, we may get a stucked result, and would not be able to re-compute when the meta is solved. 
    known s    = s == SType || s == SProp
    -- s_j, only used when all the field sorts are known and agree
    fieldSort j = fst (fieldSorts !! j)
    -- env ⊢ tys  ==>  env ⊢ λ x_0 .. x_(j-1). A_j  (the j-th field type as a function of the previous fields)
    fieldFamily :: Env -> Telescope' -> Int -> Val
    fieldFamily env tys j = eval env $ foldr (\x -> Lam x Expl) (unEl (snd (tys !! j))) (map fst (take j tys))
    -- Θ; G_j has local level j, H_j has local level n + j
    famEnv = reverse $ [ fieldFamily envA as j | j <- [0 .. n - 1] ]
                    ++ [ fieldFamily envB bs j | j <- [0 .. n - 1] ]
    -- At depth `depth`, the variable of local level `l`
    varAt :: Int -> Int -> Tm
    varAt depth l = Var (Ix (depth - l - 1))

    mkOeq s a b = applySp (Prim Oeq) [(TmSort s, Impl), (a, Expl), (b, Expl)]

    -- Θ, f_0 .. f_(k-1) ⊢ eqField k
    --   = (x_0 : A_0) .. (x_(k-1) : A_(k-1)[x_<(k-1)]) -> let y_0 = ..; ..; let y_(k-1) = ..; A_k[x_<k] ~{s_k} B_k[y_<k]
    -- Local levels: G_j = j, H_j = n + j, f_j = 2n + j, x_j = 2n + k + j, y_j = 2n + 2k + j
    eqField :: Int -> Type
    eqField k = mkPiE [ (fieldNames !! j, El (tyA (lvlX j) j) (fieldSort j)) | j <- [0 .. k - 1] ]
                      (El (letYs 0) SProp)
      where
        lvlF j = 2 * n + j
        lvlX j = 2 * n + k + j
        lvlY j = 2 * n + 2 * k + j
        -- At depth d:  G_j x_<j = A_j[x_<j],  H_j y_<j = B_j[y_<j],  f_j x_<j : A_j[x_<j] ~ B_j[y_<j]
        tyA   d j = applySp (varAt d j)        [ (varAt d (lvlX i), Expl) | i <- [0 .. j - 1] ]
        tyB   d j = applySp (varAt d (n + j))  [ (varAt d (lvlY i), Expl) | i <- [0 .. j - 1] ]
        proof d j = applySp (varAt d (lvlF j)) [ (varAt d (lvlX i), Expl) | i <- [0 .. j - 1] ]
        -- Θ, f_<k, x_<k, y_<j ⊢ letYs j   (at depth lvlY j)
        letYs j
          | j == k    = mkOeq (fieldSort k) (tyA d k) (tyB d k)
          | otherwise = Let (fieldNames !! j ++ "'") (El (tyB d j) (fieldSort j)) (castX d j) (letYs (j + 1))
          where d = lvlY j
        -- At depth d: y_j
        castX d j
          | fieldSort j == SProp = PropTm
          | otherwise            = applySp (Prim Cast) [ (tyA d j, casticit), (tyB d j, casticit)
                                                       , (proof d j, Expl), (varAt d (lvlX j), Expl) ]


wkTm :: HasGlobal => Env -> Lvl -> Lvl -> Tm -> Tm
wkTm env l n t = quote (l + n) (eval env t)

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
                              | arity f == 0 && not (null $ funcClauses f) -> eval env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                              | otherwise -> VFunc f []
                            Just (DefData d) -> VData d []
                            Just (DefEq  eq) -> VPathCons eq []
                            Just (DefCons c) -> VCons c []
                            Nothing -> error $ "eval: impossible " ++ show f
    TmSort s            -> VSort s
    PropTm              -> VPropTm
    Prim Cast           -> VPrim Cast []
    Prim p              -> VPrim p []
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

class Force c a | a -> c where 
  force :: c => a -> a

instance Force HasGlobal Val where
  force = \case
    VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp) -- t is in empty env
    VHold f sp (Just m)
      | Solved _ <- lookupMeta m -> vAppSp (VFunc f []) sp
    VProj v x sp -> case force v of
      VMkSig fs -> force (vAppSp (fromJust $ lookup x fs) sp)
      VPropTm   -> VPropTm
      v'        -> VProj v' x sp
    t -> t
  
instance Force HasGlobal VType where 
  force (VEl t s) = VEl (force t) (force s)

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: HasGlobal => Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp l t sp) (quote l u) i

class Quote a b | a -> b where 
  quote :: HasGlobal => Lvl -> a -> b

instance Quote Val Tm where
  quote l t = case force t of
    VFlex m sp -> quoteSp l (Meta m) sp
    VRigid x sp  -> quoteSp l (Var (lvl2Ix l x)) sp
    VLam x i t   -> Lam x i (quote (l + 1) (t $$ VVar l))
    VPi x i a b bs -> Pi x i (quote l a) (El (quote (l + 1) (b $$ VVar l)) bs)
    VAbsurd v    -> Absurd (quote l v)

    VCons c sp   -> quoteSp l (Call (consName c)) sp
    VFunc f sp   -> quoteSp l (Call (funcName f)) sp
    VHold f sp _ -> quoteSp l (Call (funcName f)) sp
    VData d sp   -> quoteSp l (Call (dataName d)) sp
    VPathCons f sp -> quoteSp l (Call (eqNameDef f)) sp
    VSort s      -> TmSort s
    VPropTm      -> PropTm
    VPrim p sp   -> quoteSp l (Prim p) sp
    VSig env tys -> Sig $ quoteTele l env tys
    VMkSig ts    -> MkSig $ map (second (quote l)) ts
    VProj v x sp -> quoteSp l (Proj (quote l v) x) sp

instance Quote VType Type where
  quote l (VEl t s) = El (quote l t) s

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
  VPrim _ sp -> fvSp dep sp
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

instance Force () Sort where 
  force = \case 
    SMeta m | SSolved s <- lookupSMeta m -> s
            | otherwise -> SMeta m
    IMax s s' -> imax (force s) (force s')
    UMax ss   -> umax (map force ss)
    SType -> SType
    SProp -> SProp
    Suc s -> suc s

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
  (UMax ss, s) -> UMax (s:ss)
  (s, UMax ss) -> UMax (s:ss)
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
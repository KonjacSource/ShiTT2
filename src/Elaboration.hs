module Elaboration
  (check, infer, unifyCatch, findType, checkPat, updateCxt, checkCover,
  CoverCheckingError(..), MissingPattern, splitCxt, checkCls, reportOpnCls, checkApdCover) where

import Control.Exception
import Control.Monad
import Data.IORef

import qualified Data.IntMap as IM
import qualified Data.Set as S
import Common
import Cxt
import Cxt.Type
import Errors
import Evaluation
import Metacontext
import Syntax
import qualified Unification as U
import Value

import qualified Presyntax as R
import Definition
import qualified Data.Map as M
import GHC.Stack (HasCallStack)
import Data.Maybe (isJust, fromJust)
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)

import Text.Megaparsec (parse)
import Parser

-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

unifyCatch :: HasGlobal => Cxt -> VTy -> Val -> Val -> IO ()
unifyCatch cxt a t t' =
  U.unifyCxt cxt a t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quoteCxt cxt t) (quoteCxt cxt t')

-- | Insert fresh implicit applications.
insert' :: HasGlobal => Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act where
  go (t, va) = case force va of
    VPi x Impl a b -> do
      m <- freshMeta cxt
      let mv = evalCxt cxt m
      go (App t m Impl, b $$ mv)
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: HasGlobal => Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _), va) -> pure (t, va)
  (t               , va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: HasGlobal => Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act where
  go (t, va) = case force va of
    va@(VPi x Impl a b) -> do
      if x == name then
        pure (t, va)
      else do
        m <- freshMeta cxt
        let mv = evalCxt cxt m
        go (App t m Impl, b $$ mv)
    _ ->
      throwIO $ Error cxt $ NoNamedImplicitArg name

check :: HasGlobal => Cxt -> R.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of

  (R.PrintCxt t, a) -> do
    putStrLn (showCxt cxt)
    putStrLn (replicate 80 '-')
    -- NOTE. there might be some unsolved metas in the @a@ which can be solved soon after the check. 
    -- But the printing here still contains the unsolved metas.
    putStrLn $ showVal cxt a ++ "\n\n"
    check cxt t a

  (R.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a

  -- If the icitness of the lambda matches the Pi type, check as usual
  (R.Lam x i t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') i -> do
    Lam x i' <$> check (bind cxt x a) t (b $$ VVar (lvl cxt))

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x Impl a b) -> do
    Lam x Impl <$> check (newBinder cxt x a) t (b $$ VVar (lvl cxt))

  -- See https://github.com/KonjacSource/ShiTT2/issues/1
  -- (t, a@(VData d sp)) | Just (c, sp) <- (trace ("| checking data: " ++ dataName d) $ isCons t) -> do 
  --   putStrLn $ "Checking constructor " ++ consName c ++ " against type " ++ showVal cxt a
  --   checkCons c sp (evalCxt cxt (consType c)) a

  (R.Let x a t u, a') -> do
    a <- check cxt a VType
    let va = evalCxt cxt a
    t <- check cxt t va
    let vt = evalCxt cxt t
    u <- check (define cxt x vt va) u a'
    pure (Let x a t u)

  (R.Absurd t, ty) -> do
    (t, t_ty) <- infer cxt t
    let cxt' = bind cxt "_absurd" t_ty
    case splitCxt cxt' (lvl cxt' - 1) of
      Just [] -> pure $ Absurd t
      Just ctxs -> do
        putStrLn "Absurd context:"
        mapM_ (putStrLn . showCxt) ctxs
        throwIO $ Error cxt $ NotAbsurd (quoteCxt cxt t_ty)
      Nothing -> throwIO $ Error cxt $ NotAbsurd (quoteCxt cxt t_ty)

  (R.Hole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt VType expected inferred
    pure t

infer :: HasGlobal => Cxt -> R.Tm -> IO (Tm, VTy)
infer cxt = \case

  R.PrintCxt t -> do
    putStrLn "printing context"
    putStrLn (showCxt cxt)
    infer cxt t

  R.SrcPos pos t ->
    infer (cxt {pos = pos}) t

  R.Var x -> do
    let go ix (types :> (x', origin, a))
          | x == x' && origin == Source = pure (Var ix, a)
          | otherwise                   = go (ix + 1) types
        go ix [] = case M.lookup x ?defs of
          Just (DefFunc c) -> pure (Call x, eval (env cxt) (funcType c))
          Just (DefCons c) -> pure (Call x, eval (env cxt) (consType c))
          Just (DefData c) -> pure (Call x, eval (env cxt) (dataType c))
          Just (DefEq c)   -> pure (Call x, eval (env cxt) (eqTypeDef c))
          Nothing -> throwIO $ Error cxt $ NameNotInScope x
    go 0 (types cxt)

  R.Lam x (Right i) t -> do
    a <- evalCxt cxt <$> freshMeta cxt
    let cxt' = bind cxt x a
    (t, b) <- insert cxt' $ infer cxt' t
    pure (Lam x i t, VPi x i a $ closeVal cxt b)

  R.Lam x Left{} t ->
    throwIO $ Error cxt InferNamedLam

  R.App t u i -> do

    -- choose implicit insertion
    (i, t, tty) <- case i of
      Left name -> do
        (t, tty) <- insertUntilName cxt name $ infer cxt t
        pure (Impl, t, tty)
      Right Impl -> do
        (t, tty) <- infer cxt t
        pure (Impl, t, tty)
      Right Expl -> do
        (t, tty) <- insert' cxt $ infer cxt t
        pure (Expl, t, tty)

    -- ensure that tty is Pi
    (a, b) <- case force tty of
      VPi x i' a b -> do
        unless (i == i') $
          throwIO $ Error cxt $ IcitMismatch i i'
        pure (a, b)
      tty -> do
        a <- evalCxt cxt <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt VType tty (VPi "x" i a b)
        pure (a, b)

    u <- check cxt u a
    pure (App t u i, b $$ evalCxt cxt u)

  R.U ->
    pure (Type, VType)

  R.Pi x i a b -> do
    a <- check cxt a VType
    b <- check (bind cxt x (evalCxt cxt a)) b VType
    pure (Pi x i a b, VType)

  R.Let x a t u -> do
    a <- check cxt a VType
    let ~va = evalCxt cxt a
    t <- check cxt t va
    let ~vt = evalCxt cxt t
    (u, b) <- infer (define cxt x vt va) u
    pure (Let x a t u, b)

  R.Hole -> do
    a <- evalCxt cxt <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)

  R.Absurd t -> do
    ty <- evalCxt cxt <$> freshMeta cxt
    t <- check cxt t ty
    pure (t, ty)
  R.Prop -> pure (Prop, VType)
  R.Cast -> do
    pure (Prim Cast, evalCxt cxt castTy)
  R.Apd -> do
    pure (Prim Apd, evalCxt cxt apdTy)
  R.Rfl -> do
    pure (Prim Rfl, evalCxt cxt rflTy)
  R.Oeq a u v -> do
    a <- check cxt a VType -- TODO: Prop-valued equality
    let av = evalCxt cxt a
    u <- check cxt u av
    v <- check cxt v av
    pure (applySp (Prim Oeq) [(a, Impl), (u, Expl), (v, Expl)], VProp)

-- apd : {A : U} {B : A → U} {x y : A} (f : (x : A) → B x) (h : x ~{A} y) → 
-- cast (B x) (B y) (apd {A} {λ _ → U} {x} {y} B h) (f x) =_{B y} f y
apdTy :: Ty
apdTy = Pi "A" Impl Type $
        Pi "B" Impl (Pi "_" Expl (Var 0) Type) $
        Pi "x" Impl (Var 1) $
        Pi "y" Impl (Var 2) $
        Pi "f" Expl (Pi "x" Expl (Var 3) (App (Var 3) (Var 0) Expl)) $
        Pi "h" Expl (applySp (Prim Oeq) [(Var 4, Impl), (Var 2, Expl), (Var 1, Expl)]) $
        let h = Var 0
            f = Var 1
            y = Var 2
            x = Var 3
            b = Var 4
            a = Var 5
            lhs = applySp (Prim Cast) $
              [ (eApp b x, casticit)
              , (eApp b y, casticit)
              , (applySp (Prim Apd)
                    [ (a, Impl), (Lam "_" Expl Type, Impl)
                    , (x, Impl), (y, Impl), (b, Expl), (h, Expl)
                    ], Expl)
              , (eApp f x, Expl)
              ]
            rhs = eApp f y
        in applySp (Prim Oeq) [(eApp b y, Impl), (lhs, Expl), (rhs, Expl)]

-- cast : [A B : U] → A ~{U} B → A → B
castTy :: Ty
castTy = Pi "A" casticit Type $
         Pi "B" casticit Type $
         Pi "_" Expl (applySp (Prim Oeq) [(Type, Impl), (Var 1, Expl), (Var 0, Expl)]) $
         Pi "_" Expl (Var 2) $
         Var 2

rflTy :: Ty
rflTy = Pi "A" Impl Type $
        Pi "x" Expl (Var 0) $
        applySp (Prim Oeq) [(Var 1, Impl), (Var 0, Expl), (Var 0, Expl)]

findType :: Cxt -> Lvl -> VTy
findType cxt (lvl2Ix (lvl cxt) -> unIx -> ix) = case types cxt !! ix of
  (_, _, a) -> a

--------------------------------
-- Check the Pattern Matching --
--------------------------------
{-
Consider the following function definition:

```
f : (x : A) (y : B) (z : C) -> D 
f p1 p2 p3 = rhs
```

Each pattern corresponds to a variable in the telescope.
The former pattern will affect the later types. 
For example, when we matching `x` with the pattern `p1`, the later type becomes `(y : B[p1/x]) (z : C[p1/x]) -> D[p1/x]`.
After all three patterns are matched, we check `rhs : D [p1/x] [p2/y] [p3/z]`.

On the other hand, we need to consider the dependency of the patterns.
The former variable pattern can be re-assigned by the later patterns.
Many systems use special annotations to indicate patterns that are assigned values, commonly referred to as Inaccessible Patterns.
We do not use inaccessible patterns here, simply using variable patterns instead and adding new bindings in rhs Cxt.

For example,

```
sym : (x y : A) -> x = y -> y = x
sym x y (refl u) = ?0
```

The rhs looks like,

x = u : A
y = u : A
u : A
-----------
?0 : u = u

Using de Bruijn index and level, it looks like,

Name  | Index  | Val (Level)
-------------------------------
u     | 0      | VVar 2 <-╮<╮
y     | 1      | VVar 2 --╯ |
x     | 2      | VVar 2 ----╯

The weired thing is that the some of the outer variables are assigned by inner values.
This would not be a problem when we implementing it, since we are using de Bruijn levels as values.
-}

data UnifRes
  = UnifOk Cxt
  | UnifStuck  -- When Agda would say : I'm not sure if there should be a case for the constructor 
  | UnifFail   -- Absurd pattern

-- unify ctx u v t = ctx'
-- Here ctx is the current context, u and v are the two values we are trying to unify,
-- t is their type, and ctx' is the context after unification.
-- We need to update the portion of the context that comes after the unified variable.
unify :: HasGlobal => Cxt -> Val -> Val -> VTy -> IO UnifRes
unify ctx u v t = do
  -- putStrLn $ "Unifying: " ++ showVal ctx u ++ " and " ++ showVal ctx v ++ " at type " ++ showVal ctx t
  case (force u, force v, force t) of
    (VVar x, v, _)
      | x `notElem` fv (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (v, VVar x, _)
      | x `notElem` fv (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (VCons c us, VCons c' vs, VData d ts) -- QIT constructors have no injectivity
      | consName c == consName c' && not (isQIT d) ->
          unifySp ctx us vs $ evalCxt ctx (consType c)
      | not (isQIT d) -> pure UnifFail
    (VData d us, VData d' vs, _)
      -- We assume the injectivity of datatype formers over indexes. I think it is safe without UA
      -- Which makes the dpm analysis for QIT constructors easier.
      | dataName d == dataName d' ->
          unifySp ctx us vs $ evalCxt ctx (dataType d)
      | otherwise -> pure UnifFail
    (u, v, _) ->
      (U.unify (env ctx) (lvl ctx) u v >> pure (UnifOk ctx))
      `catch` \ UnifyError ->
          pure UnifStuck

unifySp :: HasGlobal => Cxt -> Spine -> Spine -> VTy -> IO UnifRes
unifySp ctx us vs ts = go ctx (reverse us) (reverse vs) ts where
  go ctx []                         []                          _ = pure $ UnifOk ctx
  go ctx ((force -> u, i1):us) ((force -> v, i2):vs) (VPi x i3 t b) 
    | i1 == i2 = do
      uni_res <- unify ctx (updateVal ctx u) (updateVal ctx v) t
      case uni_res of
        UnifOk ctx' -> go ctx' us vs (b $$ updateVal ctx' u)
        e -> pure e
  go ctx _ _ _ = throwIO $ DefError ctx PatArgMismatch


freshVal :: HasGlobal =>  [Val] -> [Val] -> Val -> Val
freshVal from to = eval to . quote (Lvl (length from))

-- Note. This is a very bad function, it refresh the hole context.
-- But I can't figure out a better way now.
-- The Context in this project is not very well formed for most cases.
-- For example, we may have a context: `cxt, x : A, cxt'` where `A` may refer to variables in `cxt'`.
updateCxt :: HasGlobal => Cxt -> Lvl -> Val -> Cxt
updateCxt ctx x v = if length env' /= length bds' then error "!!!" else ctx {env = env', types = typ', bds = bds'} where
  env1 = env ctx
  typ = types ctx
  x' = unIx $ lvl2Ix (lvl ctx) x
  (postenv, xval_old:prenv) = splitAt x' env1

  changeTail :: [a] -> [a] -> [a]
  changeTail orig new = take (length orig - length new) orig ++ new

  -- The enviroment where only x changed.
  env2 = postenv ++ v : prenv

  -- Use the context above to update the parts of the context affected by it.
  -- Note that earlier parts of the context may also be affected, so we need to refresh the entire context here.
  -- The previous version only updated the later part of the context.
  refresh :: [Val] -> Types -> ([Val], Types)
  refresh [] [] = ([], [])
  refresh (v:es) ((x,ori,t):tys) =
    let (es', tys') = refresh es tys
        env'' = changeTail env2 es'
    in (freshVal env1 env'' v:es', (x, ori, freshVal env1 env'' t):tys')
  refresh _ _ = error "refresh: impossible"

  (env', typ') = refresh env1 typ

  genBDs :: [(Ix, Val)] -> [BD]
  genBDs = map checkBD where
    checkBD (ix, VVar lv) | ix == lvl2Ix (lvl ctx) lv = Bound
    checkBD _ = Defined

  bds' = genBDs [ (Ix x, v) | (x, v) <- zip [0 .. length env' - 1] env' ]

checkCls :: HasGlobal => Cxt -> Id -> Ty -> R.RClause -> IO Clause
checkCls ctx func_name func_typ (R.RClause rps rhs) = do
  let func_typ' = evalCxt ctx func_typ
  (ps, ctx', rhs_ty) <- checkPat False ctx rps func_typ'
  rhs' <- check ctx' rhs rhs_ty
  let rhs'' = nf (env ctx') rhs'
  -- NOTE. The @nf@ here should remove all the metas.
  if noMetas rhs'' then
    pure $ Clause ps rhs''
  else do
    throwIO $ DefError ctx $ UnsolvedMetaInFuncDef func_name

-- Pattern match against given type, returning the rest type (rhs type) and rhs Cxt.
-- isCons = True, if we are elaborating the patterns of a constructor.
-- Throws `Error`, throw `DefError _ $ WrongPattern _ _` for absurd patterns, `DefError _ $ UnsurePattern _ _` for IDK patterns.
-- TODO : Change the return type to `IO ([(Pattern, Icit)], Spine, Cxt, VTy)`
checkPat :: HasGlobal => Bool -> Cxt -> R.RPatterns -> VTy -> IO ([(Pattern, Icit)], Cxt, VTy)
checkPat isCons ctx [] ty
  | isCons = case force ty of
    -- If we are elaborating constructor patterns, we need to make sure all implicit patterns are filled.
    -- i.e.
    -- data Id : U -> U -> U where 
    --    | refl : {x : U} -> Id x x
    -- symm : Id x y -> Id y x 
    -- symm refl = refl 
    -- would be elaborated as
    -- symm (refl {u}) = refl 
      VPi x Impl a b -> do
        let ctx' = bind ctx ('_':x) a
        let b' = b $$ VVar (lvl ctx)
        (rps, rctx, rty) <- checkPat isCons ctx' [] b'
        pure ((PatVar ('_':x), Impl): rps, rctx, rty)
      _ -> pure ([], ctx, ty)
  | otherwise = pure ([], ctx, ty)
checkPat isCons ctx ((Right i, R.RPat c c_arg):ps) (force -> VPi x' i' (force -> a) b) | i == i' =
  case M.lookup c ?defs of
    Just (DefCons _) ->
      case a of
        VData d d_arg -> do
          (c_tele, c_ix) <- case lookupCons d c of
            Just r -> pure r
            Nothing -> throwIO $ DefError ctx $ NameIsNotCons c (Just d)
          let c_ty = evalCxt ctx $ getConsType d c_tele c_ix
          (ps', ctx', c_ty') <- checkPat True ctx c_arg c_ty
          d_arg' <- case c_ty' of
            VData _ x -> pure x
            e -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx' e)
          let d_type = evalCxt ctx' (dataType d)

          -- trace ("At") $ pure ()
          -- trace (showVal ctx' a) $ pure ()
          -- trace (showVal ctx' c_ty') $ pure ()
          -- trace (showVal ctx' d_type) $ pure ()

          -- Here we try to unify the returning indexes of constructor pattern with the type
          uni_res <- unifySp ctx' d_arg d_arg' d_type
          ctx'' <- case uni_res of
            UnifOk c -> pure c
            UnifStuck -> throwIO $ DefError ctx $ UnsurePattern c (quoteCxt ctx a)
            UnifFail -> throwIO $ DefError ctx $ WrongPattern c (quoteCxt ctx a)
          -- b_rest is using an old Cxt in its closure, so we need to update it.
          -- So we have to refresh the Cxt.
          -- Note. Here p2v start from the level of ctx, not ctx''.
          let p = PatCon c ps'
          let patVal = p2v (lvl ctx) p
          let patVal' = evalCxt ctx'' (quoteCxt ctx'' patVal)
          let b_rest = b $$ patVal'
          let b_rest_updated = evalCxt ctx'' (quoteCxt ctx'' b_rest)
          (rps, rctx, rty) <- checkPat isCons ctx'' ps b_rest_updated
          pure ((p, i) : rps, rctx, rty)
        _ -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx a)
    (Just (DefEq _)) | isQITCon c -> case M.lookup c (extraEq ?qitInfo) of
        Nothing -> error "checkPat: impossible"
        Just conEq -> case force a of
          VPrim Oeq eq_arg@(reverse -> [(force -> VData d d_arg, Impl), (lhs, Expl), (rhs, Expl)]) | isQIT d -> do
            -- TODO: refactor, merge with the above code.
            let c_tele = eqTel conEq
            let c_ix = eqIx conEq
            let c_ty = evalCxt ctx $ getPathConType d c_tele c_ix (eqLhs conEq) (eqRhs conEq)
            -- putStrLn $ "lhs: " ++ showVal ctx lhs ++ " rhs: " ++ showVal ctx rhs
            -- putStrLn $
            --   "Checking constructor " ++ c ++ "with tele: " ++ show c_tele ++ " and ix: " ++ show c_ix ++ "\n get c_ty: " ++ showVal ctx c_ty
            (ps', ctx', c_ty') <- checkPat True ctx c_arg c_ty
            eq_args' <- case c_ty' of
              VPrim Oeq sp@(reverse -> [(VData d' dsp, Impl), (lhs', Expl), (rhs', Expl)])
                | dataName d' == dataName d -> pure sp
              e -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx' e)
            let oeqTy = Pi "A" Impl Type $
                        Pi "x" Expl (Var 0) $
                        Pi "y" Expl (Var 1) $
                        Type
            -- Work mark
            let oeq_type = evalCxt ctx' oeqTy
            -- remember to unify lhs and rhs
            -- putStrLn $ "Unifying: " ++ showSp ctx' eq_arg ++ " and " ++ showSp ctx' eq_args' ++ " at type " ++ showVal ctx' oeq_type
            uni_res <- unifySp ctx' eq_arg eq_args' oeq_type
            ctx'' <- case uni_res of
              UnifOk c  -> pure c
              UnifStuck -> throwIO $ DefError ctx $ UnsurePattern c (quoteCxt ctx a)
              UnifFail  -> throwIO $ DefError ctx $ WrongPattern  c (quoteCxt ctx a)

            let p = PatCon c ps'
            let patVal = p2v (lvl ctx) p
            let patVal' = evalCxt ctx'' (quoteCxt ctx'' patVal)
            let b_rest = b $$ patVal'
            let b_rest_updated = evalCxt ctx'' (quoteCxt ctx'' b_rest)
            (rps, rctx, rty) <- checkPat isCons ctx'' ps b_rest_updated
            pure ((p, i) : rps, rctx, rty)

          t -> error (show t) -- throwIO $ DefError ctx $ PMNoneEq (quoteCxt ctx a)
    _ | null c_arg -> do -- Var pattern.
          let x = c
          let ctx' = bind ctx x a
          let b' = b $$ VVar (lvl ctx)
          (ps', rest, rhs) <- checkPat isCons ctx' ps b'
          pure ((PatVar x, i):ps', rest, rhs)
      | otherwise     -> throwIO $ DefError ctx $ NameIsNotCons c Nothing
checkPat isCons ctx ps@((Left x, p):ps') (force -> VPi x' i' (force -> a) b)
  | i' == Impl && x == x' = checkPat isCons ctx ((Right Impl, p):ps') (VPi x' Impl a b) -- Jump to the former clause
  | otherwise             = do
      let ctx' = bind ctx ('_':x') a
      let b' = b $$ VVar (lvl ctx)
      (rps, rctx, rty) <- checkPat isCons ctx' ps b'
      pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps@((Right Expl, _):ps') (force -> VPi x' Impl (force -> a) b) = do
    let ctx' = bind ctx ('_':x') a
    let b' = b $$ VVar (lvl ctx)
    (rps, rctx, rty) <- checkPat isCons ctx' ps b'
    pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps t = throwIO $ DefError ctx $ PatArgMismatch

patApp :: Pattern -> (Pattern, Icit) -> Pattern
patApp (PatCon c ps) p = PatCon c (ps ++ [p])
patApp (PatFunc f ps) p = PatFunc f (ps ++ [p])
patApp (PatVar x) p = error "patApp: impossible"

-- checkPat' cxt (f, fv) ps ty 
-- returns (cxt', p', patVal, rhs_ty)
-- `cxt' |- f ps = fv ps = p' = patVal : rhs_ty`
-- TODO: modify checkPat function (more information is needed), so I don't need this function anymore.
applyPat :: HasGlobal => Cxt -> (Pattern, Val) -> PatternTele Empty -> VTy -> IO (Cxt, Pattern, Val, VTy)
applyPat cxt (f, fv) [] ty = pure (cxt, f, fv, ty)
applyPat cxt (f, fv) ((p, i):ps) ty = case force ty of
  VPi x i' a b | i == i' -> case (p, force a) of
    (PatVar x', a') -> do
      let cxt' = bind cxt x' a'
      let b' = b $$ VVar (lvl cxt)
      let f' = patApp f (p, i)
      let fv' = vApp fv (VVar (lvl cxt)) i
      applyPat cxt' (f', fv') ps b'
    (PatCon c c_arg, VData d d_arg) -> do
      (c_def, c_tele, c_ix) <- case (M.lookup c ?defs, lookupCons d c) of
          (Just (DefCons c_def), Just (r1, r2)) -> pure (c_def, r1, r2)
          _ -> error "applyPat: impossible"
      let c_ty = evalCxt cxt $ getConsType d c_tele c_ix
      (cxt', cp, cv, c_ty') <- applyPat cxt (PatCon c [], VCons c_def []) c_arg c_ty
      d_arg' <- case c_ty' of
          VData _ x -> pure x
          e -> error "applyPat: impossible"
      let d_type = evalCxt cxt' (dataType d)
      uni_res <- unifySp cxt' d_arg d_arg' d_type
      cxt'' <- case uni_res of
        UnifOk c -> pure c
        _ -> error "applyPat: impossible"
      let fv_u = evalCxt cxt'' (quoteCxt cxt'' fv)
      let cv_upd = evalCxt cxt'' (quoteCxt cxt'' cv)
      let b_rest = b $$ cv_upd
      let b_rest_upd = evalCxt cxt'' (quoteCxt cxt'' b_rest)
      let fv_upd_c = vApp fv_u cv_upd i
      applyPat cxt'' (patApp f (cp, i), fv_upd_c) ps b_rest_upd
    _ -> error "applyPat: impossible"
  _ -> error "applyPat: impossible"

-- Coverage Checking
-------------------------------

type ClauseLHS = [(Pattern, Icit)]

type MissingPattern = [Spine]

data CoverCheckingError
  = CoverMissPat MissingPattern
  | MeetIDKCons -- TODO: Is this necessary? IDK case should be filterred out in dpm check phase?
  deriving Show

data CoverRes
  = CoverOk
  | CoverStuck Lvl (PatternTele ()) -- Which variable is stucking, and where is it
  | CoverFail [(Cxt, Spine)] -- Meet a dead end

checkCover :: HasGlobal => Bool -> Cxt -> FuncDef -> VTy -> Int -> [ClauseLHS] -> Either CoverCheckingError ()
checkCover genApdC ctx fn fty arity clss = case testManySpine genApdC fn clss [initSp] of
    Nothing -> Left MeetIDKCons
    Just [] -> Right ()
    Just sp -> Left . CoverMissPat $ map snd sp
  where
    genInitSpine :: Cxt -> VTy -> Int -> (Cxt, Spine)
    genInitSpine cxt ty 0 = (cxt, [])
    genInitSpine cxt (force -> VPi x i a b) arity =
      let (cxt', sp) = genInitSpine (bind cxt ("_cov_chk_"++x) a) (b $$ VVar (lvl cxt)) (arity - 1)
      in (cxt', sp ++ [(VVar (lvl cxt), i)]) -- TODO: Spine is reversed, change to normal list one day. 
    genInitSpine _ _ _ = error "genInitSpine: impossible"
    initSp = genInitSpine ctx fty arity

-- Given a `x in ctx`, where `ctx |- x : D args`, where D is a data type,
-- returns all possible context for splitting `x`.
-- For example,  
-- if `ctx |- x : Nat`, then `splitCxt ctx x = Just [ctx [x |-> zero], ctx [x |-> suc (VVar y)]]` where `y : Nat` is a fresh variable. 
-- Return `Nothing`, if there is one or more IDK constructors. 
splitCxt :: HasGlobal => Cxt -> Lvl -> Maybe [Cxt]
splitCxt cxt x = case force (findType cxt x) of
  x_ty@(VData d d_arg) -> might $ do
    fmap join $ forM (dataCons d) $ \c@(c_name, c_tele, _) -> do
          -- split x to constructor c
          -- make a raw pattern
          let p = R.RPat c_name (makePs c_tele)
          -- check the pattern against x's type
          cp <- (checkPat False cxt [(Right Expl, p)] (VPi "_" Expl x_ty (Closure (env cxt) Type)) >>= pure . Just)
                                `catch` \case
                                  DefError _ (UnsurePattern _ _) -> quitMight
                                  DefError _ (WrongPattern _ _) -> pure Nothing
                                  e -> error $ "impossible: " ++  show e
          case cp of
            Nothing -> pure []
            Just ([(p', _)], cxt', _) -> do
              let pv = p2v (lvl cxt) p'
              let cxt'' = updateCxt cxt' x pv
              pure [cxt'']
            _ -> error "splitCxt: impossible"
  
  x_ty@(VPrim Oeq sp@([]:>(a, _):>(lhs, _):>(rhs, _)))
    | VData d d_arg <- force a 
    -> might $ do 
      let cons = fromJust $ M.lookup (dataName d) (extraEq' ?qitInfo)
      fmap join $ forM cons $ \c -> do
        let c_name = eqName c
        let c_tele = eqTel c
        -- split x to constructor c
        -- make a raw pattern
        let p = R.RPat c_name (makePs c_tele)
        -- check the pattern against x's type
        cp <- (checkPat False cxt [(Right Expl, p)] (VPi "_" Expl (VPrim Oeq sp) (Closure (env cxt) Type)) >>= pure . Just) 
                              `catch` \case
                                DefError _ (UnsurePattern _ _) -> quitMight
                                DefError _ (WrongPattern _ _) -> pure Nothing
                                e -> error $ "impossible: " ++  show e
        case cp of
          Nothing -> pure []
          Just ([(p', _)], cxt', _) -> do
            let pv = p2v (lvl cxt) p'
            let cxt'' = updateCxt cxt' x pv
            pure [cxt'']
          _ -> error "splitCxt: impossible"

    
  x_ty -> error $ "splitCxt: impossible: " ++ show x_ty
  where
    makePs :: Telescope -> R.RPatterns
    makePs [] = []
    makePs ((x, i, _):xs) = (Right i, R.RPat ("_cov_chk_"++x) []) : makePs xs

-- Check a list of clause lhs against a spine
-- If the spine can be matched by the patterns, return ()
-- If stucked, split the stucked variable of the spine.
-- If fails, move to next clause lhs.
testSpine :: HasGlobal => [ClauseLHS] -> Cxt -> Spine -> CoverRes
testSpine clss cxt sp = go clss where -- cxt |- sp 
  go = \case
    [] -> CoverFail [(cxt, sp)]
    (ps:rest) -> case match (env cxt) ps sp of
      MatchSuc _ -> CoverOk
      MatchFailed -> go rest -- move to next clause
      MatchStuck (BVar x ps) -> CoverStuck x ps
      _ -> error "impossible"

-- Get the spine with splitting the stucked variable
-- Return `Nothing`, if there is one or more IDK constructors.
-- Return `Just (_, True)`, if the splitting variable is a QIT element 
genSpine :: HasGlobal => Cxt -> Spine -> Lvl -> Maybe ([(Cxt, Spine)], Bool)
genSpine cxt sp x = do
    fst <- genSpine' cxt sp x
    case force (findType cxt x) of
      VData d d_arg ->
        pure (fst, isQIT d)
      VPrim Oeq ([]:>(force -> VData d d_arg, _):>(lhs, _):>(rhs, _)) -> 
        pure (fst, False)
      ty -> error $ "impossible" ++ show ty
  where
    genSpine' :: Cxt -> Spine -> Lvl -> Maybe [(Cxt, Spine)]
    genSpine' cxt sp x = do -- Maybe
      splitted_cxts <- splitCxt cxt x
      Just $ do -- List
        cxt' <- splitted_cxts
        let sp' = updateSp cxt' sp
        pure (cxt', sp')

testManySpine :: HasGlobal => Bool -> FuncDef -> [ClauseLHS] -> [(Cxt, Spine)] -> Maybe [(Cxt, Spine)]
testManySpine genApdC f clss = \case -- f will not be used, if genApdC=False
  [] -> Just []
  (cxt, sp):rest -> case testSpine clss cxt sp of
    CoverOk -> testManySpine genApdC f clss rest
    CoverStuck l blk_pos -> do
      (gen, isqit) <- genSpine cxt sp l
      -- if isqit, we need to generate apd clauses,
      when (isqit && genApdC) $ do
        -- trace "found a QIT elim" $ pure ()
        unsafePerformIO $ Just <$> generateApdClauses' cxt f blk_pos
      left <- forM gen $ \ (cxt', sp') ->
        testManySpine genApdC f clss [(cxt', sp')]
      right <- testManySpine genApdC f clss rest
      pure $ join left ++ right
    CoverFail sp' -> do
      right <- testManySpine genApdC f clss rest
      pure $ sp' ++ right

generateApdClauses' :: HasGlobal => Cxt -> FuncDef -> PatternTele () -> IO ()
generateApdClauses' cxt f ps = do
  -- putStrLn $ "Generating apd clauses for function: " ++ funcName f ++ " with patterns: " ++ show ps
  apd_cls <- generateApdClauses cxt f ps
  -- putStrLn $ "Generated apd clauses: " ++ showSp (apdCxt apd_cls) (apdSpn apd_cls)
  insertCls (funcName f) apd_cls

-- apd {A : U} {B : A → U} 
--     (fps : (x : A) → B x)
--     {x y : A}  
--     (h : x =_A y) : 
--    cast (B x) (B y) (apd {A} {λ _ → U} {x} {y} B h) (fps x) =_{B y} fps y
-- No nested patterns supported yet. A QIT pattern must at top
-- It seems we must consider `apd` as `apd-f-ps` defined for each function `f` and pattern `ps`.
-- So the type is also dependent on `f` and `ps`, thus we don't need `A` and `B` as parameters.
-- apd (fps : (x : A) → B x) {x y : A} (h : x =_A y) : cast (B x) (B y) (apd {A} {λ _ → U} {x} {y} B h) (fps x) =_{B y} fps y
generateApdClauses :: HasGlobal => Cxt -> FuncDef -> PatternTele () -> IO ApdCls
generateApdClauses cxt f ps' = do
  (cxt', fps, fpsv, fpsty) <- applyPat cxt (PatFunc (funcName f) [], VFunc f []) ps (evalCxt cxt $ funcType f)
  -- putStrLn $ "applyPat used: fpsv= " ++ showVal cxt' fpsv ++ "; fpsty= " ++ showVal cxt' fpsty
  case force fpsty of
    VPi x Expl a b -> -- a must be a QIT type 
      case force a of
        VData d d_arg | isQIT d -> do
          let x_pat = PatVar "_x"
          let x_val = VVar (lvl cxt')
          let y_pat = PatVar "_y"
          let y_val = VVar (lvl cxt' + 1)
          let h_pat = PatVar "_h"
          let h_val = VVar (lvl cxt' + 2)
          let pats = [(fps, Expl), (x_pat, Impl), (y_pat, Impl), (h_pat, Expl)]
          let vals = [(fpsv, Expl), (x_val, Impl), (y_val, Impl), (h_val, Expl)]
          let cxt'xy = bind (bind cxt' "_x" a) "_y" a
          let h_ty = vAppSp (VPrim Oeq []) $ [] :> (a, Impl) :> (x_val, Expl) :> (y_val, Expl)
          let cxt'xyh = bind cxt'xy "_h" h_ty
          -- cast (B x) (B y) (apd {A} {λ _ → U} {x} {y} (λ z → B z) h) (fps x) =_{B y} fps y
          pure $ ApdCls
            cxt'xyh
            pats
            vals
        _ -> error "impossible"
    _ -> error "impossible"
  where
    ps = go [] ps' where
      go _ [] = error "impossible: where is the QIT pattern?"
      go acc ((PatMark (), i) : ps) = acc
      go acc ((p, i) : ps) = go (acc ++ [(fromJust $ noMark p, i)]) ps
  -- [(Cxt, PatternTele Empty, Spine)]

reportOpnCls :: HasGlobal => IO ()
reportOpnCls = do
  cls <- readIORef opnCls
  putStrLn "Opening congruences: "
  forM_ (M.toList cls) $ \(_, cs) -> do
    forM_ cs $ \ap -> do
      putStrLn $ "  apd " ++ showSp (apdCxt ap) (apdSpn ap)

-- TODO: Cxt and Defs/QITInfo should be seperated
checkApdCover :: HasGlobal => Name -> IO (Either CoverCheckingError ())
checkApdCover fnName = do
  cls <- readIORef opnCls
  case M.lookup fnName cls of
    Nothing -> error "impossible"
    Just opns -> do
      let cxtsp = (\ApdCls{..} -> (apdCxt, reverse apdSpn)) <$> opns
      lhss <- case M.lookup fnName (definedApd ?qitInfo) of
            Nothing -> do
              putStrLn $ "Error: There is no apd clause definition for funtion " ++ fnName -- make it better
              pure []
            Just lhss -> pure lhss
      let res = testManySpine False (FuncDef "dummy-value" Type []) lhss cxtsp
      -- The function def is never used if the first arg is false.
      pure $ case res of
        Nothing -> Left MeetIDKCons
        Just [] -> Right ()
        Just sp -> Left . CoverMissPat $ map snd sp

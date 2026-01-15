module Elaboration (check, infer, unifyCatch, findType, checkPat, updateCxt, checkCover, CoverCheckingError(..), MissingPattern, splitCxt, checkCls) where

import Control.Exception
import Control.Monad
import Data.IORef

import qualified Data.IntMap as IM

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
import Data.Maybe (isJust)
import Debug.Trace (trace)


-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  U.unifyCxt cxt t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quoteCxt cxt t) (quoteCxt cxt t')

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act where
  go (t, va) = case force (defs cxt) va of
    VPi x Impl a b -> do
      m <- freshMeta cxt
      let mv = evalCxt cxt m
      go (App t m Impl, (defs cxt, b) $$ mv)
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _), va) -> pure (t, va)
  (t               , va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act where
  go (t, va) = case force (defs cxt) va of
    va@(VPi x Impl a b) -> do
      if x == name then
        pure (t, va)
      else do
        m <- freshMeta cxt
        let mv = evalCxt cxt m
        go (App t m Impl, (defs cxt, b) $$ mv)
    _ ->
      throwIO $ Error cxt $ NoNamedImplicitArg name

check :: Cxt -> R.Tm -> VTy -> IO Tm
check cxt t a = case (t, force (defs cxt) a) of

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
    Lam x i' <$> check (bind cxt x a) t ((defs cxt, b) $$ VVar (lvl cxt))

  (R.LamCase cls, ty) -> do
    cls' <- mapM (checkLamCls cxt ty) cls
    case checkCover cxt ty (arity cls') (map clausePatterns cls') of
      Left err ->  throwIO $ Error cxt LambdaCaseUnCover
      Right () -> pure $ LamCase cls'

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x Impl a b) -> do
    Lam x Impl <$> check (newBinder cxt x a) t ((defs cxt, b) $$ VVar (lvl cxt))

  -- See https://github.com/KonjacSource/ShiTT2/issues/1
  -- (t, a@(VData d sp)) | Just (c, sp) <- (trace ("| checking data: " ++ dataName d) $ isCons t) -> do 
  --   putStrLn $ "Checking constructor " ++ consName c ++ " against type " ++ showVal cxt a
  --   checkCons c sp (evalCxt cxt (consType c)) a

  (R.Let x a t u, a') -> do
    a <- check cxt a VU
    let ~va = evalCxt cxt a
    t <- check cxt t va
    let ~vt = evalCxt cxt t
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

  (R.Match t cls, ty) -> do
    (t', tt) <- infer cxt t
    let lc = R.LamCase cls
    lc' <- check cxt lc (varr cxt tt ty)
    pure $ App lc' t' Expl

  (R.Hole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t
  -- where
  --   isCons :: R.Tm -> Maybe (ConsDef, R.Spine)
  --   isCons t = case R.flattenApp t of
  --     (R.Var c, args) -> case M.lookup c (defs cxt) of
  --       Just (DefCons cons) -> Just (cons, args)
  --       _                   -> Nothing
  --     _ ->  Nothing

  --   checkCons :: ConsDef -> R.Spine -> VTy -> VTy -> IO Tm
  --   checkCons c sp ty goal = do
  --     putStrLn $ "Elaborating constructor " ++ consName c
  --     (metas, ret_ty) <- metaSpine ty
  --     putStrLn $ "Metas for constructor " ++ consName c ++ ": " ++ show (length metas)
  --     putStrLn $ "Metas: " ++ show (map (showVal cxt) (map fst metas))
  --     putStrLn $ "Goal " ++ showVal cxt goal
  --     putStrLn $ "Return type " ++ showVal cxt ret_ty
  --     unifyCatch cxt goal ret_ty
  --     putStrLn $ "Unification done for constructor " ++ consName c
  --     build <- go sp metas ty []
  --     putStrLn $ "Constructor " ++ consName c ++ " checked successfully."
  --     pure (applySp (Call $ consName c) build)
  --     where
  --       metaSpine ::VTy -> IO (Spine, Val)
  --       metaSpine ty = case force (defs cxt) ty of
  --         ty@(VData {}) -> pure ([], ty)
  --         VPi x i a b -> do
  --           m <- freshMeta cxt
  --           let mv = evalCxt cxt m
  --           (rest, ty) <- metaSpine ((defs cxt, b) $$ mv)
  --           pure ((mv, i) : rest, ty)
  --         _ -> throwIO $ Error cxt $ TypeMismatch (Left "a data type or a pi type") (quoteCxt cxt ty) (applySp (Call $ consName c) [])

  --       go :: R.Spine -- Arguments for now
  --          -> Spine -- Metas to fill
  --          -> VTy -- Current type, insert its argument when needed 
  --          -> TSpine -- Built spine
  --          -> IO TSpine
  --       go [] metas ty build = trace "go []" $ case force (defs cxt) ty of
  --         VData {}
  --           | null metas -> do
  --             unifyCatch cxt ty goal
  --             pure build
  --           | otherwise ->
  --             error "IMPOSSIBLE"
  --         VPi x Impl a b
  --           | ((m', Impl):ms) <- metas -> do
  --             m <- freshMeta cxt
  --             let mv = evalCxt cxt m
  --             unifyCatch cxt m' mv
  --             go [] ms ((defs cxt, b) $$ mv) (build ++ [(m, Impl)])
  --           | ((_, Expl):_) <- metas ->
  --             throwIO $ Error cxt $ IcitMismatch Expl Impl
  --           | otherwise -> error "IMPOSSIBLE"
  --         ty -> throwIO $ Error cxt $ TypeMismatch (Left "a data type") (quoteCxt cxt ty) (applySp (Call $ consName c) build)
  --       go allsp@((t, i) : sp) metas ty build = trace ("go " ++ show (R.stripPos t)) $ case (i, force (defs cxt) ty, metas) of
  --         (Right i, VPi x i' a b, (m, _) : ms)
  --           | i == i' -> do
  --             putStrLn "(Right i, VPi ... ), no insert"
  --             t' <- check cxt t a
  --             putStrLn $ "check done for argument " ++ show (R.stripPos t)
  --             unifyCatch cxt m (evalCxt cxt t')
  --             putStrLn $ "unify done for argument " ++ show (R.stripPos t)
  --             go sp ms ((defs cxt, b) $$ evalCxt cxt t') (build ++ [(t', i)])
  --         (Left name, VPi x Impl a b, (m, _) : ms)
  --           | name == x -> do
  --             putStrLn "(Left name, VPi ... ), no insert"
  --             t' <- check cxt t a
  --             unifyCatch cxt m (evalCxt cxt t')
  --             go sp ms ((defs cxt, b) $$ evalCxt cxt t') (build ++ [(t', Impl)])
  --           | otherwise -> do
  --             putStrLn "(Left name, VPi ... ), insert"
  --             m' <- freshMeta cxt
  --             let mv = evalCxt cxt m'
  --             unifyCatch cxt m mv
  --             go ((t, i) : sp) ms ((defs cxt, b) $$ mv) (build ++ [(m', Impl)])
  --         (Right Expl, VPi x Impl a b, (m, _) : ms) -> do 
  --           putStrLn $ "(Right Expl, VPi ... ), insert" ++ show x
  --           m' <- freshMeta cxt
  --           let mv = evalCxt cxt m'
  --           unifyCatch cxt m mv
  --           go ((t, Right Expl) : sp) ms ((defs cxt, b) $$ mv) (build ++ [(m', Impl)])
  --         (Right Impl, VPi x Expl a b, _) -> do
  --           putStrLn "(Right Impl, VPi ... ), error"
  --           throwIO $ Error cxt $ IcitMismatch Impl Expl
  --         (_, ty, ms) -> do
  --           putStrLn "go _, not a pi" 
  --           throwIO $ Error cxt $ TypeMismatch (Left "a pi type") (quoteCxt cxt ty) (applySp (Call $ consName c) build)

infer :: Cxt -> R.Tm -> IO (Tm, VTy)
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
        go ix [] = case M.lookup x (defs cxt) of
          Just (DefFunc c) -> pure (Call x, eval (defs cxt) (env cxt) (funcType c))
          Just (DefCons c) -> pure (Call x, eval (defs cxt) (env cxt) (consType c))
          Just (DefData c) -> pure (Call x, eval (defs cxt) (env cxt) (dataType c))
          Nothing -> throwIO $ Error cxt $ NameNotInScope x
    go 0 (types cxt)

  R.Lam x (Right i) t -> do
    a <- evalCxt cxt <$> freshMeta cxt
    let cxt' = bind cxt x a
    (t, b) <- insert cxt' $ infer cxt' t
    pure (Lam x i t, VPi x i a $ closeVal cxt b)

  R.Lam x Left{} t ->
    throwIO $ Error cxt InferNamedLam

  R.LamCase _ ->
    throwIO $ Error cxt InferLamCase

  R.Match t cls ->
    throwIO $ Error cxt InferLamCase

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
    (a, b) <- case force (defs cxt) tty of
      VPi x i' a b -> do
        unless (i == i') $
          throwIO $ Error cxt $ IcitMismatch i i'
        pure (a, b)
      tty -> do
        a <- evalCxt cxt <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt tty (VPi "x" i a b)
        pure (a, b)

    u <- check cxt u a
    pure (App t u i, (defs cxt, b) $$ evalCxt cxt u)

  R.U ->
    pure (U, VU)

  R.Pi x i a b -> do
    a <- check cxt a VU
    b <- check (bind cxt x (evalCxt cxt a)) b VU
    pure (Pi x i a b, VU)

  R.Let x a t u -> do
    a <- check cxt a VU
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
unify :: Cxt -> Val -> Val -> VTy -> IO UnifRes
unify ctx u v t =
  case (force' ctx u, force' ctx v) of
    (VVar x, v)
      | x `notElem` fv (defs ctx) (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (v, VVar x)
      | x `notElem` fv (defs ctx) (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (VCons c us, VCons c' vs)
      | consName c == consName c' ->
          unifySp ctx us vs $ evalCxt ctx (consType c)
      | otherwise -> pure UnifFail
    (u, v) ->
      (U.unify (defs ctx) (env ctx) (lvl ctx) u v >> pure (UnifOk ctx))
      `catch` \ UnifyError ->
          pure UnifStuck

unifySp :: HasCallStack => Cxt -> Spine -> Spine -> VTy -> IO UnifRes
unifySp ctx us vs ts = case (reverse us, reverse vs, ts) of
  ([], [], _) -> pure $ UnifOk ctx
  ((force' ctx -> u, i1):us, (force' ctx -> v, i2):vs, VPi x i3 t b) | i1 == i2 -> do
    uni_res <- unify ctx (updateVal ctx u) (updateVal ctx v) t
    case uni_res of
      UnifOk ctx' ->
        let u' = updateVal ctx' u in
        unifySp ctx' us vs ((defs ctx, b) $$ u')
      e -> pure e
  -- ((force' ctx -> u, i1):us, (force' ctx -> v, i2):vs, VPi x i3 t b) -> do 
  --   -- print all the arguments
  --   putStrLn $ showVal ctx u ++ " " ++ show i1
  --   putStrLn $ showVal ctx v ++ " " ++ show i2
  --   putStrLn $ showVal ctx t ++ " " ++ show i3
  --   putStrLn x
  --   error "!!!!"
  _ -> throwIO $ DefError ctx $ PatArgMismatch

freshVal :: Defs -> [Val] -> [Val] -> Val -> Val
freshVal def from to = eval def to . quote def from (Lvl (length from))

-- Note. This is a very bad function, it refresh the hole context.
-- But I can't figure out a better way now.
-- The Context in this project is not very well formed for most cases.
-- For example, we may have a context: `cxt, x : A, cxt'` where `A` may refer to variables in `cxt'`.
updateCxt :: Cxt -> Lvl -> Val -> Cxt
updateCxt ctx x v = if length env' /= length bds' then error "!!!" else ctx {env = env', types = typ', bds = bds'} where
  env1 = env ctx
  typ = types ctx
  def = defs ctx
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
    in (freshVal def env1 env'' v:es', (x, ori, freshVal def env1 env'' t):tys')
  refresh _ _ = error "refresh: impossible"

  (env', typ') = refresh env1 typ

  genBDs :: [(Ix, Val)] -> [BD]
  genBDs = map checkBD where
    checkBD (ix, VVar lv) | ix == lvl2Ix (lvl ctx) lv = Bound
    checkBD _ = Defined

  bds' = genBDs [ (Ix x, v) | (x, v) <- zip [0 .. length env' - 1] env' ]

checkCls :: HasCallStack => Cxt -> Id -> Ty -> R.RClause -> IO Clause
checkCls ctx func_name func_typ (R.RClause rps rhs) = do
  let func_typ' = evalCxt ctx func_typ
  (ps, ctx', rhs_ty) <- checkPat False ctx rps func_typ'
  rhs' <- check ctx' rhs rhs_ty
  let rhs'' = nf (defs ctx') (env ctx') rhs'
  -- NOTE. The @nf@ here should remove all the metas.
  if noMetas rhs'' then
    pure $ Clause ps rhs''
  else do
    throwIO $ DefError ctx $ UnsolvedMetaInFuncDef func_name

checkLamCls :: HasCallStack => Cxt -> VTy -> R.RClause -> IO Clause
checkLamCls ctx fty (R.RClause rps rhs) = do
  (ps, ctx', rhs_ty) <- checkPat False ctx rps fty
  rhs' <- check ctx' rhs rhs_ty
  let rhs'' = nf (defs ctx') (env ctx') rhs'
  if noMetas rhs'' then
    pure $ Clause ps rhs''
  else do
    throwIO $ Error ctx $ UnsolvedMetaInLambdaCase

-- Pattern match against given type, returning the rest type (rhs type) and rhs Cxt.
-- isCons = True, if we are elaborating the patterns of a constructor.
-- Throws `Error`, throw `DefError _ $ WrongPattern _ _` for absurd patterns, `DefError _ $ UnsurePattern _ _` for IDK patterns.
-- TODO : Change the return type to `IO ([(Pattern, Icit)], Spine, Cxt, VTy)`
checkPat :: Bool -> Cxt -> R.RPatterns -> VTy -> IO ([(Pattern, Icit)], Cxt, VTy)
checkPat isCons ctx [] ty
  | isCons = case force' ctx ty of -- If we are elaborating constructor patterns, we need to make sure all implicit patterns are filled.
      VPi x Impl a b -> do
        let ctx' = bind ctx ('_':x) a
        let b' = (defs ctx', b) $$ VVar (lvl ctx)
        (rps, rctx, rty) <- checkPat isCons ctx' [] b'
        pure ((PatVar ('_':x), Impl): rps, rctx, rty)
      _ -> pure ([], ctx, ty)
  | otherwise = pure ([], ctx, ty)
checkPat isCons ctx ((Right i, R.RPat c c_arg):ps) (force' ctx -> VPi x' i' (force' ctx -> a) b) | i == i' =
  case M.lookup c (defs ctx) of
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
          let patVal = p2v (defs ctx'') (lvl ctx) p
          let patVal' = evalCxt ctx'' (quoteCxt ctx'' patVal)
          let b_rest = (defs ctx'', b) $$ patVal'
          let b_rest_updated = evalCxt ctx'' (quoteCxt ctx'' b_rest)
          (rps, rctx, rty) <- checkPat isCons ctx'' ps b_rest_updated
          pure ((p, i) : rps, rctx, rty)
        _ -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx a)
    _ | null c_arg    -> do -- Var pattern.
          let x = c
          let ctx' = bind ctx x a
          let b' = (defs ctx, b) $$ VVar (lvl ctx)
          (ps', rest, rhs) <- checkPat isCons ctx' ps b'
          pure ((PatVar x, i):ps', rest, rhs)
      | otherwise     -> throwIO $ DefError ctx $ NameIsNotCons c Nothing
checkPat isCons ctx ps@((Left x, p):ps') (force' ctx -> VPi x' i' (force' ctx -> a) b)
  | i' == Impl && x == x' = checkPat isCons ctx ((Right Impl, p):ps') (VPi x' Impl a b) -- Jump to the former clause
  | otherwise             = do
      let ctx' = bind ctx ('_':x') a
      let b' = (defs ctx, b) $$ VVar (lvl ctx)
      (rps, rctx, rty) <- checkPat isCons ctx' ps b'
      pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps@((Right Expl, _):ps') (force' ctx -> VPi x' Impl (force' ctx -> a) b) = do
    let ctx' = bind ctx ('_':x') a
    let b' = (defs ctx, b) $$ VVar (lvl ctx)
    (rps, rctx, rty) <- checkPat isCons ctx' ps b'
    pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps t = throwIO $ DefError ctx $ PatArgMismatch

-- Coverage Checking
-------------------------------

type ClauseLHS = [(Pattern, Icit)]

type MissingPattern = [Spine]

data CoverCheckingError = CoverMissPat MissingPattern | MeetIDKCons
  deriving (Show)

data CoverRes
  = CoverOk
  | CoverStuck Lvl -- Which variable is stuck
  | CoverFail [(Cxt, Spine)] -- Meet a dead end

checkCover :: Cxt -> VTy -> Int -> [ClauseLHS] -> Either CoverCheckingError ()
checkCover ctx fty arity clss = case testManySpine (defs ctx) clss [initSp] of
    Nothing -> Left MeetIDKCons
    Just [] -> Right ()
    Just sp -> Left . CoverMissPat $ map snd sp
  where
    genInitSpine :: Cxt -> VTy -> Int -> (Cxt, Spine)
    genInitSpine cxt ty 0 = (cxt, [])
    genInitSpine cxt (force' cxt -> VPi x i a b) arity =
      let (cxt', sp) = genInitSpine (bind cxt ("_cov_chk_"++x) a) ((defs cxt, b) $$ VVar (lvl cxt)) (arity - 1)
      in (cxt', sp ++ [(VVar (lvl cxt), i)]) -- TODO: Spine is reversed, change to normal list one day. 
    genInitSpine _ _ _ = error "genInitSpine: impossible"

    initSp = genInitSpine ctx fty arity

-- Given a `x in ctx`, where `ctx |- x : D args`, where D is a data type,
-- returns all possible context for splitting `x`.
-- For example,  
-- if `ctx |- x : Nat`, then `splitCxt ctx x = Just [ctx [x |-> zero], ctx [x |-> suc (VVar y)]]` where `y : Nat` is a fresh variable. 
-- Return `Nothing`, if there is one or more IDK constructors. 
splitCxt :: Cxt -> Lvl -> Maybe [Cxt]
splitCxt cxt x = case force' cxt (findType cxt x) of
  x_ty@(VData d d_arg) -> might $ do
    fmap join $ forM (dataCons d) $ \c@(c_name, c_tele, c_ix) -> do
          -- split x to constructor c
          -- make a raw pattern
          let makePs :: Telescope -> R.RPatterns
              makePs [] = []
              makePs ((x, i, _):xs) = (Right i, R.RPat ("_cov_chk_"++x) []) : makePs xs
          let p = R.RPat c_name (makePs c_tele)
          -- check the pattern against x's type
          cp <- (checkPat False cxt [(Right Expl, p)] (VPi "_" Expl x_ty (Closure (env cxt) U)) >>= pure . Just)
                                `catch` \case
                                  DefError _ (UnsurePattern _ _) -> quitMight
                                  DefError _ (WrongPattern _ _) -> pure Nothing
                                  e -> error $ "impossible: " ++  show e
          case cp of
            Nothing -> pure []
            Just ([(p', _)], cxt', _) -> do
              let pv = p2v (defs cxt) (lvl cxt) p'
              let cxt'' = updateCxt cxt' x pv
              pure [cxt'']
            _ -> error "splitCxt: impossible"
  _ -> error "splitCxt: impossible"

-- Check a list of clause lhs against a spine
-- If the spine can be matched by the patterns, return ()
-- If stucked, split the stucked variable of the spine.
-- If fails, move to next clause lhs.
testSpine :: Defs -> [ClauseLHS] -> Cxt -> Spine -> CoverRes
testSpine defs clss cxt sp = go clss where -- cxt |- sp 
  go = \case
    [] -> CoverFail [(cxt, sp)]
    (ps:rest) -> case match defs (env cxt) ps sp of
      MatchSuc _ -> CoverOk
      MatchFailed -> go rest -- move to next clause
      MatchStuck (BVar x) -> CoverStuck x
      _ -> error "impossible"

genSpine :: Cxt -> Spine -> Lvl -> Maybe [(Cxt, Spine)]
genSpine cxt sp l = do -- Maybe
  splitted_cxts <- splitCxt cxt l
  pure $ do -- Maybe
    cxt' <- splitted_cxts
    let sp' = updateSp cxt' sp
    pure (cxt', sp')

testManySpine :: Defs -> [ClauseLHS] -> [(Cxt, Spine)] -> Maybe [(Cxt, Spine)]
testManySpine defs clss = \case
  [] -> Just []
  (cxt, sp):rest -> case testSpine defs clss cxt sp of
    CoverOk -> testManySpine defs clss rest
    CoverStuck l -> do
      gen <- genSpine cxt sp l
      left <- forM gen $ \ (cxt', sp') ->
        testManySpine defs clss [(cxt', sp')]
      right <- testManySpine defs clss rest
      pure $ join left ++ right
    CoverFail sp' -> do
      right <- testManySpine defs clss rest
      pure $ sp' ++ right
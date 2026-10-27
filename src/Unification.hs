
module Unification (unify, unifyCxt) where

import Control.Exception
import Data.IORef
import GHC.IO (unsafePerformIO)

import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value
import Cxt.Type 
import Definition
import Cxt (showCxt, showVal)
import Debug.Trace (trace)

-- Unification
--------------------------------------------------------------------------------

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl             -- ^ size of Γ
  , cod :: Lvl             -- ^ size of Δ
  , ren :: IM.IntMap Lvl}  -- ^ mapping from Δ vars to Γ vars

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

liftN :: Int -> PartialRenaming -> PartialRenaming
liftN 0 pren = pren
liftN n pren = liftN (n - 1) (lift pren)

-- | @invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
invert :: HasGlobal => Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []             = pure (0, mempty)
      go (sp :> (t, _)) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: HasGlobal => MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goCls :: PartialRenaming -> Env -> Clause -> IO Clause
  goCls pren env c@(Clause ps rhs) = do 
    let (cnt, vs) = countVarPat (cod pren) c
    let pren' = liftN cnt pren
    rhs' <- go pren' (eval (map VVar vs ++ env) rhs)
    pure $ Clause ps rhs'
    
  goSp :: HasGlobal => PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []             = pure t
  goSp pren t (sp :> (u, i)) = App <$> goSp pren t sp <*> go pren u <*> pure i

  go :: HasGlobal => PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x i t  -> Lam x i <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x i a b -> Pi x i <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VType       -> pure Type
    VAbsurd t   -> Absurd <$> go pren t

    VFunc f sp  -> goSp pren (Call (funcName f)) sp
    VHold f sp  -> goSp pren (Call (funcName f)) sp
    VData f sp  -> goSp pren (Call (dataName f)) sp
    VCons f sp  -> goSp pren (Call (consName f)) sp
    VPathCons f sp -> goSp pren (Call (eqNameDef f)) sp
    -- VProp       -> pure Prop
    VPropTm     -> pure PropTm
    VPrim p sp  -> goSp pren (Prim p) sp
    VProj v x sp -> do 
      v' <- go pren v
      goSp pren (Proj v' x) sp



-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [Icit] -> Tm -> Tm
lams = go (0 :: Int) where
  go x []     t = t
  go x (i:is) t = Lam ("x"++show (x+1)) i $ go (x + 1) is t

--                    Γ      ?α         sp       rhs
solve :: HasGlobal => Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (reverse $ map snd sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

unifySp :: HasGlobal => Env -> Lvl -> Spine -> Spine -> IO ()
unifySp env l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
-- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp env l sp sp' >> unify env l t t'

  _                              -> throwIO UnifyError -- rigid mismatch error

-- TODO: Typed unification for irrelevance
-- unify :: Defs -> Env -> Lvl -> VTy -> Val -> Val -> IO ()
unify :: HasGlobal =>  Env -> Lvl -> Val -> Val -> IO ()
unify env l t u = case (force t, force u) of
    (VLam _ _ t , VLam _ _ t'    ) -> unify (VVar l:env) (l + 1) (t $$ VVar l) (t' $$ VVar l)
    (t          , VLam _ i t'    ) -> unify (VVar l:env) (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
    (VLam _ i t , t'             ) -> unify (VVar l:env) (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
    (VType      , VType          ) -> pure ()
    (VPi x i a b, VPi x' i' a' b') | i == i' -> unify env l a a' >> unify (VVar l:env) (l + 1) (b $$ VVar l) (b' $$ VVar l)
    (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp env l sp sp'
    (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp env l sp sp'
                                   -- TODO: | otherwise  -> solve' defs l m sp m' sp' 
    (VFlex m sp , t'             ) -> solve l m sp t'
    (t          , VFlex m' sp'   ) -> solve l m' sp' t
    (VFunc f sp , VFunc f' sp'   ) -> unifyFn (f, sp) (f', sp')
    (VHold f sp , VHold f' sp'   ) -> unifyFn (f, sp) (f', sp')
    (VFunc f sp , VHold f' sp'   ) -> unifyFn (f, sp) (f', sp') 
    (VHold f sp , VFunc f' sp'   ) -> unifyFn (f, sp) (f', sp')
    

    (VCons c sp , VCons c' sp'   ) | consName c == consName c' -> unifySp env l sp sp' 
    (VData d sp , VData d' sp'   ) | dataName d == dataName d' -> unifySp env l sp sp'

    (VPropTm    , _       ) -> pure ()
    (_          , VPropTm ) -> pure ()
    -- (VProp      , VProp   ) -> pure ()
    (VPrim Cast vs, t)
      | unsafePerformIO $ unifyCast vs t -> pure ()
    (t, VPrim Cast vs)
      | unsafePerformIO $ unifyCast vs t -> pure ()
    (VPrim Apd _, VPrim Apd _) -> pure () -- Fake prop irrelevence
    (VPrim p vs, VPrim p' vs')
      | p == p' -> unifySp env l vs vs'
    (VProj v x vs, VProj v' x' vs')
      | x == x' -> unify env l v v' >> unifySp env l vs vs'

    (t          , VFunc f  sp    ) -> unifyWithEvalFn t (f, sp)
    (VFunc f  sp, t              ) -> unifyWithEvalFn t (f, sp)
    (t          , VHold f  sp    ) -> unifyWithEvalFn t (f, sp)
    (VHold f  sp, t              ) -> unifyWithEvalFn t (f, sp)

    _                            -> throwIO UnifyError  -- rigid mismatch error
  where 
    unifyFn :: (FuncDef, Spine) -> (FuncDef, Spine) -> IO ()
    unifyFn (f, sp) (f', sp') | funcName f == funcName f' = unifySp env l sp sp'
                              | otherwise                 = throwIO UnifyError
    unifyWithEvalFn :: Val -> (FuncDef, Spine) -> IO ()
    unifyWithEvalFn t (f, sp) = case evalFun' env f sp of 
                                  Just v' -> unify env l t v'
                                  Nothing -> trace (show t ++ "\n" ++ funcName f ++ " " ++ show sp) $ throwIO UnifyError 
    unifyCast :: Spine -> Val -> IO Bool
    unifyCast vs@(reverse -> [(a, _), (b, _), (p, _), (x, _)]) t = do 
      b <- tryUnify env l a b 
      if b then 
        unify env l x t >> pure True
      else pure False
    unifyCast _ _ = pure False

-- | try unifying, if fails, restore the metacontext and return False
-- | TODO: We do not want to solve metas during trying unification, 
-- |       so we need bool arg in unify to control this
tryUnify :: HasGlobal =>  Env -> Lvl -> Val -> Val -> IO Bool
tryUnify env l t u = do 
  nm <- readIORef nextMeta
  mc <- readIORef mcxt
  (unify env l t u >> pure True) 
    `catch` \UnifyError -> do
      writeIORef nextMeta nm
      writeIORef mcxt mc
      pure False
    
unifyCxt :: HasGlobal => Cxt -> VTy -> Val -> Val ->  IO ()
unifyCxt cxt _ = unify (env cxt) (lvl cxt)
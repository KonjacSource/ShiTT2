
module Unification (unify, unifyCxt) where

import Control.Exception
import Data.IORef

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
invert :: Defs -> Lvl -> Spine -> IO PartialRenaming
invert defs gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []             = pure (0, mempty)
      go (sp :> (t, _)) = do
        (dom, ren) <- go sp
        case force defs t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: Defs -> MetaVar -> PartialRenaming -> Val -> IO Tm
rename defs m pren v = go pren v where

  goCls :: PartialRenaming -> Env -> Clause -> IO Clause
  goCls pren env c@(Clause ps rhs) = do 
    let (cnt, vs) = countVarPat (cod pren) c
    let pren' = liftN cnt pren
    rhs' <- go pren' (eval defs (map VVar vs ++ env) rhs)
    pure $ Clause ps rhs'
    
  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []             = pure t
  goSp pren t (sp :> (u, i)) = App <$> goSp pren t sp <*> go pren u <*> pure i

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force defs t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x i t  -> Lam x i <$> go (lift pren) ((defs, t) $$ VVar (cod pren))
    VPi x i a b -> Pi x i <$> go pren a <*> go (lift pren) ((defs, b) $$ VVar (cod pren))
    VU          -> pure U
    VAbsurd t   -> Absurd <$> go pren t

    VLamCase     env cls sp -> do 
      cls' <- mapM (goCls pren env) cls
      pure $ LamCase cls'
    VLamCaseHold env cls sp -> do 
      cls' <- mapM (goCls pren env) cls
      pure $ LamCase cls'

    VFunc f sp  -> goSp pren (Call (funcName f)) sp
    VHold f sp  -> goSp pren (Call (funcName f)) sp
    VData f sp  -> goSp pren (Call (dataName f)) sp
    VCons f sp  -> goSp pren (Call (consName f)) sp


-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [Icit] -> Tm -> Tm
lams = go (0 :: Int) where
  go x []     t = t
  go x (i:is) t = Lam ("x"++show (x+1)) i $ go (x + 1) is t

--               Γ      ?α         sp       rhs
solve :: Defs -> Lvl -> MetaVar -> Spine -> Val -> IO ()
solve defs gamma m sp rhs = do
  pren <- invert defs gamma sp
  rhs  <- rename defs m pren rhs
  let solution = eval defs [] $ lams (reverse $ map snd sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

solve' :: Defs -> Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
solve' defs gamma m sp m' sp' = do 
  catch (solve defs gamma m sp (VFlex m' sp'))
        (\UnifyError -> solve defs gamma m' sp' (VFlex m sp))

unifySp :: Defs -> Env -> Lvl -> Spine -> Spine -> IO ()
unifySp defs env l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
-- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp defs env l sp sp' >> unify defs env l t t'

  _                              -> throwIO UnifyError -- rigid mismatch error

unify :: Defs -> Env -> Lvl -> Val -> Val -> IO ()
unify defs env l t u = case (force defs t, force defs u) of
    (VLam _ _ t , VLam _ _ t'    ) -> unify defs (VVar l:env) (l + 1) ((defs, t) $$ VVar l) ((defs, t') $$ VVar l)
    (t          , VLam _ i t'    ) -> unify defs (VVar l:env) (l + 1) (vApp defs t (VVar l) i) ((defs, t') $$ VVar l)
    (VLam _ i t , t'             ) -> unify defs (VVar l:env) (l + 1) ((defs, t) $$ VVar l) (vApp defs t' (VVar l) i)
    (VU         , VU             ) -> pure ()
    (VPi x i a b, VPi x' i' a' b') | i == i' -> unify defs env l a a' >> unify defs (VVar l:env) (l + 1) ((defs, b) $$ VVar l) ((defs, b') $$ VVar l)
    (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp defs env l sp sp'
    (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp defs env l sp sp'
                                   -- TODO: | otherwise  -> solve' defs l m sp m' sp' 
    (VFlex m sp , t'             ) -> solve defs l m sp t'
    (t          , VFlex m' sp'   ) -> solve defs l m' sp' t
    (VFunc f sp , VFunc f' sp'   ) -> unifyFn (f, sp) (f', sp')
    (VHold f sp , VHold f' sp'   ) -> unifyFn (f, sp) (f', sp')
    (VFunc f sp , VHold f' sp'   ) -> unifyFn (f, sp) (f', sp') 
    (VHold f sp , VFunc f' sp'   ) -> unifyFn (f, sp) (f', sp')
    
    (t          , VFunc f  sp    ) -> unifyWithEvalFn t (f, sp)
    (VFunc f  sp, t              ) -> unifyWithEvalFn t (f, sp)
    (t          , VHold f  sp    ) -> unifyWithEvalFn t (f, sp)
    (VHold f  sp, t              ) -> unifyWithEvalFn t (f, sp)

    (VCons c sp , VCons c' sp'   ) | consName c == consName c' -> unifySp defs env l sp sp' 
    (VData d sp , VData d' sp'   ) | dataName d == dataName d' -> unifySp defs env l sp sp'
    _                            -> throwIO UnifyError  -- rigid mismatch error
  where 
    unifyFn :: (FuncDef, Spine) -> (FuncDef, Spine) -> IO ()
    unifyFn (f, sp) (f', sp') | funcName f == funcName f' = unifySp defs env l sp sp'
                              | otherwise                 = throwIO UnifyError
    unifyWithEvalFn :: Val -> (FuncDef, Spine) -> IO ()
    unifyWithEvalFn t (f, sp) = case evalFun' defs env f sp of 
                                  Just v' -> unify defs env l t v'
                                  Nothing -> trace (show t ++ "\n" ++ funcName f ++ " " ++ show sp) $ throwIO UnifyError 
unifyCxt :: Cxt -> Val -> Val ->  IO ()
unifyCxt cxt = unify (defs cxt) (env cxt) (lvl cxt)
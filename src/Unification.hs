
module Unification (unify, unifyCxt, unifyCxtTy, findType) where

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
import Cxt
import Definition
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
    VHold f sp _-> goSp pren (Call (funcName f)) sp
    VData f sp  -> goSp pren (Call (dataName f)) sp
    VCons f sp  -> goSp pren (Call (consName f)) sp
    VPathCons f sp -> goSp pren (Call (eqNameDef f)) sp
    VProp       -> pure Prop
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

trySolve :: HasGlobal => Lvl -> MetaVar -> Spine -> Val -> IO Bool 
trySolve gamma m sp rhs =
  (solve gamma m sp rhs >> pure True) 
    `catch` \UnifyError -> pure False

type UnifyConfig = (?unifyOrConv :: Bool, HasGlobal) -- True for unification, False for conversion

unifySp :: UnifyConfig => Cxt -> Spine -> Spine -> VTy -> IO ()
unifySp cxt sp sp' = go cxt (reverse sp) (reverse sp') where 
  go cxt [] [] _ = pure ()
  go cxt ((force -> t, _):us) ((force -> t', _):vs) (force -> VPi x i a b) = do 
    unify cxt t t' a 
    go cxt us vs (b $$ t) -- No need to go under the binder
  go cxt _ _ _ = throwIO UnifyError

unifyTy :: UnifyConfig => Cxt -> VTy -> VTy -> IO ()
unifyTy cxt a b = unify cxt a b VType

-- TODO: Typed unification for irrelevance
-- unify :: Defs -> Env -> Lvl -> VTy -> Val -> Val -> IO ()
unify :: UnifyConfig => Cxt -> Val -> Val -> VTy -> IO ()
unify cxt@Cxt{..} t u ty = do 
  case sortOf cxt ty of 
    Just SProp -> case (?unifyOrConv, force t, force u) of 
      (True, VFlex m sp, _) -> trySolve lvl m sp u >> pure ()
      (True, _, VFlex m sp) -> trySolve lvl m sp t >> pure ()
      _ -> pure ()
    Just SType -> unifyRelevant t u ty
    Nothing    -> unifyRelevant t u ty
  where
    unifyRelevant t u ty = case (force t, force u, force ty) of
      (VLam _ _ t , VLam _ _ t'    , VPi x _ a b) -> unify (bind cxt x a) (t $$ VVar lvl) (t' $$ VVar lvl) (b $$ VVar lvl)
      (t          , VLam _ i t'    , VPi x _ a b) -> unify (bind cxt x a) (vApp t (VVar lvl) i) (t' $$ VVar lvl) (b $$ VVar lvl)
      (VLam _ i t , t'             , VPi x _ a b) -> unify (bind cxt x a) (t $$ VVar lvl) (vApp t' (VVar lvl) i) (b $$ VVar lvl)
      (VType      , VType          , _) -> pure ()
      (VPi x i a b, VPi x' i' a' b', _) 
        | i == i' -> do
          unifyTy cxt a a'
          unifyTy (bind cxt x a) (b $$ VVar lvl) (b' $$ VVar lvl)
      (VRigid x sp, VRigid x' sp'  , _) | x == x' -> unifySp cxt sp sp' (findType cxt x)
      -- (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp env l sp sp' -- we need typed meta to support this
      (VFlex m sp  , t'             , _) | ?unifyOrConv -> solve lvl m sp t'
      (t           , VFlex m' sp'   , _) | ?unifyOrConv -> solve lvl m' sp' t
      (VFunc f sp  , VFunc f' sp'   , _) -> unifyFn (f, sp) (f', sp')
      (VHold f sp _, VHold f' sp' _ , _) -> unifyFn (f, sp) (f', sp')
      (VFunc f sp  , VHold f' sp'  _, _) -> unifyFn (f, sp) (f', sp') 
      (VHold f sp _, VFunc f' sp'   , _) -> unifyFn (f, sp) (f', sp')
      

      (VCons c sp , VCons c' sp'   , _) | consName c == consName c' -> unifySp cxt sp sp' (evalCxt cxt (consType c))
      (VData d sp , VData d' sp'   , _) | dataName d == dataName d' -> unifySp cxt sp sp' (evalCxt cxt (dataType d))

      (VPropTm    , _       , _) -> pure ()
      (_          , VPropTm , _) -> pure ()
      (VProp      , VProp   , _) -> pure ()
      (VPrim Cast vs, t     , _)
        | unsafePerformIO $ unifyCast vs t -> pure ()
      (t, VPrim Cast vs     , _)
        | unsafePerformIO $ unifyCast vs t -> pure ()
      (VPrim p vs, VPrim p' vs' , _)
        | p == p' -> unifySp cxt vs vs' (evalCxt cxt (getPrimTy p))
      (VProj v x vs, VProj v' x' vs', _)
        | x == x' -> undefined -- TODO

      (t          , VFunc f  sp    , ty) -> unifyWithEvalFn t (f, sp) ty
      (VFunc f  sp, t              , ty) -> unifyWithEvalFn t (f, sp) ty
      (t          , VHold f  sp _  , ty) -> unifyWithEvalFn t (f, sp) ty
      (VHold f  sp _, t            , ty) -> unifyWithEvalFn t (f, sp) ty

      _                            -> throwIO UnifyError  -- rigid mismatch error

    unifyFn :: (FuncDef, Spine) -> (FuncDef, Spine) -> IO ()
    unifyFn (f, sp) (f', sp') | funcName f == funcName f' = unifySp cxt sp sp' (evalCxt cxt (funcType f))
                              | otherwise                 = throwIO UnifyError
    unifyWithEvalFn :: Val -> (FuncDef, Spine) -> VTy -> IO ()
    unifyWithEvalFn t (f, sp) ty = case evalFun' env f sp of 
                                  Just v' -> unify cxt t v' ty
                                  Nothing -> trace (show t ++ "\n" ++ funcName f ++ " " ++ show sp) $ throwIO UnifyError 
    unifyCast :: Spine -> Val -> IO Bool
    unifyCast vs@(reverse -> [(a, _), (b, _), (p, _), (x, _)]) t = do 
      b <- conv cxt a b
      if b then 
        unify cxt x t ty >> pure True
      else pure False
    unifyCast _ _ = pure False

-- | try unifying, if fails, restore the metacontext and return False
-- | TODO: We do not want to solve metas during trying unification, 
-- |       so we need bool arg in unify to control this
conv :: HasGlobal => Cxt -> Val -> Val-> IO Bool
conv cxt t u = do
  let ?unifyOrConv = False 
  (unifyTy cxt t u >> pure True) 
    `catch` \UnifyError -> pure False
    
unifyCxt :: UnifyConfig => Cxt -> Val -> Val -> VTy -> IO ()
unifyCxt = unify

unifyCxtTy :: UnifyConfig => Cxt -> VTy -> VTy -> IO ()
unifyCxtTy = unifyTy

findType :: Cxt -> Lvl -> VTy
findType cxt (lvl2Ix (lvl cxt) -> unIx -> ix) = case types cxt !! ix of
  (_, _, a) -> a

-- 

-- TODO: Maybe we should change to Agda's El to store a type and its sort together
-- Returns Nothing if IDK or it is not a type
sortOf :: HasGlobal => Cxt -> VTy -> Maybe Sort 
sortOf cxt@Cxt{..} ty = case force ty of 
  VPi x i a b -> do 
    sortOf (bind cxt x a) (b $$ VVar lvl)
  VType -> Just SType
  VProp -> Just SType
  VRigid x sp -> sortOfApp cxt (findType cxt x) sp 
  VData d sp -> sortOfApp cxt (evalCxt cxt (dataType d)) sp
  VFunc f sp -> sortOfApp cxt (evalCxt cxt (funcType f)) sp
  VHold f sp _ -> sortOfApp cxt (evalCxt cxt (funcType f)) sp
  VCons c sp -> Nothing
  VPrim Oeq _ -> Just SProp
  VPrim Apd sp -> Nothing
  VPrim Cast sp -> Nothing
  VPrim Rfl sp -> Nothing
  VLam {} -> Nothing
  VPathCons {} -> Nothing 
  VPropTm -> Nothing
  VProj {} -> undefined -- TODO
  VAbsurd _ -> Nothing
  VFlex _ _ -> Nothing

sortOfApp :: HasGlobal => Cxt -> VTy -> Spine -> Maybe Sort
sortOfApp cxt ty sp = go (reverse sp) (force ty) where
  go [] ty = case force ty of 
    VType -> Just SType
    VProp -> Just SProp
    _     -> Nothing
  go ((v, i):sp) (force -> VPi x i' a b) | i == i' = go sp (b $$ v)
  go _ _ = Nothing

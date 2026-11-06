module Value where

import Common
import Syntax
import Definition
import qualified Data.Map as M

type Env     = [Val]
type Spine   = [(Val, Icit)]
type VTelescope = [(Name, Icit, VTy)]
type VTelescope' = [(Name, VTy)]
data Closure = Closure Env Tm deriving Show 

type VTy     = Val
data VType   = VEl { unVEl :: VTy, getVSort :: Sort } deriving Show

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VType {-# unpack #-} Closure Sort
  | VAbsurd Val
  | VFunc FuncDef Spine -- TODO: Change the FuncDefs to Name. Sometimes the FuncDef might be out of date.
  | VHold FuncDef Spine ~Reduced
  -- ^ Clauses are exhausted, but the function is still stucked. We store the meta variable if the function is stucked on a meta
  | VData DataDef Spine 
  | VCons ConsDef Spine
  | VPathCons EqConsDef Spine

  | VSort Sort
  | VPropTm 
  | VPrim Prim Spine ~Reduced

  | VSig Env Telescope' -- A closure
  | VMkSig [(Name, Val)]
  | VProj Val Name Spine
  deriving Show 

-- | We may have some values with computational rules, such as Oeq, Cast, etc
--   Force may trigger the computation of these primitives.
data Reduced
  = RReduced Val
  | RBlocked [MetaVar]
  | RNeutral -- ^ Neutral (including not fully applied)
  deriving Show

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []

pattern VType :: Val
pattern VType = VSort SType
pattern VProp :: Val
pattern VProp = VSort SProp

-- eqName : eqTel -> eqLhs =_{eqData eqIx} eqRhs
data EqCons = EqCons 
  { eqData :: DataDef 
  , eqName :: Name
  , eqTel  :: Telescope
  , eqLhs  :: Tm 
  , eqRhs  :: Tm 
  , eqIx   :: TSpine
  } deriving Show

eqCons2Defs :: EqCons -> EqConsDef
eqCons2Defs EqCons{..} = EqConsDef 
  { eqNameDef = eqName
  , eqDataDef = eqData
  , eqTypeDef = goPi eqTel $ mkEq eqLhs eqRhs eqIx
  } where 
    goPi :: Telescope -> Tm -> Tm
    goPi [] t = t
    goPi ((x, i, a):rest) t = Pi x i a (mkProp (goPi rest t))
    mkEq :: Tm -> Tm -> TSpine -> Tm 
    mkEq lhs rhs sp = applySp (Prim Oeq) [(applySp (Call (dataName eqData)) sp, Impl), (lhs, Expl), (rhs, Expl)]

instance SortOf VType where
  sortOf (VEl _ s) = s

blockers :: Val -> [MetaVar]
blockers = \case
  VFlex m _               -> [m]
  VHold _ _ (RBlocked ms) -> ms
  VPrim _ _ (RBlocked ms) -> ms
  VProj v _ _             -> blockers v
  _                       -> []
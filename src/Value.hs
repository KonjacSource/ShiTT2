module Value where

import Common
import Syntax
import Definition
import qualified Data.Map as M

type Env     = [Val]
type Spine   = [(Val, Icit)]
data Closure = Closure Env Tm deriving Show 
type VTy     = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VTy {-# unpack #-} Closure
  | VU
  | VAbsurd Val
  | VFunc FuncDef Spine -- TODO: Change the FuncDefs to Name. Sometimes the FuncDef might be out of date.
  | VHold FuncDef Spine -- Clauses are exhausted, but the function is still stucked (a neutral term forever)
  | VData DataDef Spine 
  | VCons ConsDef Spine
  | VPathCons EqConsDef Spine

  -- | VProp 
  | VPropTm 
  | VPrim Prim Spine 
  | VProj Val Name Spine
  deriving Show 

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []

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
    goPi ((x, i, a):rest) t = Pi x i a (goPi rest t)
    mkEq :: Tm -> Tm -> TSpine -> Tm 
    mkEq lhs rhs sp = applySp (Prim Oeq) [(applySp (Call (dataName eqData)) sp, Impl), (lhs, Expl), (rhs, Expl)]

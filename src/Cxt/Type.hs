module Cxt.Type where 

import Common
import Value
import qualified Data.Map as M
import Data.Set
import Syntax
import Definition


-- Elaboration context
-------------------------- 

data NameOrigin = Inserted | Source deriving Eq
type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt              -- used for:
  ----------------------------------------------------------------
  { env    :: Env           -- evaluation
  , lvl    :: Lvl           -- unification
  , types  :: Types         -- raw name lookup, pretty printing
  , bds    :: [BD]          -- fresh meta creation
  , pos    :: SourcePos     -- error reporting
  , defs   :: Defs
  , qitInfo:: QITInfo
  }

-- opening apd clauses, indexed by the function name
type OpnCls = M.Map Name [ApdCls]

-- apd (f ps) {x, y} e = ...
data ApdCls = ApdCls
  { apdCxt   :: Cxt               -- the context including the variables bound in `ps`, `x`, `y`, and `e`
  , apdPat   :: PatternTele Empty -- the pattern `(f ps, {x, y}, e)`, every user clause must be matchable in here
  , apdSpn   :: Spine             -- the spine applying to apd, `(f ps, {x, y}, e)`, user clauses must cover this spine
  , apdRhsTy :: Cxt -> (VTy, Closure, Val, Val, Val, Val) -> VTy 
  -- ^ HOAS, input the context and values of user provided `A`, `B`, `f ps`, `x`, `y`, and `e`, 
  -- These values have nothing to do with apdCxt
  }

-- eqName : eqTel -> eqLhs =_{eqData eqIx} eqRhs
data EqCons = EqCons 
  { eqData :: DataDef 
  , eqName :: Name
  , eqTel  :: Telescope
  , eqLhs  :: Tm 
  , eqRhs  :: Tm 
  , eqIx   :: TSpine
  }

type Defs = M.Map Name Def
data QITInfo = QITInfo
  { apdCls :: M.Map Name (FuncDef, [Pattern], Pattern)
                            -- apd is defined for `apd (f xs) e`
  , extraEq:: M.Map Name EqCons
                            -- path constructors given by QITs, indexed by the name of the path constructor
  -- TODO: extraEq' :: M.Map Name [EqCons] -- indexed by the name of the QIT, this is necessary
  }
module Cxt.Type where 

import Common
import Value
import qualified Data.Map as M
import Data.Set
import Syntax
import Definition
import GHC.Stack
import Data.IORef


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
  }

-- opening apd clauses, indexed by the function name
type OpnCls = M.Map Name [ApdCls]

-- apd (f ps) {x, y} e = ...
data ApdCls = ApdCls
  { apdCxt   :: Cxt               -- the context including the variables bound in `ps`, `x`, `y`, and `e`
  , apdPat   :: PatternTele Empty -- the pattern `(f ps, {x, y}, e)`, every user clause must be matchable in here
  , apdSpn   :: Spine             -- the spine applying to apd, `(f ps, {x, y}, e)`, user clauses must cover this spine
  }

type Defs = M.Map Name Def
data QITInfo = QITInfo
  { apdCls :: M.Map Name (FuncDef, [Pattern], Pattern) -- apd is defined for `apd (f xs) e`
  , extraEq :: M.Map Name EqCons -- path constructors given by QITs, indexed by the name of the path constructor
  , extraEq' :: M.Map Name [EqCons] -- indexed by the name of the QIT
  , definedApd :: M.Map Name [PatternTele Empty] -- for which (f ps, {x, y}, e) apd is defined, indexed by the name of `f`
  , apdClauses :: M.Map Name [Clause] -- TODO: use this field to store the apd clauses, so that we can check the termination
  }

type HasGlobal = (?defs :: Defs, ?qitInfo :: QITInfo, HasCallStack)

withDefs :: (?qitInfo :: QITInfo) => Defs -> (HasGlobal => a) -> a
withDefs defs act = let ?defs = defs in act

withQITI :: (?defs :: Defs) => QITInfo -> (HasGlobal => a) -> a
withQITI qiti act = let ?qitInfo = qiti in act

withGlobal :: Defs -> QITInfo -> (HasGlobal => a) -> a
withGlobal defs qiti act = let ?defs = defs; ?qitInfo = qiti in act

withGlobal' :: IORef (Defs, QITInfo) -> (HasGlobal => IO a) -> IO a
withGlobal' defsR act = do
  (defs, qiti) <- readIORef defsR
  let ?defs = defs
      ?qitInfo = qiti
  act 


insertEqCon :: EqCons -> QITInfo -> QITInfo
insertEqCon eqcons qiti = 
  qiti { extraEq  = M.insert (eqName eqcons) eqcons (extraEq qiti)
       , extraEq' = insertItem (dataName (eqData eqcons)) eqcons (extraEq' qiti) }

insertApd :: Name -> PatternTele Empty -> Clause -> QITInfo -> QITInfo
insertApd f ps cls qiti = 
  qiti { definedApd = insertItem f ps (definedApd qiti)
       , apdClauses = insertItem f cls (apdClauses qiti) }

isQITCon :: HasGlobal => Name -> Bool
isQITCon c = M.member c (extraEq ?qitInfo)


module Definition where

import Common
import Syntax
import qualified Presyntax as R

data Def
  = DefFunc FuncDef
  | DefData DataDef
  | DefCons ConsDef
  | DefEq   EqConsDef
  deriving Show 

data ConsDef = ConsDef
  { consName :: Name 
  , consData :: DataDef -- ^ Datatype which the constructor belongs to.
  , consType :: Ty -- ^ The type of the constructor.
  } 

data EqConsDef = EqConsDef
  { eqNameDef :: Name
  , eqDataDef :: DataDef -- ^ Datatype which the constructor belongs to.
  , eqTypeDef :: Ty -- ^ The type of the constructor.
  }

data FuncDef = FuncDef
  { funcName :: Name
  , funcType :: Type -- ^ Type of the function
  , funcClauses :: [Clause] 
  -- TODO: change this to a Defs lookup function, because this field might be out of date when we using interleaved functions
  } 

data DataDef = DataDef
  { dataName :: Name 
  , dataIx   :: Telescope
  , dataCons :: [(Name, Telescope, TSpine)]
  -- ^ List of (Name of constructor, Arguments list, The returning indexes), 
  -- Note that the returning indexes is under the context of the arguments list. 
  , isQIT    :: Bool
  }

instance Show ConsDef where 
  show = consName

instance Show EqConsDef where 
  show = eqNameDef

instance Show FuncDef where 
  show = funcName
  
instance Show DataDef where 
  show = dataName

lookupCons :: DataDef -> Name -> Maybe (Telescope, TSpine)
lookupCons (DataDef d _ cons _) c = go cons where 
  go [] = Nothing
  go ((c', ts, ix):rest) 
    | c' == c = pure (ts, ix)
    | otherwise = go rest

-- We only have inductive types, not propositions, so it is always a type.
-- TODO: Universe level
getConsType :: DataDef -> Telescope -> TSpine -> Ty
getConsType d [] ix = applySp (Call $ dataName d) ix
getConsType d ((x, i, t):ts) ix = Pi x i t $ mkType $ getConsType d ts ix 

getPathConType :: DataDef -> Telescope -> TSpine -> Tm -> Tm -> Ty
getPathConType d [] ix lhs rhs = applySp (Prim Oeq) [(applySp (Call $ dataName d) ix, Impl), (lhs, Expl), (rhs, Expl)]
getPathConType d ((x, i, t):ts) ix lhs rhs = Pi x i t $ mkProp $ getPathConType d ts ix lhs rhs

dataType :: DataDef -> Ty 
dataType d = go (dataIx d) where 
  go [] = Type 
  go ((x,i,t):ts) = Pi x i t (mkType $ go ts)

class Arity f where 
  arity :: f -> Int 

instance Arity Clause where 
  arity = length . clausePatterns

instance Arity a => Arity [a] where 
  arity [] = 0
  arity (x:_) = arity x

instance Arity FuncDef where 
  arity f = arity (funcClauses f)

data RFuncDef = RFuncDef
  { funcNameR :: Name
  , funcTypeR :: R.Tm -- ^ Type of the function
  , funcClausesR :: [R.RClause]
  }

type RTelescope = [(Name, Icit, R.Tm)]

data RDataDef = RDataDef
  { dataNameR :: Name
  , dataIxR :: R.Tm
  , dataConsR :: [(Name, R.Tm)]
  , isQITR :: Bool 
  } deriving Show 

-- def apd 
-- | (f ps) e = rhs
data RApdDef = RApdDef
  { apdFuncNameR :: Name   -- ^ f
  , apdClausesR :: [RApdClause] -- ^ | (f ps) e = rhs
  }

-- | (f ps) {x} {y} e = rhs
data RApdClause = RApdClause
  { apdPatR1 :: R.RPattern  -- ^ f ps
  , apdPatR2 :: R.RPatterns -- ^ {x} {y} e
  , apdRhsR  :: R.Tm        -- ^ rhs
  }

data Header 
  = FunHeader Name R.Tm 
  | DataHeader Name Bool R.Tm -- true for qit
  deriving Show 

data Body = FunBody Name [R.RClause] | DataBody Name [(Name, R.Tm)]

data RMutalBlock = RMutalBlock
  { mutualSig  :: [(SourcePos, Header)]
  , mutualBody :: [(SourcePos, Body)]
  }

data RDef 
  = RDefData   RDataDef     -- ^ data
  | RDefFunc   RFuncDef     -- ^ def 
  | RDefApd    RApdDef      -- ^ def apd
  | RDefMutual RMutalBlock  -- ^ mutual
  | RCommand   Command      -- ^ #..

data Command 
  = CmdPrint R.Tm               -- ^ #print
  | CmdCheck R.Tm (Maybe R.Tm)  -- ^ #check 
  | CmdFail  RDef               -- ^ #fail

type Program = [(SourcePos, RDef)]

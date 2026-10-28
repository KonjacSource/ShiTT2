module Syntax where

import Common
import qualified Data.Map as M

data Clause = Clause
  { clausePatterns :: PatternTele Empty
  , clauseRhs :: Tm
  } deriving Show

-- | Type argument `a` should be `Empty` for normal pattern or `()` for pattern with mark
data Pattern' a 
  = PatVar Name
  | PatCon Name (PatternTele a)
  | PatFunc Name (PatternTele a) -- apd (f ps) e
  | PatMark a
  deriving (Functor, Show)

type PatternArg a = (Pattern' a, Icit)
type PatternTele a = [PatternArg a]
type Pattern = Pattern' Empty
type PatternWithMark = Pattern' () 

toPatternWithMark :: Pattern -> PatternWithMark
toPatternWithMark = fmap exfalso

noMark :: PatternWithMark -> Maybe Pattern
noMark = \case
  PatMark () -> Nothing
  PatVar x -> Just $ PatVar x
  PatCon c ps -> PatCon c <$> mapM (\(p, i) -> (,) <$> noMark p <*> pure i) ps
  PatFunc f ps -> PatFunc f <$> mapM (\(p, i) -> (,) <$> noMark p <*> pure i) ps

data Empty 
exfalso :: Empty -> a
exfalso = \case

instance Show Empty where 
  show = exfalso

type Ty = Tm

data Tm
  = Var Ix
  | Call Id -- ^ Call functions or datatypes or constructor
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | Type
  | Absurd Tm
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]

  | Prop 
  | PropTm -- A term of a proposition type
  | Prim Prim
  | Proj Tm Name
  deriving Show

data Prim 
  = Apd
  -- apd {A : U} {B : A → U} {x y : A} : (f : (x : A) → B x) (h : x = y) → cast (B x) (B y) (apU B h) (f x) = f y 
  | Cast
  -- cast [A B : U] (p : A = B) (a : A) : B
  | Oeq
  -- eq {A : U} (x y : A) : U
  | Rfl
  -- rfl {A : U} (x : A) : x ~{A} x
  deriving (Show, Eq)

data Sort = SType | SProp deriving (Show, Eq)

imax :: Sort -> Sort -> Sort
imax SType SType = SType
imax SProp SType = SType
imax _     SProp = SProp

max1 :: Sort -> Sort -> Sort
max1 SType SType = SType
max1 SProp SType = SType
max1 SType SProp = SType
max1 SProp SProp = SProp

max :: [Sort] -> Sort
max = foldr max1 SProp

-- to control the type of cast
-- cast (A B : U) (p : A = B) (a : A) : B
-- or
-- cast {A B : U} (p : A = B) (a : A) : A
casticit :: Icit
casticit = Impl

eApp :: Tm -> Tm -> Tm
eApp t u = App t u Expl

iApp :: Tm -> Tm -> Tm
iApp t u = App t u Impl

noMetas :: Tm -> Bool
noMetas = \case
  Var _ -> True
  Call _ -> True
  Lam _ _ t -> noMetas t
  App t u _ -> noMetas t && noMetas u
  Type -> True
  Absurd _ -> True
  Pi _ _ a b -> noMetas a && noMetas b
  Let _ a t u -> noMetas a && noMetas t && noMetas u
  Meta _ -> False
  InsertedMeta _ _ -> False
  
  Prop -> True
  PropTm -> True 
  Prim _ -> True
  Proj t _ -> noMetas t


-- f x y z = applySp f [(x, _), (y, _), (z, _)]
type TSpine = [(Tm, Icit)]

applySp :: Tm -> TSpine -> Tm
applySp = foldl (\t (u, i) -> App t u i)

-- Primitive's Type

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
-- Note: cast for prop can be safely postulated.
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

oeqTy :: Ty
oeqTy = Pi "A" Impl Type $
        Pi "x" Expl (Var 0) $
        Pi "y" Expl (Var 1) $
        Prop

getPrimTy :: Prim -> Ty
getPrimTy = \case
  Apd -> apdTy
  Cast -> castTy
  Rfl -> rflTy
  Oeq -> oeqTy
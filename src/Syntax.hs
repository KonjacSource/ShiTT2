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
data Type = El { unEl :: Ty, getSort :: Sort } deriving Show
mkType t = El t SType
mkProp t = El t SProp

data Tm
  = Var Ix
  | Call Id -- ^ Call functions or datatypes or constructor
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | Absurd Tm
  | Pi Name Icit Type Type
  | Let Name Type Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]

  | TmSort Sort
  | PropTm -- ^ A term of a proposition type
  | Prim Prim

  | Sig Telescope' 
  -- ^ n-sigma type, sig {x : A; y : B x; z : C x y}
  | MkSig [(Name, Tm)]
  | Proj Tm Name
  deriving Show

pattern Type :: Tm
pattern Type = TmSort SType

pattern Prop :: Tm
pattern Prop = TmSort SProp

data Prim 
  = Apd
  -- apd {A : U} {B : A → U} {x y : A} : (f : (x : A) → B x) (h : x = y) → cast (B x) (B y) (apU B h) (f x) ~ f y 
  | Cast
  -- cast [A B : U] (p : A = B) (a : A) : B
  | Oeq
  -- eq {A : U} (x y : A) : Prop
  | Rfl
  -- rfl {A : U} (x : A) : x ~{A} x
  deriving (Show, Eq)

type Telescope = [(Name, Icit, Type)]
type Telescope' = [(Name, Type)]

data Sort = SType | SProp | SMeta SMetaVar | IMax Sort Sort | UMax [Sort] | Suc Sort
  deriving (Show, Eq)

-- | Pick a field, return the telescope of previous fields and the type of the field
fieldType :: Telescope' -> Name -> Maybe (Telescope', Type)
fieldType ts n = go [] n ts where 
  go acc n [] = Nothing 
  go acc n ((x, t):ts) 
    | x == n = Just (reverse acc, t)
    | otherwise = go ((x, t):acc) n ts

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

class NoMetas a where
  noMetas :: a -> Bool

instance NoMetas Tm where
  noMetas = \case
    Var _ -> True
    Call _ -> True
    Lam _ _ t -> noMetas t
    App t u _ -> noMetas t && noMetas u
    Absurd _ -> True
    Pi _ _ a b -> noMetas a && noMetas b
    Let _ a t u -> noMetas a && noMetas t && noMetas u
    Meta _ -> False
    InsertedMeta _ _ -> False
    TmSort s -> noMetas s
    PropTm -> True 
    Prim _ -> True
    Sig tys -> all (noMetas . snd) tys
    MkSig ts -> all (noMetas . snd) ts
    Proj t _ -> noMetas t

instance NoMetas Sort where
  noMetas = \case
    SType -> True
    SProp -> True
    SMeta _ -> False
    IMax s1 s2 -> noMetas s1 && noMetas s2
    UMax ss -> all noMetas ss
    Suc s -> noMetas s

instance NoMetas Type where 
  noMetas (El t _) = noMetas t

-- f x y z = applySp f [(x, _), (y, _), (z, _)]
type TSpine = [(Tm, Icit)]

applySp :: Tm -> TSpine -> Tm
applySp = foldl (\t (u, i) -> App t u i)

-- Primitive's Type
apdTy :: Type
apdTy = mkProp $
        Pi "A" Impl (mkType Type) $ mkProp $
        Pi "B" Impl (mkType $ Pi "_" Expl (mkType $ Var 0) (mkType Type)) $ mkProp $
        Pi "x" Impl (mkType $ Var 1) $ mkProp $
        Pi "y" Impl (mkType $ Var 2) $ mkProp $
        Pi "f" Expl (mkType $ Pi "x" Expl (mkType $ Var 3) (mkType $ App (Var 3) (Var 0) Expl)) $ mkProp $
        Pi "h" Expl (mkProp $ applySp (Prim Oeq) [(Var 4, Impl), (Var 2, Expl), (Var 1, Expl)]) $
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
        in mkProp $ applySp (Prim Oeq) [(eApp b y, Impl), (lhs, Expl), (rhs, Expl)]

-- cast : [A B : U] → A ~{U} B → A → B
-- Note: cast for prop can be safely postulated.
castTy :: Type
castTy = mkType $ 
         Pi "A" casticit (mkType Type) $ mkType $
         Pi "B" casticit (mkType Type) $ mkType $ 
         Pi "_" Expl (mkProp $ applySp (Prim Oeq) [(Type, Impl), (Var 1, Expl), (Var 0, Expl)]) $ mkType $ 
         Pi "_" Expl (mkType $ Var 2) $ mkType $
         Var 2

rflTy :: Type
rflTy = mkProp $ 
        Pi "A" Impl (mkType Type) $ mkProp $ 
        Pi "x" Expl (mkType $ Var 0) $ mkProp $ 
        applySp (Prim Oeq) [(Var 1, Impl), (Var 0, Expl), (Var 0, Expl)]

oeqTy :: Type
oeqTy = mkType $ 
        Pi "A" Impl (mkType Type) $ mkType $ 
        Pi "x" Expl (mkType $ Var 0) $ mkType $
        Pi "y" Expl (mkType $ Var 1) $ mkType $
        Prop

getPrimTy :: Prim -> Type
getPrimTy = \case
  Apd -> apdTy
  Cast -> castTy
  Rfl -> rflTy
  Oeq -> oeqTy

travTm :: (Tm -> Tm) -> Tm -> Tm
travTm f = f . go where
  go = \case
    Var x -> Var x
    Call f -> Call f
    Lam x i t -> Lam x i (go t)
    App t u i -> App (go t) (go u) i
    Absurd t -> Absurd (go t)
    Pi x i (El a as) (El b bs) -> Pi x i (El (go a) as) (El (go b) bs)
    Let x (El a as) t u -> Let x (El (go a) as) (go t) (go u)
    Meta m -> Meta m
    InsertedMeta m bds -> InsertedMeta m bds

    TmSort s -> TmSort s
    PropTm -> PropTm
    Prim p -> Prim p
    Sig tys -> Sig $ map (\(x, El t s) -> (x, El (go t) s)) tys
    MkSig ts -> MkSig $ map (\(x, t) -> (x, go t)) ts
    Proj t x -> Proj (go t) x

class SortOf a where
  sortOf :: a -> Sort 

instance SortOf Type where
  sortOf (El _ s) = s



module Syntax where

import Common

data Clause = Clause
  { clausePatterns :: [(Pattern, Icit)]
  , clauseRhs :: Tm
  } deriving Show

data Pattern
  = PatVar Name
  | PatCon Name [(Pattern, Icit)]
  deriving Show

type Ty = Tm

data Tm
  = Var Ix
  | Call Id -- ^ Call functions or datatypes or constructor
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | U
  | Absurd Tm
  | LamCase [Clause]
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]
  deriving Show

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
  U -> True
  Absurd _ -> True
  LamCase cls -> all (\(Clause ps rhs) -> noMetas rhs) cls
  Pi _ _ a b -> noMetas a && noMetas b
  Let _ a t u -> noMetas a && noMetas t && noMetas u
  Meta _ -> False
  InsertedMeta _ _ -> False

type TSpine = [(Tm, Icit)]

applySp :: Tm -> TSpine -> Tm
applySp = foldl (\t (u, i) -> App t u i)

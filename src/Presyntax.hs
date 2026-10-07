
module Presyntax where

import Common

data Tm
  = Var Name                       -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit)   -- t u  | t {u} | t {x = u}
  | U                              -- U
  | Absurd Tm                      -- absurd x
  | Pi Name Icit Tm Tm             -- (x : A) -> B | {x : A} -> B
  | Let Name Tm Tm Tm              -- let x : A = t; u
  | SrcPos SourcePos Tm            -- source position for error reporting
  | Hole                           -- _
  | PrintCxt Tm                    -- printcxt[Tm]
  -- | Prop                           -- Prop
  | Cast                           -- cast
  | Apd                            -- apd
  | Oeq Tm Tm Tm                   -- a ~{A} b, or a ~ b for a ~{_} b
  | Rfl                            -- rfl {A : U} (x : A) : x ~{A} x
  deriving Show

-- | Get rid of source positions, for better debug printing.
stripPos :: Tm -> Tm
stripPos = \case
  Var x        -> Var x
  Lam x i t -> Lam x i (stripPos t)
  App t u i    -> App (stripPos t) (stripPos u) i
  U            -> U
  Absurd x     -> Absurd (stripPos x)
  Pi x i a b   -> Pi x i (stripPos a) (stripPos b)
  Let x a t u  -> Let x (stripPos a) (stripPos t) (stripPos u)
  SrcPos _ t   -> stripPos t
  Hole         -> Hole
  PrintCxt t   -> PrintCxt (stripPos t)
  -- Prop         -> Prop  
  Cast         -> Cast
  Apd          -> Apd
  Rfl          -> Rfl
  Oeq a b c    -> Oeq (stripPos a) (stripPos b) (stripPos c)

data RClause = RClause
  { clausePatternsR :: RPatterns
  , clauseRhsR :: Tm
  } deriving Show

data RPattern = RPat Name RPatterns deriving Show
type RPatterns = [(Either Name Icit, RPattern)]

type Spine = [(Tm, Either Name Icit)]

flattenApp :: Tm -> (Tm, Spine)
flattenApp t = go t [] where
  go (App t u i) args = go t ((u, i) : args)
  go (SrcPos _ t) args =  go t args
  go (PrintCxt t) args =  go t args
  go t args           = (t, args)

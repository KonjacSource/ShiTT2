
module Pretty (prettyTm, showTm0, displayMetas, showDefs) where

import Control.Monad
import Data.IORef
import Text.Printf

import qualified Data.IntMap.Strict as IM

import Common
import Evaluation
import Metacontext
import Syntax
import Cxt.Type
import GHC.Stack (HasCallStack)
import Definition
    ( DataDef(dataName),
      FuncDef(funcName),
      EqConsDef(eqNameDef),
      ConsDef(consName),
      Def(DefEq, DefFunc, DefData, DefCons) )
import qualified Data.Map as M

--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Float -- U, var
appp  = 2  :: Float -- application
eqp = 1.5 :: Float
pip   = 1  :: Float -- pi
letp  = 0  :: Float -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Float -> Float -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: HasCallStack => Float -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  bracket :: ShowS -> ShowS
  bracket ss = ('{':).ss.('}':)

  piBind ns x Expl a = showParen True ((x++) . (" : "++) . go letp ns a)
  piBind ns x Impl a = bracket        ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = bracket (x++)
  lamBind x Expl = (x++)

  goBDS :: Float -> [Name] -> MetaVar -> [BD] -> ShowS
  goBDS p ns m bds = case (ns, bds) of
    ([]      , []             ) -> (("?"++show m)++)
    (ns :> n , bds :> Bound   ) -> par p appp $ goBDS appp ns m bds . (' ':) . (n++)
    (ns :> n , bds :> Defined ) -> goBDS appp ns m bds
    _                           -> error "impossible"

  sepBy :: String -> [ShowS] -> ShowS
  sepBy _   []     = id
  sepBy sep (s:ss) = s . foldr (\s' acc -> (sep++) . s' . acc) id ss

  go :: HasCallStack => Float -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)   | x >= 0     -> ((ns !! x)++)
                 | otherwise  -> (("<"++ show x ++ ">")++)
    App (App (App (Prim Oeq) ty Impl) a Expl) b Expl
                              -> par p eqp $ go appp ns a . (" ~"++) . bracket (go letp ns ty) . (' ':) . go appp ns b
    App t u Expl              -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl              -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (fresh ns -> x) i t   -> par p letp $ ("λ "++) . lamBind x i . goLam (ns:>x) t where
                                   goLam ns (Lam (fresh ns -> x) i t) =
                                     (' ':) . lamBind x i . goLam (ns:>x) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    Absurd t                      -> par p appp $ ("absurd "++) . go atomp ns t
    Pi "_" Expl (El a _) (El b _) -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) i (El a as) b -> par p pip $ piBind ns x i a . goPi (ns:>x) b where
                                   goPi ns (El (Pi (fresh ns -> x) i (El a _) b) _)
                                     | x /= "_" = piBind ns x i a . goPi (ns:>x) b
                                   goPi ns (El b _) = (" → "++) . go pip ns b

    Let (fresh ns -> x) (El a _) t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m bds        -> goBDS p ns m bds
    Call f                    -> (f ++)
    Type                      -> ("U"++)
    Prop                      -> ("Prop"++)
    TmSort _                  -> ("Sort?"++) -- TODO
    PropTm                    -> (".." ++)
    Prim p                    -> (show p ++)
    Proj t x                  -> par p atomp $ go atomp ns t . ((" ."++x)++) 
    Sig tys                   -> ("sig {"++) . goTele ns tys . ('}':) where
                                   goTele ns []           = id
                                   goTele ns [(x, El a _)]     = field ns x a
                                   goTele ns ((x, El a _):tys) = field ns x a . ("; "++) . goTele (ns :> fresh ns x) tys
                                   field ns x a = (x++) . (" : "++) . go letp ns a
    MkSig ts                  -> ('<':) . sepBy "; " [ (x++) . (" := "++) . go letp ns t | (x, t) <- ts ] . ('>':)

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

displayMetas :: HasGlobal => IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved -> printf "let ?%s = ?;\n" (show m)
    Solved v -> printf "let ?%s = %s;\n" (show m) (showTm0 $ quote 0 v)
  putStrLn ""

showDefs :: HasGlobal => String 
showDefs = unlines $ map showDef (M.toList ?defs) where
  showDef (fname, def) = case def of
    DefFunc f -> "def " ++ funcName f
    DefData d -> "data " ++ dataName d
    DefCons c -> "constructor " ++ consName c
    DefEq eq  -> "eq " ++ eqNameDef eq
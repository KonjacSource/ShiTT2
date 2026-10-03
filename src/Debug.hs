{-# LANGUAGE GADTs #-}

module Debug where 
import Debug.Trace (trace)
import Cxt.Type

isDebug :: Bool
isDebug = True

class ShowUnderCxt a where 
  showUnderCxt :: Cxt -> a -> String

data Ex = forall a . ShowUnderCxt a => Ex a 

debug :: Cxt -> [Ex] -> ()
debug cxt | isDebug = \case 
  [] -> () 
  (Ex x:xs) -> trace (showUnderCxt cxt x) $ debug cxt xs
debug _ = const () 

module Common (
    module Common
  , SourcePos(..)
  , Pos
  , unPos
  , initialPos) where

import Text.Megaparsec
import Control.Exception
import GHC.IO (unsafePerformIO)
import qualified Data.Map as M

type Name = String
type Id = String
data Icit = Impl | Expl deriving (Eq)
data BD = Bound | Defined deriving Show

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}

-- Throwable Maybe 
-------------------

instance Exception () where 

might :: IO a -> Maybe a 
might action = unsafePerformIO $ (action >>= pure . Just) `catch` \() -> pure Nothing

quitMight :: IO a 
quitMight = throwIO ()

insertItem :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
insertItem k v m = if M.member k m then
  M.adjust (v :) k m
else 
  M.insert k [v] m

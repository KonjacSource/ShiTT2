
module Metacontext where

import Data.IORef
import System.IO.Unsafe

import qualified Data.IntMap as IM

import Common
import Value
import Cxt.Type
import GHC.Stack (HasCallStack)
import Text.Printf (printf)
import qualified Data.Map as M
import Control.Monad (forM_)

--------------------------------------------------------------------------------

data MetaEntry = Solved Val | Unsolved
  deriving Show

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: HasCallStack => MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error $ "impossible: " ++ show m 

opnCls :: IORef OpnCls
opnCls = unsafeDupablePerformIO $ newIORef M.empty
{-# noinline opnCls #-}

insertCls :: Name -> ApdCls -> IO ()
insertCls fname = modifyIORef opnCls . insertItem fname 

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

allSolved :: IO Bool 
allSolved = do
  ms <- readIORef mcxt
  pure $ IM.null $ IM.filter (\case Solved _ -> False; Unsolved -> True) ms

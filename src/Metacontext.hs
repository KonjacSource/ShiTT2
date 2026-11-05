
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
import Syntax

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

data SMetaEntry = SSolved Sort | SUnsolved
  deriving Show

nextSMeta :: IORef Int
nextSMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextSMeta #-}

smcxt :: IORef (IM.IntMap SMetaEntry)
smcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline smcxt #-}

lookupSMeta :: HasCallStack => SMetaVar -> SMetaEntry
lookupSMeta (SMetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef smcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error $ "impossible: " ++ show m

opnCls :: IORef OpnCls
opnCls = unsafeDupablePerformIO $ newIORef M.empty
{-# noinline opnCls #-}

insertCls :: Name -> ApdCls -> IO ()
insertCls fname = modifyIORef opnCls . insertItem fname

removeCls :: Name -> IO ()
removeCls = modifyIORef opnCls . M.delete

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty
  writeIORef nextSMeta 0
  writeIORef smcxt mempty
  writeIORef opnCls M.empty


allSolved :: IO Bool
allSolved = do
  ms <- readIORef mcxt
  mss <- readIORef smcxt
  pure $ IM.null (IM.filter (\case Solved _ -> False; Unsolved -> True) ms)
      && IM.null (IM.filter (\case SSolved _ -> False; SUnsolved -> True) mss)

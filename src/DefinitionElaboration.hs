module DefinitionElaboration where

import qualified Presyntax as R
import Presyntax (RClause(..), RPattern(..), RPatterns)
import Common
import Syntax
import Value
import Definition
import qualified Elaboration as E
import Evaluation
import Cxt
import Cxt.Type
import qualified Data.Map.Strict as M
import Errors
import Control.Exception
import Control.Monad (forM, when, unless, join, forM_)
import GHC.Stack (HasCallStack)
import Pretty (displayMetas)
import Data.IORef (readIORef)
import Metacontext (nextMeta)
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)

checkFunc1 :: Cxt -> RFuncDef -> IO FuncDef
checkFunc1 ctx (RFuncDef func_name func_typ cls) = do
  func_typ' <- E.check ctx func_typ VU
  let func_typ'' = nf (defs ctx) (env ctx) func_typ'
  unless (noMetas func_typ'') $ do
    throwIO $ DefError ctx $ UnsolvedMetaInFuncDef func_name
  let go = \case
        [] -> pure []
        (rcls : rrest) -> do
          cls <- E.checkCls ctx func_name func_typ'' rcls
          rest <- go rrest
          pure $ cls : rest
  cls' <- go cls
  pure $ FuncDef func_name func_typ'' cls'

insertFunc :: Defs -> FuncDef -> Defs
insertFunc defs func = M.insert (funcName func) (DefFunc func) defs

checkFunc ::  Cxt -> RFuncDef -> IO FuncDef
checkFunc ctx rfun = do
  m <- readIORef nextMeta
  prefun <- checkFunc1 ctx (rfun {funcClausesR = []}) -- this allowing recursion.
  fun <- checkFunc1 (ctx {defs = M.insert (funcNameR rfun) (DefFunc prefun) (defs ctx)}) rfun
  -- TODO : Check Coverage.
  -- putStrLn $ showFunc fun
  pure fun

unfoldPi :: Tm -> (Telescope, Tm)
unfoldPi (Pi x i t b) = ((x,i,t) : fst (unfoldPi b), snd (unfoldPi b))
unfoldPi b = ([], b)


-- Check Data Definitions
----------------------------
insertData :: Defs -> DataDef -> Defs
insertData defs dat = M.insert (dataName dat) (DefData dat) defs

checkData :: SourcePos -> Defs -> RDataDef -> IO DataDef
checkData s defs rdat = do
    ix_ty <- E.check (emptyCxt s){defs = defs} (dataIxR rdat) VU >>= checkIx . nf defs []
    -- (snd -> ix_ty) <- checkTelescope  ()
    let defs' = insertData defs (DataDef (dataNameR rdat) ix_ty [])
    cons <- forM (dataConsR rdat) $ \(n, t) -> do
      t' <- nf defs' [] <$> E.check (emptyCxt s){defs = defs'} t VU
      checkCons s (dataNameR rdat) defs' ix_ty n t'
    pure (DataDef (dataNameR rdat) ix_ty cons)
  where
    checkIx :: Tm -> IO Telescope
    checkIx tm = case unfoldPi tm of
      (ix, U) -> pure ix
      _ -> throwIO $ DefError ((emptyCxt s){defs = defs}) $ DataMustInU (dataNameR rdat)

checkCons :: SourcePos -> Name -> Defs -> Telescope -> Name -> Tm -> IO (Name, Telescope, TSpine)
checkCons s datName defs ix_ty c ty = do
  case go ty of
    Nothing -> throwIO $ DefError ((emptyCxt s) {defs = defs}) $ ConstructorMustReturnData c
    Just (ts, ret_ix) -> pure (c, ts, ret_ix)
  where
    go :: Tm -> Maybe (Telescope, TSpine)
    go tm = do
      let (ts, r) = unfoldPi tm
      as <- goApp r
      pure (ts, as)

    goApp :: Tm -> Maybe TSpine
    goApp (App a b i) = do
      as <- goApp a
      pure (as :> (b,i))
    goApp (Call n)
      | n == datName = Just []
    goApp _ = Nothing

getConstructors :: DataDef -> [(Name, ConsDef)]
getConstructors dat = map go (dataCons dat) where

  go (c, ts, ix) = (c, ConsDef c dat (go1 ts (go2 (Call (dataName dat)) ix)))

  go1 [] c = c
  go1 ((x, i, t):xs) c = Pi x i t $ go1 xs c

  go2 c [] = c
  go2 c (as :> (a, i)) = App (go2 c as) a i

insertCons :: Defs -> [(Name, ConsDef)] -> Defs
insertCons = foldl (\d (c, def) -> M.insert c (DefCons def) d)

checkProg' :: Defs -> Program -> IO Defs
checkProg' defs [] = pure defs
checkProg' defs ((sp, d):ds) = case d of
  RDefFunc d -> do
    f <- checkFunc ((emptyCxt sp){defs = defs}) d
    -- Coverage Check
    let defs' = insertFunc defs f
    checkFuncCover sp defs' (funcName f)
    checkProg' defs' ds
  RDefData d -> do
    d <- checkData sp defs d
    checkProg' (insertCons (insertData defs d) (getConstructors d)) ds
  RDefMutual mb -> do
    let sigs = mutualSig mb
    let bodys = mutualBody mb
    defs' <- insertMutualSig defs sigs
    defs'' <- insertMutualBody defs' (map snd sigs) bodys
    -- Coverage Check 
    forM_ sigs $ \ (_, h) -> case h of
      FunHeader name _ -> checkFuncCover sp defs'' name
      _ -> pure ()
    checkProg' defs'' ds

-- Interleaved
---------------

addCons :: SourcePos -> Defs -> Name ->  [(Name, R.Tm)] -> IO Defs
addCons srcpos defs name = case M.lookup name defs of {Just (DefData d) -> go defs d; _ -> error "impossibles"} where
  go :: Defs -> DataDef -> [(Name, R.Tm)] -> IO Defs
  go defs d = \case
    [] -> do
      let defs1 = M.insert name (DefData d) defs
      let defs2 = insertCons defs1 (getConstructors d)
      pure defs2
    (c, t) : cs -> do
      t' <- nf defs [] <$> E.check (emptyCxt srcpos){defs = defs} t VU
      cons <- checkCons srcpos name defs (dataIx d) c t'
      let d' = d {dataCons = dataCons d ++ [cons]}
      go defs d' cs

addFunCls :: SourcePos -> Defs -> Name -> [R.RClause] -> IO Defs
addFunCls srcpos defs name = case M.lookup name defs of {Just (DefFunc f) -> go defs f; _ -> error "impossibles"} where
  go defs f = \case
    [] -> pure $ M.insert name (DefFunc f) defs
    (c:cs) -> do
      cls <- E.checkCls ((emptyCxt srcpos) {defs = defs}) (funcName f) (funcType f) c
      let f' = f {funcClauses = funcClauses f ++ [cls]}
      go defs f' cs


insertMutualSig :: Defs -> [(SourcePos, Header)] -> IO Defs
insertMutualSig defs = \case
  [] -> pure defs
  (sp, h) : rest -> case h of
    FunHeader name ty -> do
      checkFunc1 ((emptyCxt sp){defs = defs}) (RFuncDef name ty []) >>= \ f ->
        insertMutualSig (insertFunc defs f) rest
    DataHeader name ty -> do
      checkData sp defs (RDataDef name ty []) >>= \ d ->
        insertMutualSig (insertData defs d) rest

lookupHeader :: Cxt -> Name -> [Header] -> IO Header
lookupHeader cxt n = \case
  [] -> throwIO $ DefError cxt $ NameNotFoundOrMismatch n
  (h:hs) -> case h of
    FunHeader name ty | name == n -> pure h
    DataHeader name ty | name == n -> pure h
    _ -> lookupHeader cxt n hs

insertMutualBody :: Defs -> [Header] -> [(SourcePos, Body)] -> IO Defs
insertMutualBody defs headers = \case
  [] -> pure defs
  (sp, b) : rest -> case b of
    FunBody name cls -> do
      h <- lookupHeader ((emptyCxt sp){defs = defs}) name headers
      case h of
        FunHeader _ ty -> do
          defs' <- addFunCls sp defs name cls
          insertMutualBody defs' headers rest
        _ -> throwIO $ DefError ((emptyCxt sp){defs = defs}) $ NameNotFoundOrMismatch name
    DataBody name cons -> do
      h <- lookupHeader ((emptyCxt sp){defs = defs}) name headers
      case h of
        DataHeader _ ty -> do
          defs' <- addCons sp defs name cons
          insertMutualBody defs' headers rest
        _ -> throwIO $ DefError ((emptyCxt sp){defs = defs}) $ NameNotFoundOrMismatch name

checkProg :: HasCallStack => String -> Defs -> Program -> IO Defs
checkProg src defs prog = checkProg' defs prog `catch` \ e -> do
  displayError src e
  throwIO e

-- Coverage Checking
-------------------------------

checkFuncCover :: SourcePos -> Defs -> Name -> IO ()
checkFuncCover srcpos defs fname = do
    case checkFuncCover' srcpos defs fname of
      Left (E.CoverMissPat ps) -> do
        putStrLn $ "Error: function " ++ fname ++ " is not exhaustive."
        putStrLn $ "Missing the following " ++ show (length ps) ++ " pattern(s):"
        forM_ ps $ \sp ->
          putStrLn $ " " ++ printSp sp
      Left E.MeetIDKCons -> putStrLn $ "Error: cannot check exhaustiveness for function " ++ fname ++ " due to unknown existance of some constructors."
      Right () -> pure ()
  where
    printSp :: Spine -> String
    printSp = \case
      [] -> ""
      rest :> (VCons c sp', i) -> printSp rest ++ " " ++ q i (consName c ++ printSp sp')
      rest :> (v, i) -> printSp rest ++ " " ++ q i "_"
      where
        q Impl s = "{" ++ s ++ "}"
        q Expl s = "(" ++ s ++ ")"


checkFuncCover' :: SourcePos -> Defs -> Name -> Either E.CoverCheckingError ()
checkFuncCover' srcpos defs fname = do
    case M.lookup fname defs of
      Just (DefFunc f@(FuncDef _ fty (map clausePatterns -> ps))) -> do
        E.checkCover ((emptyCxt srcpos) {defs = defs}) (eval defs [] fty) (arity f) ps
      _ -> error " impossible"
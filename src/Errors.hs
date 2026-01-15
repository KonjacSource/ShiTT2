
module Errors where

import Control.Exception
import Text.Printf

import Common
import Cxt.Type
import Cxt
import Syntax
import Definition (DataDef)
import GHC.Stack (HasCallStack)

--------------------------------------------------------------------------------

data UnifyError = UnifyError
  deriving (Show, Exception)

data TopLevelError = TopLevelError
  deriving (Show, Exception)

data ElabError
  = NameNotInScope Name
  | CantUnify Tm Tm
  | InferNamedLam
  | InferLamCase
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  | NotAbsurd Ty  
  | UnsolvedMetaInLambdaCase 
  | LambdaCaseUnCover
  | TypeMismatch (Either String Tm) {-Exp-} Tm {-Act-} Tm
  deriving (Show, Exception)

data DefElabError 
  = PatArgMismatch
  | NameIsNotCons Name (Maybe DataDef)
  | PMNoneData Tm
  | UnsurePattern Name Tm
  | WrongPattern Name Tm
  | ConstructorMustReturnData Name 
  | DataMustInU Name
  | ClauseArityNonsame
  | UnsolvedMetaInFuncDef Name
  | NameNotFoundOrMismatch Name 
  deriving (Show, Exception)
 
data Error 
  = Error Cxt ElabError
  | DefError Cxt DefElabError
  deriving (Show, Exception)
  
displayError :: HasCallStack => String -> Error -> IO ()
displayError file (Error cxt e) = do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t'   ->
          ("Cannot unify expected type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with inferred type\n\n" ++
           "  " ++ showTm cxt t')
        InferNamedLam ->
          "Cannot infer type for lambda with named argument"
        InferLamCase ->
          "Cannot infer type for lambda-case expression"
        NoNamedImplicitArg name ->
          "No named implicit argument with name " ++ name
        IcitMismatch i i' -> printf (
          "Function icitness mismatch: expected %s, got %s.")
          (show i) (show i')
        NotAbsurd ty ->
          "Type is not absurd: " ++ showTm cxt ty
        UnsolvedMetaInLambdaCase ->
          "Unsolved meta in lambda-case expression"
        LambdaCaseUnCover ->
          "Lambda-case expression is not cover"
        TypeMismatch t1 t2 t3 ->
          "Type mismatch:\n" ++
          "  Expected: " ++ either id (showTm cxt) t1 ++ "\n" ++
          "  Inferred: " ++ showTm cxt t2 ++ "\n" ++
          "  Term: " ++ showTm cxt t3

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
displayError file (DefError cxt e) = do 
  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg  = case e of
        PatArgMismatch ->
          "Pattern argument mismatch"
        NameIsNotCons name Nothing ->
          "Name is not a constructor: " ++ name
        NameIsNotCons name (Just d) ->
          "Name is not a constructor: " ++ name ++
          "\nIn data type: " ++ show d
        PMNoneData t ->
          "Pattern match on non-data type: " ++ showTm cxt t
        UnsurePattern name t ->
          printf "I don't know if there should be a case %s for type %s" name (showTm cxt t)
        WrongPattern name t ->
          printf "No case %s for type %s" name (showTm cxt t)
        ConstructorMustReturnData name ->
          printf "Constructor %s must return data type" name
        DataMustInU name ->
          printf "Data type %s must be in U" name
        ClauseArityNonsame ->
          "Clauses have different arities"
        UnsolvedMetaInFuncDef func_name ->
          printf "Unsolved meta in function definition %s" func_name
        NameNotFoundOrMismatch name ->
          printf "Name not found or mismatch: %s" name
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg


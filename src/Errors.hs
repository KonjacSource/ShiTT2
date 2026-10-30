
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
  | NotAType Tm
  | SigmaMismatch
  | FieldNotFound Name Tm
  | NotASigma Tm
  deriving (Show, Exception)

data DefElabError 
  = PatArgMismatch
  | NameIsNotCons Name (Maybe DataDef)
  | PMNoneData Tm
  | PMNoneEq Tm 
  | UnsurePattern Name Tm
  | WrongPattern Name Tm
  | ConstructorMustReturnData Name 
  | NonQITCan'tHaveEqCons Name Name
  | HigherDimensionalDataNotSupported Name Name
  | DataMustInU Name
  | ClauseArityNonsame
  | UnsolvedMetaInFuncDef Name
  | NameNotFoundOrMismatch Name 
  | DefiningApdForWrongFunction Name Name 
  | DefiningApdNotFullyApplied Name
  | DefiningApdForNonQITElim Name String
  | NoApdClauseDefinedFor Name
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
        NotAType t ->
          "Not a type: " ++ showTm cxt t
        SigmaMismatch ->
          "Sigma type mismatch"
        FieldNotFound x t ->
          "Field not found: " ++ x ++ " in type: " ++ showTm cxt t
        NotASigma t ->
          "Expected a sigma type, but got: " ++ showTm cxt t

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
          printf "Constructor %s must return data type (or a QIT equality)" name
        HigherDimensionalDataNotSupported datName consName ->
          printf "Higher-dimensional path constructors are not supported. In data type %s, constructor %s" datName consName
        NonQITCan'tHaveEqCons datName consName ->
          printf "Non-QIT data type %s can't have path constructor %s" datName consName
        DataMustInU name ->
          printf "Data type %s must be in U" name
        ClauseArityNonsame ->
          "Clauses have different arities"
        UnsolvedMetaInFuncDef func_name ->
          printf "Unsolved meta in function definition %s" func_name
        NameNotFoundOrMismatch name ->
          printf "Name not found or mismatch: %s" name
        DefiningApdForWrongFunction f f' ->
          printf "Defined an apd clause for %s, while I am expecting for %s" f' f
        DefiningApdNotFullyApplied name ->
          printf "Defined an apd clause for %s, but the pattern is not fully applied" name
        DefiningApdForNonQITElim name ps ->
          printf "Defined an apd clause for %s with patterns %s, but it is not a QIT eliminator" name ps
        PMNoneEq t ->
          "A path constructor matched on non-equality type: " ++ showTm cxt t
        NoApdClauseDefinedFor f -> 
          "There is no apd clause defined for function " ++ show f

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg


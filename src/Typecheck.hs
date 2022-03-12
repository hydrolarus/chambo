module Typecheck where

import Control.Monad.State
import qualified Data.Map as M
import Debug.Trace
import Syntax

dbg :: Show a => a -> a
dbg a = trace (show a) a

newtype GlobalCtx = GlobalCtx {globalFuncs :: M.Map String Function}

newtype LocalCtx = LocalCtx {localVars :: M.Map String Type}

data TypeError
  = TEVariableNotDefined String
  | TEFunctionNotDefined String
  | TEFunctionArgsTooMuch [String]
  | TEFunctionArgsMissing [String]
  | TEMismatchedType Type Type -- expected found
  | TEInvalidBinOpArgs BinOp Type Type
  deriving (Show)

newtype TypeCheck a = TypeCheck {runTypeCheck :: (GlobalCtx, LocalCtx) -> Either TypeError (GlobalCtx, LocalCtx, a)}

processFile :: File -> TypeCheck File
processFile (File items) = do
  forM_ items $ \case
    IFunction function -> addFunctionSig function

  items' <- forM items $ \case
    IFunction function -> do
      fun <- local $ typeCheckFunction function
      pure $ IFunction fun

  pure $ File items'

typeCheckFunction :: Function -> TypeCheck Function
typeCheckFunction f@(Function name args ret pres posts body _) = do
  forM_ args $ uncurry addLocalVar
  pres' <- forM pres typeCheckTerm
  posts' <- forM posts $ \t -> local $ do
    addLocalVar "result" ret
    typeCheckTerm t

  (bodyTy, body') <- exprGetType body
  typeExpect ret bodyTy
  pure $ f {funPre = pres', funPost = posts', funTBody = Just body'}

exprGetType :: Expr -> TypeCheck (Type, TExpr)
exprGetType (EIntLiteral n) = pure (TInt, TEIntLiteral n)
exprGetType (EStringLiteral s) = pure (TString, TEStringLiteral s)
exprGetType (EBoolLiteral b) = pure (TBool, TEBoolLiteral b)
exprGetType EUnitLiteral = pure (TUnit, TEUnitLiteral)
exprGetType (EBinOp op lhs rhs) = do
  (lhsTy, lhs') <- exprGetType lhs
  (rhsTy, rhs') <- exprGetType rhs
  ty <- binOpType op lhsTy rhsTy
  pure (ty, TEBinOp op lhs' rhs')
exprGetType (EPrefixOp op a) = do
  (ty, a') <- exprGetType a
  ty <- prefixOpType op ty
  pure (ty, TEPrefixOp op a')
exprGetType (ESeq a b) = do
  (_, a') <- exprGetType a
  (bTy, b') <- exprGetType b
  pure (bTy, TESeq a' b')
exprGetType (EVar name) = do
  lctx <- getLocalCtx
  case M.lookup name (localVars lctx) of
    Nothing -> tyError (TEVariableNotDefined name)
    Just ty -> pure (ty, TEVar name ty)
exprGetType (EFunCall name args) = do
  gctx <- getGlobalCtx
  Function _ fnArgs ret _ _ _ _ <- case M.lookup name (globalFuncs gctx) of
    Nothing -> tyError $ TEFunctionNotDefined name
    Just x -> pure x
  args' <- forM args $ \(name, arg) -> exprGetType arg >>= \(ty, targ) -> pure (name, (ty, targ))
  let argTypes = map (\(name, (ty, _)) -> (name, ty)) args'
  namedArgsTypeMatch fnArgs argTypes
  pure (ret, TEFunCall name $ map (\(name, (_, texp)) -> (name, texp)) args')
exprGetType (EAssert te) = do
  te' <- typeCheckTerm te
  pure (TUnit, TEAssert te')
exprGetType (EIf cond thn els) = do
  (condTy, cond') <- exprGetType cond
  (thenTy, then') <- exprGetType thn
  (elseTy, else') <- exprGetType els

  case (condTy, thenTy, elseTy) of
    (TBool, a, b) -> typeExpect a b >> pure (a, TEIf cond' then' else')
    (_, _, _) -> tyError $ TEMismatchedType TBool condTy
exprGetType (ELet name rhs body) = do
  (rhsTy, rhs') <- exprGetType rhs
  (bodyTy, body') <- local $ do
    addLocalVar name rhsTy
    exprGetType body
  pure (bodyTy, TELet name rhsTy rhs' body')

typeCheckTerm :: Term -> TypeCheck Term
typeCheckTerm (TExpr ex _) = do
  (ty, ex') <- exprGetType ex
  typeExpect TBool ty
  pure $ TExpr ex (Just ex')
typeCheckTerm (TForall s ty te) = do
  te' <- local $ do
    addLocalVar s ty
    typeCheckTerm te
  pure $ TForall s ty te'
typeCheckTerm (TDisjunction a b) = do
  a' <- typeCheckTerm a
  b' <- typeCheckTerm b
  pure $ TDisjunction a' b'
typeCheckTerm (TConjunction a b) = do
  a' <- typeCheckTerm a
  b' <- typeCheckTerm b
  pure $ TConjunction a' b'

binOpType :: BinOp -> Type -> Type -> TypeCheck Type
binOpType OpAdd TInt TInt = pure TInt
binOpType OpSub TInt TInt = pure TInt
binOpType OpMul TInt TInt = pure TInt
binOpType OpDiv TInt TInt = pure TInt
binOpType OpLt TInt TInt = pure TBool
binOpType OpLte TInt TInt = pure TBool
binOpType OpGt TInt TInt = pure TBool
binOpType OpGte TInt TInt = pure TBool
binOpType OpImplies TBool TBool = pure TBool
binOpType OpAnd TBool TBool = pure TBool
binOpType OpOr TBool TBool = pure TBool
binOpType op a b
  | op `elem` [OpEq, OpNeq] = case (a, b) of
    (TInt, TInt) -> pure TBool
    (TBool, TBool) -> pure TBool
    (TString, TString) -> pure TBool
    (_, _) -> tyError $ TEInvalidBinOpArgs op a b
  | otherwise = tyError $ TEInvalidBinOpArgs op a b

prefixOpType :: PrefixOp -> Type -> TypeCheck Type
prefixOpType OpNot b = typeExpect TBool b >> pure b

namedArgsTypeMatch :: [(String, Type)] -> [(String, Type)] -> TypeCheck ()
namedArgsTypeMatch [] [] = pure ()
namedArgsTypeMatch [] xs = tyError $ TEFunctionArgsTooMuch (map fst xs)
namedArgsTypeMatch xs [] = tyError $ TEFunctionArgsMissing (map fst xs)
namedArgsTypeMatch ((n, ty) : xs) ys = case lookupRemove n ys of
  Nothing -> tyError $ TEFunctionArgsMissing [n]
  Just (ty', ys')
    | ty' == ty -> namedArgsTypeMatch xs ys'
    | otherwise -> tyError $ TEMismatchedType ty ty'
  where
    lookupRemove :: String -> [(String, Type)] -> Maybe (Type, [(String, Type)])
    lookupRemove name [] = Nothing
    lookupRemove name ((n, ty) : xs)
      | n == name = Just (ty, xs)
      | otherwise = do
        (found, rest) <- lookupRemove name xs
        Just (found, (n, ty) : rest)

typeExpect :: Type -> Type -> TypeCheck ()
typeExpect expect got
  | expect == got = pure ()
  | otherwise = tyError $ TEMismatchedType expect got

-------------------------------------------------------------------------------

instance Functor TypeCheck where
  fmap f TypeCheck {..} =
    TypeCheck
      { runTypeCheck =
          \(gctx, lctx) -> do
            (gctx', lctx', res) <- runTypeCheck (gctx, lctx)
            Right (gctx', lctx', f res)
      }

instance Applicative TypeCheck where
  pure a = TypeCheck {runTypeCheck = \(gctx, lctx) -> Right (gctx, lctx, a)}

  TypeCheck {runTypeCheck = f} <*> TypeCheck {runTypeCheck = a} =
    TypeCheck
      { runTypeCheck = \(gctx, lctx) -> do
          (gctx', lctx', a') <- a (gctx, lctx)
          (gctx'', lctx'', f') <- f (gctx', lctx')
          Right (gctx'', lctx'', f' a')
      }

instance Monad TypeCheck where
  TypeCheck {runTypeCheck = a} >>= f =
    TypeCheck
      { runTypeCheck = \(gctx, lctx) -> do
          (gctx', lctx', a') <- a (gctx, lctx)
          let TypeCheck {runTypeCheck = res} = f a'
          res (gctx', lctx')
      }

runTypeCheckNew :: TypeCheck a -> Either TypeError a
runTypeCheckNew action = case runTypeCheck action (GlobalCtx M.empty, LocalCtx M.empty) of
  Left err -> Left err
  Right (_, _, x) -> Right x

getGlobalCtx :: TypeCheck GlobalCtx
getGlobalCtx = TypeCheck {runTypeCheck = \(gctx, lctx) -> Right (gctx, lctx, gctx)}

modifyGlobalCtx :: (GlobalCtx -> GlobalCtx) -> TypeCheck ()
modifyGlobalCtx f = TypeCheck {runTypeCheck = \(gctx, lctx) -> Right (f gctx, lctx, ())}

getLocalCtx :: TypeCheck LocalCtx
getLocalCtx = TypeCheck {runTypeCheck = \(gctx, lctx) -> Right (gctx, lctx, lctx)}

modifyLocalCtx :: (LocalCtx -> LocalCtx) -> TypeCheck ()
modifyLocalCtx f = TypeCheck {runTypeCheck = \(gctx, lctx) -> Right (gctx, f lctx, ())}

addFunctionSig :: Function -> TypeCheck ()
addFunctionSig f@(Function name args ret pres posts _ _) = modifyGlobalCtx (GlobalCtx . M.insert name f . globalFuncs)

local :: TypeCheck a -> TypeCheck a
local action = do
  orig <- getLocalCtx
  res <- action
  modifyLocalCtx (const orig)
  pure res

addLocalVar :: String -> Type -> TypeCheck ()
addLocalVar name ty = modifyLocalCtx (LocalCtx . M.insert name ty . localVars)

tyError :: TypeError -> TypeCheck a
tyError err = TypeCheck {runTypeCheck = \_ -> Left err}
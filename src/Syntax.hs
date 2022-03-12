module Syntax where

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Bifunctor

newtype File = File [Item]

newtype Item
  = IFunction Function
  deriving (Show, Eq)

data Function = Function
  { funName :: String,
    funArgs :: [(String, Type)],
    funRet :: Type,
    funPre :: [Term],
    funPost :: [Term],
    funBody :: Expr,
    funTBody :: Maybe TExpr
  }
  deriving (Show, Eq)

data Type
  = TInt
  | TString
  | TBool
  | TUnit
  deriving (Eq, Show)

data Term
  = TExpr Expr (Maybe TExpr)
  | TForall String Type Term
  | TDisjunction Term Term
  | TConjunction Term Term
  deriving (Show, Eq)

data Expr
  = EIntLiteral Integer
  | EStringLiteral String
  | EBoolLiteral Bool
  | EUnitLiteral
  | EBinOp BinOp Expr Expr
  | EPrefixOp PrefixOp Expr
  | ESeq Expr Expr
  | EVar String
  | EFunCall String [(String, Expr)]
  | EAssert Term
  | EIf Expr Expr Expr
  | ELet String Expr Expr
  deriving (Show, Eq)

data BinOp
  = OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpEq
  | OpNeq
  | OpLt
  | OpLte
  | OpGt
  | OpGte
  | OpImplies
  | OpAnd
  | OpOr
  deriving (Show, Eq)

data PrefixOp
  = OpNot
  deriving (Show, Eq)

data TExpr
  = TEIntLiteral Integer
  | TEStringLiteral String
  | TEBoolLiteral Bool
  | TEUnitLiteral
  | TEBinOp BinOp TExpr TExpr
  | TEPrefixOp PrefixOp TExpr
  | TESeq TExpr TExpr
  | TEVar String Type
  | TEFunCall String [(String, TExpr)]
  | TEAssert Term
  | TEIf TExpr TExpr TExpr
  | TELet String Type TExpr TExpr
  deriving (Show, Eq)

weakenExpr :: TExpr -> Expr
weakenExpr (TEIntLiteral n) = EIntLiteral n
weakenExpr (TEStringLiteral s) = EStringLiteral s
weakenExpr (TEBoolLiteral b) = EBoolLiteral b
weakenExpr TEUnitLiteral = EUnitLiteral
weakenExpr (TEBinOp op a b) = EBinOp op (weakenExpr a) (weakenExpr b)
weakenExpr (TEPrefixOp op a) = EPrefixOp op (weakenExpr a)
weakenExpr (TESeq a b) = ESeq (weakenExpr a) (weakenExpr b)
weakenExpr (TEVar s ty) = EVar s
weakenExpr (TEFunCall name args) = EFunCall name (map (second weakenExpr) args)
weakenExpr (TEAssert te) = EAssert te
weakenExpr (TEIf cond thn els) = EIf (weakenExpr cond) (weakenExpr thn) (weakenExpr els)
weakenExpr (TELet s ty rhs body) = ELet s (weakenExpr rhs) (weakenExpr body)

lookupFunction :: File -> String -> Maybe Function
lookupFunction (File items) name = go items
  where
    go [] = Nothing
    go ((IFunction f@(Function n _ _ _ _ _ _)) : xs)
      | n == name = Just f
      | otherwise = go xs

functions :: File -> [Function]
functions (File items) = flip mapMaybe items $
  \case IFunction func -> Just func

substTExpr :: M.Map String TExpr -> TExpr -> TExpr
substTExpr subst e@(TEIntLiteral n) = e
substTExpr subst e@(TEStringLiteral s) = e
substTExpr subst e@(TEBoolLiteral b) = e
substTExpr subst e@TEUnitLiteral = e
substTExpr subst (TEBinOp op a b) = TEBinOp op (substTExpr subst a) (substTExpr subst b)
substTExpr subst (TEPrefixOp op a) = TEPrefixOp op (substTExpr subst a)
substTExpr subst (TESeq a b) = TESeq (substTExpr subst a) (substTExpr subst b)
substTExpr subst e@(TEVar s ty) = fromMaybe e (M.lookup s subst)
substTExpr subst (TEFunCall name args) = TEFunCall name $ map (second (substTExpr subst)) args
substTExpr subst (TEAssert te) = TEAssert $ substTerm subst te
substTExpr subst (TEIf cond th el) = TEIf (substTExpr subst cond) (substTExpr subst th) (substTExpr subst el)
substTExpr subst (TELet s ty rhs body) = TELet s ty (substTExpr subst rhs) (substTExpr subst body)

substTerm :: M.Map String TExpr -> Term -> Term
substTerm subst (TExpr e e') = TExpr e (substTExpr subst <$> e')
substTerm subst (TForall s ty e) = TForall s ty (substTerm subst e)
substTerm subst (TDisjunction a b) = TDisjunction (substTerm subst a) (substTerm subst b)
substTerm subst (TConjunction a b) = TConjunction (substTerm subst a) (substTerm subst b)

prettyTExpr :: TExpr -> String
prettyTExpr (TEIntLiteral n) = show n
prettyTExpr (TEStringLiteral s) = show s
prettyTExpr (TEBoolLiteral b) = show b
prettyTExpr TEUnitLiteral = "()"
prettyTExpr (TEBinOp op a b) = "(" ++ prettyTExpr a ++ " " ++ op' ++ " " ++ prettyTExpr b ++ ")"
  where
    op' = case op of
      OpAdd -> "+"
      OpSub -> "-"
      OpMul -> "*"
      OpDiv -> "/"
      OpEq -> "="
      OpNeq -> "!="
      OpLt -> "<"
      OpLte -> "<="
      OpGt -> ">"
      OpGte -> ">="
      OpImplies -> "==>"
      OpAnd -> "&&"
      OpOr -> "||"
prettyTExpr (TEPrefixOp op a) = op' ++ "(" ++ prettyTExpr a ++ ")"
  where
    op' = case op of
      OpNot -> "!"
prettyTExpr (TESeq a b) = prettyTExpr a ++ "; " ++ prettyTExpr b
prettyTExpr (TEVar s ty) = s
prettyTExpr (TEFunCall name args) = name ++ "(" ++ intercalate ", " args' ++ ")"
  where
    args' = map (\(name, expr) -> name ++ ": " ++ prettyTExpr expr) args
prettyTExpr (TEAssert te) = "assert { " ++ prettyTerm te ++ " }"
prettyTExpr (TEIf cond thn els) =
  "if " ++ prettyTExpr cond
    ++ " then "
    ++ prettyTExpr thn
    ++ " else "
    ++ prettyTExpr els
prettyTExpr (TELet name ty rhs body) =
  "let " ++ name ++ " : " ++ prettyType ty
    ++ " = "
    ++ prettyTExpr rhs
    ++ " in "
    ++ prettyTExpr body

prettyTerm :: Term -> String
prettyTerm (TExpr ex Nothing) = "<Term not yet type checked>"
prettyTerm (TExpr ex (Just te)) = prettyTExpr te
prettyTerm (TForall s ty te) = "forall " ++ s ++ ":" ++ prettyType ty ++ " . " ++ prettyTerm te
prettyTerm (TDisjunction a b) = "(" ++ prettyTerm a ++ " \\/ " ++ prettyTerm b ++ ")"
prettyTerm (TConjunction a b) = "(" ++ prettyTerm a ++ " /\\ " ++ prettyTerm b ++ ")"

prettyType :: Type -> String
prettyType TInt = "int"
prettyType TString = "string"
prettyType TBool = "bool"
prettyType TUnit = "()"
module Main where

import Control.Monad (forM_, when)
import Data.Maybe (listToMaybe)
import Verification
import Syntax
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Typecheck
import Z3.Monad ( evalZ3 )
import Parsing
import Data.List (intercalate)

import System.Console.ANSI

infixr 2 ==>

infix 4 .&&

infix 6 .>=

infix 6 .<

infix 6 .<=

(.&&) :: Expr -> Expr -> Expr
(.&&) = EBinOp OpAnd

(.>=) :: Expr -> Expr -> Expr
(.>=) = EBinOp OpGte

(.<) :: Expr -> Expr -> Expr
(.<) = EBinOp OpLt

(.<=) :: Expr -> Expr -> Expr
(.<=) = EBinOp OpLte

(==>) :: Expr -> Expr -> Expr
(==>) = EBinOp OpImplies

(.==) :: Expr -> Expr -> Expr
(.==) = EBinOp OpEq

infixl 9 .*

infixl 7 .+

(.+) :: Expr -> Expr -> Expr
(.+) = EBinOp OpAdd

(.*) :: Expr -> Expr -> Expr
(.*) = EBinOp OpMul

var :: String -> Expr
var = EVar

int :: Integer -> Expr
int = EIntLiteral

t :: Expr -> Term
t e = TExpr e Nothing

fun name args ret pres posts body = Function name args ret pres posts body Nothing

maxFn :: Function
maxFn =
  fun
    "max"
    [("a", TInt), ("b", TInt)]
    TInt
    []
    [ TDisjunction (t $ var "result" .== var "a") (t $ var "result" .== var "b"),
      TConjunction (t $ var "result" .>= var "a") (t $ var "result" .>= var "b")
    ]
    ( EIf (var "a" .>= var "b") (var "a") (var "b")
    )

sem :: Expr -> Expr -> Expr
sem = ESeq

testFn :: Function
testFn =
  fun "test" [] TUnit [] [] $
    ELet "res" (EFunCall "max" [("b", int 2), ("a", int 5)]) $
      EAssert (t $ var "res" .== int 4)
        `sem` EUnitLiteral

vcTest :: Function
vcTest =
  fun
    "vc_test"
    []
    TUnit
    []
    [ -- trivial
      t $ int 3 .<= int 5,
      -- WRONG!
      -- forall x. 0 < x <= 6  ==> x <= 2
      TForall "x" TInt . t $ (int 0 .< var "x" .&& var "x" .<= int 6) ==> var "x" .<= int 2,
      -- Correct!
      -- forall x. 0 < x <= 6  ==> x <= 10
      TForall "x" TInt . t $ (int 0 .< var "x" .&& var "x" .<= int 6) ==> var "x" .<= int 10
    ]
    EUnitLiteral

assumptionsTest :: Function
assumptionsTest =
  fun
    "assumptions"
    [("a", TInt), ("b", TInt)]
    TInt
    -- preconditions
    [ t $ var "a" .< var "b",
      t $ int 0 .<= var "a",
      t $ int 0 .<= var "b"
    ]
    -- posconditions
    [t $ var "a" .< var "b" .* int 2]
    (EIf (var "a" .== int 2) (int 3) (int 9))

file :: File
file = File $ map IFunction [maxFn, testFn]

getFile :: IO File
getFile = do
  fileName <- listToMaybe <$> getArgs
  content <- maybe (pure "") readFile fileName
  pure $ parse content

main :: IO ()
main = do
  file <- getFile

  putStr "Typechecking...  "
  file' <- case runTypeCheckNew (processFile file) of
    Left err -> do
      putStrLn $ "\nFailed: " ++ show err
      exitFailure
    Right file -> do
      putStrLn "Ok!"
      pure file

  putStrLn "\nRunning VCs..."
  let vcs = allVCs file'
  -- print vcs
  forM_ (zip [1..] vcs) $ \(i, vc) -> do
    res <- evalZ3 $ verify file' vc

    let path' = intercalate "." (path vc)
    case res of
      Unknown -> do
        withColour Yellow $ putStr "Unknown "
        putStrLn path'
      Success -> do
        withColour Green $ putStr "Success "
        putStrLn path'
      Failed model vc -> do
        withColour Red $ putStr "Failed  "
        putStrLn path'

        when (model /= []) $
          putStrLn $ "  Counterexample: " ++ show model

        putStrLn $ unlines . map ("  " ++) $ printVC vc

        pure ()


printVC :: VerificationCondition -> [String]
printVC VC {..} = assumptions' ++ ["check:  " ++ prettyTerm expression]
  where
    -- assumptions' = flip map assumptions $ \s -> "assume: " ++ prettyTerm s
    assumptions' = []

withColour :: Color -> IO a -> IO a
withColour col action = do
    setSGR [SetColor Foreground Vivid col]
    res <- action
    setSGR [Reset]
    pure res
module Main where

import           Control.Monad       (forM_, when)
import           Data.List           (intercalate)
import           Data.Maybe          (listToMaybe)
import           System.Console.ANSI
import           System.Environment  (getArgs)
import           System.Exit         (exitFailure)

import           Parsing
import           Syntax
import           Typecheck
import           Verification


import           Z3.Monad            (evalZ3)

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

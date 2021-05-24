module GRIN.Pipeline

import Data.SortedSet as Set
import Data.SortedMap as Map
import Data.String.Builder

import System.Clock
import System.File

import GRIN.AST
import GRIN.Error
import GRIN.GrinM

import GRIN.Analysis.CallGraph

import GRIN.Opts.CaseSimplify
import GRIN.Opts.CopyPropogation
import GRIN.Opts.UnusedConstructorElim
import GRIN.Opts.UnusedFunctionElim
import GRIN.Opts.UnusedParameterElim
import GRIN.Opts.NormaliseBind

public export
data Optimise name
    = CopyPropogation
    | UnusedConstructorElim
    | UnusedFunctionElim
    | UnusedParamElim
    | NormaliseBind
    | CaseSimplify
    | Fix (List (Optimise name))

Show (Optimise name) where
    show CopyPropogation = "copy propogation"
    show UnusedConstructorElim = "unused constructor elimintation"
    show UnusedFunctionElim = "unused function elimination"
    show UnusedParamElim = "unused parameter elimination"
    show NormaliseBind = "bind normalisation"
    show CaseSimplify = "case simplification"
    show (Fix os) = "fix " ++ show os

export
runOpts : Ord name => List (Optimise name) -> GrinM name ()

export
runOpt : Ord name => Optimise name -> GrinM name ()
runOpt CopyPropogation = copyProp
runOpt CaseSimplify = caseSimplify
runOpt UnusedConstructorElim = unusedConsElim
runOpt UnusedFunctionElim = unusedFuncElim
runOpt UnusedParamElim = unusedParamElim
runOpt NormaliseBind = normaliseBind
runOpt s@(Fix ss) = do
    p0 <- gets prog
    runOpts ss
    p1 <- gets prog
    if p1 == p0
        then pure ()
        else runOpt s

runOpts [] = pure ()
runOpts (s :: ss) = runOpt s *> runOpts ss

public export
data Transform name
    = O (Optimise name)
    | SaveGrin Bool String
    | SaveCalls Bool String
    | SaveCalledBy Bool String

Show (Transform name) where
    show (O o) = show o
    show (SaveGrin _ _) = "save GRIN"
    show (SaveCalls _ _) = "save calls graph"
    show (SaveCalledBy _ _) = "save called by graph"

export
runTransform : Show name => ShowB (Prog name) => Ord name => Transform name -> GrinT name IO ()
runTransform (O opt) = liftGrinM (pure . runIdentity) $ runOpt opt
runTransform (SaveGrin True f) = do
    p <- gets prog
    let pretty = runBuilder $ showB p
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform (SaveCalls True f) = do
    calls <- getCalls
    let pretty = showCallGraph calls
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform (SaveCalledBy True f) = do
    calls <- getCalledBy
    let pretty = showCallGraph calls
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform _ = pure ()

export
runTransforms : Show name => ShowB (Prog name) => Ord name => List (Transform name) -> GrinT name IO ()
runTransforms [] = pure ()
runTransforms (t :: ts) = runTransform t *> runTransforms ts

nano : Integer
nano = 1000000000

micro : Integer
micro = 1000000

export
runWithTiming : Show name => ShowB (Prog name) => Ord name => List (Transform name) -> GrinT name IO ()
runWithTiming [] = pure ()
runWithTiming (t :: ts) = do
    putStrLn $ "Start " ++ show t
    clock <- liftIO $ clockTime Process
    let start = seconds clock * nano + nanoseconds clock
    runTransform t
    let end = seconds clock * nano + nanoseconds clock
    let time = end - start
    putStrLn $
        "Finished, took: "
        ++ show (time `div` nano) ++ "."
        ++ addZeros (unpack (show ((time `mod` nano) `div` micro)))
        ++ "s"
    runWithTiming ts
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x, y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

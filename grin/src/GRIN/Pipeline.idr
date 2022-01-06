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
import GRIN.Analysis.Inline

import GRIN.Opts.CaseSimplify
import GRIN.Opts.CopyPropogation
import GRIN.Opts.Inline
import GRIN.Opts.NormaliseBind
import GRIN.Opts.UnusedConstructorElim
import GRIN.Opts.UnusedFunctionElim
import GRIN.Opts.UnusedParameterElim
import GRIN.Opts.UnusedVarElim

public export
data Optimise name
    = CaseSimplify
    | CopyPropogation
    | InlineSimpleDef
    | InlineUsedOnce
    | InlineFunc name
    | NormaliseBind
    | UnusedConstructorElim
    | UnusedFunctionElim
    | UnusedParamElim
    | UnusedVarElim
    | Fix (List (Optimise name))

Show name => Show (Optimise name) where
    show CopyPropogation = "copy propogation"
    show CaseSimplify = "case simplification"
    show InlineSimpleDef = "inline simple definitions"
    show InlineUsedOnce = "inline functions used once"
    show (InlineFunc fn) = "inline " ++ show fn
    show NormaliseBind = "bind normalisation"
    show UnusedConstructorElim = "unused constructor elimintation"
    show UnusedFunctionElim = "unused function elimination"
    show UnusedParamElim = "unused parameter elimination"
    show UnusedVarElim = "unused variable elimination"
    show (Fix os) = "fix " ++ assert_total (show os)

export
runOpts : Show name => Monad m => Ord name => List (Optimise name) -> GrinT name m ()

export
runOpt : Show name => Monad m => Ord name => Optimise name -> GrinT name m ()
runOpt CaseSimplify = caseSimplify
runOpt CopyPropogation = copyProp
runOpt InlineSimpleDef = do
    inlineSimpleDefs
    inlineAll
runOpt InlineUsedOnce = do
    inlineUsedOnce
    inlineAll
runOpt (InlineFunc fn) = do
    ds <- gets $ defs . prog
    case lookup fn ds of
        Nothing => pure ()
        Just def => modify $ record { toInline = singleton fn def }
    inlineAll
runOpt NormaliseBind = normaliseBind
runOpt UnusedConstructorElim = unusedConsElim
runOpt UnusedFunctionElim = unusedFuncElim
runOpt UnusedParamElim = unusedParamElim
runOpt UnusedVarElim = unusedVarElim
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
    | SaveInlineSimple Bool String

Show name => Show (Transform name) where
    show (O o) = show o
    show (SaveGrin _ _) = "save GRIN"
    show (SaveCalls _ _) = "save calls graph"
    show (SaveCalledBy _ _) = "save called by graph"
    show (SaveInlineSimple _ _) = "save simple functions to inline"

export
runTransform : Show name => ShowB (Prog name) => Ord name => Transform name -> GrinT name IO ()
runTransform (O opt) = runOpt opt
runTransform (SaveGrin True f) = do
    p <- gets prog
    let pretty = runBuilder $ showB p
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform (SaveCalls True f) = do
    cg <- getCalls
    let pretty = showCallGraph cg
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform (SaveCalledBy True f) = do
    cg <- getCalledBy
    let pretty = showCallGraph cg
    Right () <- lift $ writeFile f pretty
        | Left err => newError $ FileErr f err
    pure ()
runTransform (SaveInlineSimple True f) = do
    inlineSimpleDefs
    ti <- gets toInline
    Right () <- lift $ writeFile f $ show $ keys ti
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

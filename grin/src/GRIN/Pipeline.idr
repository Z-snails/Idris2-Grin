module GRIN.Pipeline

import Data.SortedSet as Set
import Data.SortedMap as Map
import Data.String.Builder

import System.File

import GRIN.AST
import GRIN.GrinM

import GRIN.Analysis
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

export
runTransform : Show name => ShowB (Prog name) => Ord name => Transform name -> GrinT name IO ()
runTransform (O opt) = liftGrinM (pure . runIdentity) $ runOpt opt
runTransform (SaveGrin True f) = do
    p <- gets prog
    let pretty = runBuilder $ showB p
    ignore $ lift $ writeFile f pretty
runTransform (SaveCalls True f) = do
    calls <- getCalls
    let pretty = showCallGraph calls
    ignore $ lift $ writeFile f pretty
runTransform (SaveCalledBy True f) = do
    calls <- getCalledBy
    let pretty = showCallGraph calls
    ignore $ lift $ writeFile f pretty
runTransform _ = pure ()

export
runTransforms : Show name => ShowB (Prog name) => Ord name => List (Transform name) -> GrinT name IO ()
runTransforms [] = pure ()
runTransforms (t :: ts) = runTransform t *> runTransforms ts

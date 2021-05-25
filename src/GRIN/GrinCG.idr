module GRIN.GrinCG

import Core.Core
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
import Core.Options.Log
import Compiler.Common

import Data.String.Builder
import Data.String

import Libraries.Utils.Path

import System
import System.File
import System.Directory

import GRIN.ANFToGRIN
import GRIN.AST
import GRIN.Data
import GRIN.Error
import GRIN.PrettyCompatB
import GRIN.Pipeline
import GRIN.Name
import GRIN.GrinM

getSaveIR : List String -> Bool
getSaveIR [] = False
getSaveIR (d :: ds) = trim d == "save-ir" || getSaveIR ds

getDoOpts : List String -> Bool
getDoOpts [] = True
getDoOpts (d :: ds) = trim d /= "no-opts" && getDoOpts ds

getSkipCG : List String -> Bool
getSkipCG [] = False
getSkipCG (d :: ds) = trim d == "skip-cg" || getSkipCG ds

getDoStats : List String -> Bool
getDoStats [] = False
getDoStats (d :: ds) = trim d == "stats" || getDoStats ds

ShowB GName where
    showB = showB @{FromShow}

data PostPipeline
    = Eval
    | EvalWithStats
    | SaveLLVM

compileExpr :
    PostPipeline ->
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    (outDir : String) ->
    ClosedTerm ->
    (outFile : String) ->
    Core (Maybe String)
compileExpr post d tmpDir outDir term outFile = do
    let appDir = outDir </> outFile ++ "_app"
        mkGrinFile = \f => appDir </> f <.> "grin"
        outGrinFile = mkGrinFile outFile
        outLLFile = outDir </> outFile

    ds <- getDirectives (Other "grin")
    let doOpts = getDoOpts ds
    let saveIR = getSaveIR ds
    let skipCG = getSkipCG ds

    Right _ <- coreLift $ mkdirAll appDir
        | Left err => throw $ FileErr appDir err

    cdata <- getCompileData True ANF term

    prog0 <- logTime "++ Compile ANF to GRIN" $ compileANF cdata.anf

    prog1 <- logTime "++ Resolve names" $ pure $ runResolveM $ traverseProg resolve prog0

    let pipeline : List (Transform (Resolved GName))
        pipeline =
            [ SaveGrin saveIR (mkGrinFile "000_ANF")
            , O NormaliseBind
            , SaveGrin saveIR (mkGrinFile "001_bind_normalise")
            , O CopyPropogation
            , SaveGrin saveIR (mkGrinFile "002_copy_prop")
            , O InlineSimpleDef
            , SaveGrin saveIR (mkGrinFile "003_inline_simple")
            , O $ Fix
                [ UnusedFunctionElim
                , UnusedConstructorElim
                ]
            , SaveGrin saveIR (mkGrinFile "004_unused_function_constructor")
            , O  $ InlineUsedOnce
            , SaveGrin saveIR (mkGrinFile "005_inline_used_once")
            , O $ Fix [ UnusedParamElim ]
            , SaveGrin saveIR (mkGrinFile "006_unused_parameter")
            , O CaseSimplify
            , SaveGrin saveIR (mkGrinFile "007_case_simplify")
            , O NormaliseBind
            , SaveCalls saveIR (appDir </> "calls_graph")
            , SaveCalledBy saveIR (appDir </> "called_by_graph")
            , SaveGrin True outGrinFile
            ]

    st <- logTime "++ Run optimisations" $ coreLift $ execGrinT' (runTransforms $
            if doOpts
                then pipeline
                else [ SaveGrin True outGrinFile ])
            (newGrinState prog1)

    let [] = getErrors st
        | errs => throw $ InternalError $ "Error running optimisations\n" ++ show errs

    doLog <- unverifiedLogging "grin" 10

    let grinc = "grinIdris2-exe"
    let grinCMD =
            grinc
            ++ " \"" ++ (outDir </> outFile ++ "_app")
            ++ "\" \""  ++ outGrinFile ++ "\""
            ++ (if doLog then " --logging" else "")
            ++ (if saveIR then " --save-ir" else "")
            ++ (case post of 
                    Eval => " --eval"
                    EvalWithStats => " --eval-stats"
                    SaveLLVM => " --save-llvm \"" ++ (outDir </> outFile) ++ "\"")

    unverifiedLogC "grin" 10 $ pure grinCMD
    unless skipCG $ (coreLift $ system grinCMD) >>= \case
        0 => pure ()
        errno => throw $ InternalError $ "grinIdris2-exe returned error " ++ show errno

    pure $ Just outGrinFile

executeExpr :
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    ClosedTerm -> Core ()
executeExpr d tmpDir term = do
    ds <- getDirectives (Other "grin")
    if getDoStats ds
        then ignore $ compileExpr EvalWithStats d tmpDir tmpDir term "execute"
        else ignore $ compileExpr Eval d tmpDir tmpDir term "execute"

export
grin : Codegen
grin = MkCG (compileExpr SaveLLVM) executeExpr

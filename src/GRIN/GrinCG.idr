module GRIN.GrinCG

import Core.Core
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
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
import GRIN.PrettyCompatB
import GRIN.Pipeline
import GRIN.Name
import GRIN.GrinM

getSaveIR : List String -> Bool
getSaveIR [] = False
getSaveIR (d :: ds) = trim d == "save-ir" || getSaveIR ds

ShowB GName where
    showB = showB @{FromShow}

compileExpr :
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    (outDir : String) ->
    ClosedTerm ->
    (outFile : String) ->
    Core (Maybe String)
compileExpr d tmpDir outDir term outFile = do
    let tmpDir = outDir </> (outFile ++ "_app")
    let outGrinFile = outDir </> outFile <.> "grin"
    let mkGrinFile = \file => tmpDir </> file <.> "grin"

    ds <- getDirectives (Other "grin")
    let saveIR = getSaveIR ds

    Right _ <- coreLift $ mkdirAll tmpDir
        | Left err => throw $ FileErr tmpDir err

    cdata <- getCompileData True ANF term

    prog0 <- logTime "++ Compile ANF to GRIN" $ compileANF cdata.anf

    prog1 <- logTime "++ Resolve names" $ pure $ runResolveM $ traverseProg resolve prog0

    logTime "++ Run optimisations" $ coreLift_ $ runGrinT (runTransforms
            [ SaveGrin saveIR (mkGrinFile "000_ANF")
            , O $ Fix [ NormaliseBind ]
            , SaveGrin saveIR (mkGrinFile "001_bind_normalise")
            , O CopyPropogation
            , SaveGrin saveIR (mkGrinFile "002_copy_prop" )
            , O $ Fix
                [ UnusedFunctionElim
                , UnusedConstructorElim
                ]
            , SaveGrin saveIR (mkGrinFile "003_unused_function_constructor")
            , O $ Fix [ UnusedParamElim ]
            , SaveGrin saveIR (mkGrinFile "004_unused_parameter")
            , O CaseSimplify
            , SaveGrin saveIR (mkGrinFile "005_case_simplify")
            , O $ NormaliseBind
            , SaveCalls saveIR (tmpDir </> "calls_graph")
            , SaveCalledBy saveIR (tmpDir </> "called_by_graph")
            , SaveGrin True outGrinFile
            ]) prog1

    pure $ Just outGrinFile

executeExpr :
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    ClosedTerm -> Core ()
executeExpr d tmpDir term = do
    Just grinFile <- compileExpr d tmpDir tmpDir term "execute"
        | Nothing => throw $ InternalError "compileExpr returned Nothing"
    coreLift_ $ system $ "grin " ++ grinFile ++ " --eval"

export
grin : Codegen
grin = MkCG compileExpr executeExpr

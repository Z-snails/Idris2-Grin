module GRIN.GRIN

import Libraries.Utils.Path

import System
import System.File

import Core.Core
import Core.TT
import Core.Context
import Core.Instances

import Compiler.Common
import Compiler.Inline
import Compiler.Pipeline

import GRIN.Syntax
import GRIN.ANF
import GRIN.Pretty
import GRIN.Optimisations.SimpleUnusedParameterElimination

compileExpr :
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    (outDir : String) ->
    ClosedTerm ->
    (outFile : String) ->
    Core (Maybe String)
compileExpr d tmpDir outDir term outFile = do
    let outGrinFile = outDir </> outFile <.> "grin"
        grin = "grin" -- for now hardcoded, maybe make configurable later

    cdata <- getCompileData True ANF term
    prettyProg <- runPipeline
        [ anfToGrin
        , liftTI Core.pure simpleUnusedParameterElimination
        , liftTI Core.pure prettyGrin
        ] cdata.anf

    Right () <- coreLift $ writeFile outGrinFile prettyProg
        | Left err => throw $ FileErr outGrinFile err

    pure $ Just outGrinFile

executeExpr :
    Ref Ctxt Defs ->
    (tmpDir : String) ->
    ClosedTerm -> Core ()
executeExpr d tmpDir term = do
    Just grinFile <- compileExpr d tmpDir tmpDir term "execute"
        | Nothing => throw $ InternalError "compileExpr returned Nothing"
    coreLift_ $ system "grin -q execute.grin"

export
grin : Codegen
grin = MkCG compileExpr executeExpr
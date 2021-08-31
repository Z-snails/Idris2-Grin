module Main (main) where

import Control.Exception
import Data.Functor
import qualified Data.Text.IO as T
import qualified Text.Megaparsec as M
import System.Environment
import System.FilePath

import Idris2.PrimOps
import Idris2.EvalPrimOp
import Grin.Grin
import Grin.Parse
import Pipeline.Pipeline

parseOpts :: [String] -> PipelineOpts -> PipelineOpts
parseOpts [] opt = opt
parseOpts ("--save-ir" : opts) opt = parseOpts opts opt
parseOpts ("--logging" : opts) opt = parseOpts opts $ opt { _poLogging = True }
parseOpts (_ : opts) opt = parseOpts opts opt

idris2Opts :: FilePath -> [String] -> PipelineOpts
idris2Opts outDir opts = parseOpts opts $ defaultOpts
    { _poOutputDir = outDir
    , _poLogging = False
    , _poFailOnLint = False
    }

postPipeline :: [String] -> [PipelineStep]
postPipeline [] = []
postPipeline ("--save-llvm" : llvm : opts) = SaveLLVM (Abs llvm) : postPipeline opts
postPipeline ("--eval" : opts) = PureEvalPlugin evalPrimOp False : postPipeline opts
postPipeline ("--eval-stats" : opts) = PureEvalPlugin evalPrimOp True : postPipeline opts
postPipeline (_ : opts) = postPipeline opts

doOptimise :: [String] -> Bool
doOptimise [] = True
doOptimise ("--eval" : opts) = False
doOptimise ("--eval-stats" : opts) = False
doOptimise (_ : opts) = doOptimise opts

help :: String
help = unlines
    [ "Grin compiler for idris2grin"
    , "Usage:"
    , "  grinIdris2-exe <working directory> <input file>.grin [options]"
    , ""
    , "Options:"
    , "  --logging              enable logging"
    , "  --save-ir              save intermediate grin files"
    , "  --eval                 run pure evaluator"
    , "  --eval-stats           run pure evaluator with statistics"
    , "  --save-llvm <file>     save llvm to file."
    ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        [ "--help" ] -> putStrLn help
        (workingDir : input : opts) -> do
            content <- T.readFile input
            (typeEnv, prog0) <- either (throwIO . userError . M.errorBundlePretty) pure $ parseGrinWithTypes input content
            let prog1 = concatPrograms [idris2PrimOps, prog0]
            let doOpts = doOptimise opts
            if doOpts
                then void $ optimize (idris2Opts workingDir opts) prog1 [] (postPipeline opts)
                else void $ optimizeWith (idris2Opts workingDir opts) prog1 [] [] (postPipeline opts)
        _ -> throwIO $ userError "Unrecognised options"

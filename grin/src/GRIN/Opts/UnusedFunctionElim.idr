module GRIN.Opts.UnusedFunctionElim

import Data.List as List
import Data.Maybe
import Data.SortedSet
import Data.SortedMap as Map

import GRIN.AST
import GRIN.GrinM

export
unusedFuncElim : Ord name => GrinM name ()
unusedFuncElim = do
    used <- getCalls
    MkProg exts defs main <- gets prog
    let isUsed : name -> Bool
        isUsed = \n => isJust $ lookup n used
        addUsed : name -> a -> SortedMap name a -> SortedMap name a
        addUsed = \n => if isUsed n then insert n else const id
        usedDefs : SortedMap name (Def name)
        usedDefs = foldr (uncurry addUsed) empty $ toList defs
        usedExts : SortedMap name (Extern name)
        usedExts = foldr (uncurry addUsed) empty $ toList exts
    putProg $ MkProg usedExts usedDefs main

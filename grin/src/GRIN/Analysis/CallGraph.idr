module GRIN.Analysis.CallGraph

import Data.Maybe
import Data.SortedMap as Map
import Data.SortedSet as Set

import GRIN.AST
import GRIN.Analysis

callsSExp : SExp name -> SortedSet name -> SortedSet name
callsExp : Exp name -> SortedSet name -> SortedSet name

callsSExp (Do e) = callsExp e
callsSExp (App fn _) = insert fn
callsSExp _ = id

callsExp (SimpleExp e) m = callsSExp e m
callsExp (Bind _ rhs rest) m = callsExp rest $ callsSExp rhs m
callsExp (Case _ alts) m = foldr (callsExp . altExp) m alts

||| Get the call graph for all functions called by `def`.
callGraphDef : Ord name => SortedMap name (Def name) -> (fn : name) -> CallGraph name -> CallGraph name
callGraphDef defs fn cg = case lookup fn cg of
    Nothing => case lookup fn defs of
        Just (MkDef _ _ exp _) =>
            let calls = callsExp exp empty
            in foldr (callGraphDef defs) (insert fn calls cg) calls
        Nothing => cg
    Just _ => cg

||| Get the call graph for all functions (transitively) called by main
export
callsGraph : Ord name => Prog name -> CallGraph name
callsGraph (MkProg _ defs main) = case lookup main defs of
    Nothing => empty
    Just (MkDef fn _ _ _) => callGraphDef defs fn empty

export
calledByGraph : Ord name => CallGraph name -> CallGraph name
calledByGraph calls = foldl go empty (Map.toList calls)
  where
    go : CallGraph name -> (name, SortedSet name) -> CallGraph name
    go cg0 (caller, callees) = foldl (\cg, callee => case lookup callee cg of
        Nothing => insert callee (singleton caller) cg
        Just callers => insert callee (insert caller callers) cg) cg0 callees

export
showCallGraph : Show name => CallGraph name -> String
showCallGraph cg = fastConcat $ showCalls <$> toList cg
  where
    showCalls : (name, SortedSet name) -> String
    showCalls (fn, fns) = fastConcat [show fn, ": ", show $ Set.toList fns, "\n"]

module GRIN.Analysis.Inline

import Data.List
import Data.Num.Implementations
import Data.SortedMap as Map
import Data.SortedMap.Extra
import Data.SortedSet as Set

import GRIN.AST
import GRIN.GrinM

[SemigroupMergeLeft] Semigroup (SortedMap k v) where
    (<+>) = mergeLeft

[MonoidMergeLeft] Ord k => Monoid (SortedMap k v) using SemigroupMergeLeft where
    neutral = empty

simpleDef : Ord name => Def name -> SortedMap name (Def name)
simpleDef (MkDef fn _ (SimpleExp (Do _)) _) = empty
simpleDef def@(MkDef fn _ (SimpleExp _) _) = singleton fn def
simpleDef _ = empty

export
inlineSimpleDefs : Ord name => Monad m => GrinT name m ()
inlineSimpleDefs = do
    MkProg _ defs m <- gets prog
    modify $ record { toInline =
        delete m $ foldMap @{%search} @{MonoidMergeLeft} simpleDef defs }

calledSExp : Eq name => name -> SExp name -> Nat
calledExp : Eq name => name -> Exp name -> Nat

calledSExp fn (Do e) = calledExp fn e
calledSExp fn (App fn' _) = if fn == fn' then 1 else 0
calledSExp _ _ = 0

calledExp fn (SimpleExp e) = calledSExp fn e
calledExp fn (Bind _ rhs rest) = calledSExp fn rhs + calledExp fn rest
calledExp fn (Case _ alts) = foldMap @{%search} @{Additive} (calledExp fn . altExp) alts

export
inlineUsedOnce : Ord name => Monad m => GrinT name m ()
inlineUsedOnce = do
    ds <- gets $ defs . prog
    cg <- getCalls
    let toInline = foldr (addOne ds) empty $ Map.toList cg
    modify $ record { toInline = toInline }
  where
    addOne : SortedMap name (Def name) -> (name, SortedSet name) -> SortedMap name (Def name) -> SortedMap name(Def name) 
    addOne ds (fn, callers) ins = case Set.toList callers of
        [caller] => case lookup caller ds of
            Just callerDef => if calledExp fn (callerDef.body) <= 1
                then case lookup fn ds of
                    Just def => insert fn def ins
                    Nothing => ins
                else ins
            Nothing => ins
        _ => ins

||| Unfinished
module ANF.Optimisations.SimpleUnusedParameterElimination

-- I have realised this might be hard because an AApp might try applying a
-- function that doesn't need any more arguments, so I will do this in grin
-- for now

import Data.SortedSet
import Data.SortedMap
import Data.List

import Core.Name

import Compiler.ANF

collectWhen : Ord a => Bool -> a -> SortedSet a
collectWhen True i = singleton i
collectWhen False _ = empty

collectUsedAVar : List Int -> AVar -> SortedSet Int
collectUsedAVar _ ANull = empty
collectUsedAVar params (ALocal i) = collectWhen (i `elem` params) i

mutual
    collectUsedANF : List Int -> ANF -> SortedSet Int
    collectUsedANF params = \case
        AV _ var => collectUsedAVar params var
        AAppName _ _ _ args => foldMap (collectUsedAVar params) args
        AUnderApp _ _ _ args => foldMap (collectUsedAVar params) args
        AApp _ _ clos arg => collectUsedAVar params clos <+> collectUsedAVar params arg
        ALet _ _ rhs rest => collectUsedANF params rhs <+> collectUsedANF params rest
        ACon _ _ _ args => foldMap (collectUsedAVar params) args
        AOp _ _ _ args => foldMap (collectUsedAVar params) args
        AExtPrim _ _ _ args => foldMap (collectUsedAVar params) args
        AConCase _ arg alts def =>
            collectUsedAVar params arg <+>
            foldMap (collectUsedAConAlt params) alts <+>
            foldMap (collectUsedANF params) def
        AConstCase _ arg alts def =>
            collectUsedAVar params arg <+>
            foldMap (collectUsedAConstAlt params) alts <+>
            foldMap (collectUsedANF params) def
        APrimVal _ _ => empty
        AErased _ => empty
        ACrash _ _ => empty

    collectUsedAConAlt : List Int -> AConAlt -> SortedSet Int
    collectUsedAConAlt params (MkAConAlt _ _ _ exp) = collectUsedANF params exp

    collectUsedAConstAlt : List Int -> AConstAlt -> SortedSet Int
    collectUsedAConAlt params (MkAConstAlt _ exp) = collectUsedANF params exp

collectUsedDef : ANFDef -> SortedSet Int
collectUsedDef (MkAFun args exp) = collectUsedANF args exp
collectUsedDef _ = empty

number : List a -> List (Nat, a)
number = number' 0
  where
    number' : Nat -> List a -> List (Nat, a)
    number' _ [] = []
    number' i (x :: xs) = (i, x) :: number' (i + 1) xs

removeUnusedArgs : SortedSet Nat -> List Int -> List Int
removeUnusedArgs unused args = [arg | (idx, arg) <- number args, not $ contains idx unused]

removeUnusedANF : SortedMap Name (SortedSet Nat) -> ANF -> ANF

removeUnusedDef : SortedMap Name (SortedSet Nat) -> (Name, ANFDef) -> (Name, ANFDef)
removeUnusedDef unused (n, MkAFun args exp) =
    case lookup n unused of
        Just un =>
            (n, MkAFun (removeUnusedArgs un args) (removeUnusedANF unused exp))
        Nothing => (n, MkAFun args exp)
removeUnusedDef _ def = def

simpleUnusedParameterElimination : List (Name, ANFDef) -> List (Name, ANFDef)
simpleUnusedParameterElimination defs =
    let unusedArgsInDef : ANFDef -> SortedSet Nat
        unusedArgsInDef def@(MkAFun args _) =
            let used = collectUsedDef def
                go : (Nat, Int) -> SortedSet Nat
                go = \(idx, arg) => collectWhen (not $ contains arg used) idx
            in foldMap go $ number args
        unusedArgsInDef _ = empty
        
        unusedDefMap : SortedMap Name (SortedSet Nat)
        unusedDefMap = foldMap (\(n, def) => singleton n $ unusedArgsInDef def) defs
    in map (removeUnusedDef unusedDefMap) defs
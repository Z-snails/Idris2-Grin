module GRIN.Optimisations.SimpleUnusedParameterElimination

import Data.SortedSet
import Data.SortedMap

import Core.Name

import Compiler.Pipeline

import GRIN.Syntax

number : List a -> List (Nat, a)
number = number' 0
  where
    number' : Nat -> List a -> List (Nat, a)
    number' _ [] = []
    number' i (x :: xs) = (i, x) :: number' (i + 1) xs

collectWhen : Ord a => Bool -> a -> SortedSet a
collectWhen True a = singleton a
collectWhen False _ = empty

collectUsedVar : SortedSet GrinVar -> GrinVar -> SortedSet GrinVar
collectUsedVar params var = collectWhen (contains var params) var

collectUsedSVal : SortedSet GrinVar -> SimpleVal -> SortedSet GrinVar
collectUsedSVal params = \case
    SLit _ => empty
    SVar var => collectUsedVar params var
    SUndefined _ => empty

collectUsedVal : SortedSet GrinVar -> Val -> SortedSet GrinVar
collectUsedVal params = \case
    VTagNode _ args => foldMap (collectUsedSVal params) args
    VTag _ => empty
    VSimpleVal val => collectUsedSVal params val
    VUnit => empty

mutual
    collectUsedSExp : SortedSet GrinVar -> SimpleExp -> SortedSet GrinVar
    collectUsedSExp params = \case
        Do exp => collectUsedExp params exp
        App _ args => foldMap (collectUsedVar params) args
        Pure val => collectUsedVal params val
        Store val => collectUsedVal params val
        Fetch var => collectUsedVar params var
        Update var val => collectUsedVar params var <+> collectUsedVal params val

    collectUsedExp : SortedSet GrinVar -> GrinExp -> SortedSet GrinVar
    collectUsedExp params = \case
        Bind _ rhs rest => collectUsedSExp params rhs <+> collectUsedExp params rest
        Case val alts =>
            collectUsedVal params val <+>
            foldMap (collectUsedAlt params) alts
        Simple exp => collectUsedSExp params exp

    collectUsedAlt : SortedSet GrinVar -> GrinAlt -> SortedSet GrinVar
    collectUsedAlt params (MkAlt _ exp) = collectUsedExp params exp

UsedVarMap : Type
UsedVarMap = SortedMap GrinVar (SortedSet Nat)

collectUsedDef : GrinDef -> UsedVarMap
collectUsedDef (MkDef n params exp) =
    let used = toList $ collectUsedExp (fromList params) exp
    in singleton n $ fromList [idx | (idx, arg) <- number params, arg `elem` used]

collectUsedProg : GrinProg -> UsedVarMap
collectUsedProg (MkProg _ defs) = foldMap collectUsedDef defs

getName : Tag -> Maybe GrinVar
getName (MkTag ty n) = case ty of
    Thunk => Just n
    InfThunk => Just n
    Missing _ => Just n
    _ => Nothing

varUsed : UsedVarMap -> GrinVar -> Nat -> Bool
varUsed nm n idx = case lookup n nm of
    Nothing => True
    Just used => contains idx used

removeUnusedArgs : UsedVarMap -> GrinVar -> List a -> List a
removeUnusedArgs nm n xs = [x | (idx, x) <- number xs, varUsed nm n idx]

removeUnusedVal : UsedVarMap -> Val -> Val
removeUnusedVal nm = \case
    val@(VTagNode tag args) => case getName tag of
        Nothing => val
        Just n => case removeUnusedArgs nm n args of
                [] => VTag tag
                args' => VTagNode tag args
    val => val

mutual
    removeUnusedSExp : UsedVarMap -> SimpleExp -> SimpleExp
    removeUnusedSExp nm = \case
        Do exp => Do (removeUnusedExp nm exp)
        App n args => App n (removeUnusedArgs nm n args)
        Pure val => Pure (removeUnusedVal nm val)
        Store val => Store (removeUnusedVal nm val)
        Fetch var => Fetch var
        Update var val => Update var (removeUnusedVal nm val)

    removeUnusedExp : UsedVarMap -> GrinExp -> GrinExp
    removeUnusedExp nm = \case
        Bind val rhs rest => Bind val (removeUnusedSExp nm rhs) (removeUnusedExp nm rest)
        Case val alts => Case val (removeUnusedAlt nm <$> alts)
        Simple exp => Simple (removeUnusedSExp nm exp)
    
    removeUnusedAlt : UsedVarMap -> GrinAlt -> GrinAlt
    removeUnusedAlt nm (MkAlt pat exp) = MkAlt pat (removeUnusedExp nm exp)

removeUnusedDef : UsedVarMap -> GrinDef -> GrinDef
removeUnusedDef nm (MkDef n args exp) =
    MkDef n (removeUnusedArgs nm n args) (removeUnusedExp nm exp)

removeUnusedProg : UsedVarMap -> GrinProg -> GrinProg
removeUnusedProg nm (MkProg exts defs) = MkProg exts (removeUnusedDef nm <$> defs)

export
simpleUnusedParameterElimination : TransInfo (\x => x) GrinProg GrinProg
simpleUnusedParameterElimination =
    MkTI \prog =>
        let nm = collectUsedProg prog
        in removeUnusedProg nm prog
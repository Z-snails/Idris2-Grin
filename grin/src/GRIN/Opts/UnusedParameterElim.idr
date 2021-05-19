module GRIN.Opts.UnusedParameterElim

import Data.SortedSet as Set
import Data.SortedMap

import GRIN.AST
import GRIN.GrinM

number : List a -> List (Nat, a)
number = number' 0
  where
    number' : Nat -> List a -> List (Nat, a)
    number' _ [] = []
    number' i (x :: xs) = (i, x) :: number' (i + 1) xs

collectWhen : Bool -> a -> SortedSet a -> SortedSet a
collectWhen True a = insert a
collectWhen False _ = id

collectUsedVar : SortedSet Var -> Var -> SortedSet Var -> SortedSet Var
collectUsedVar params var m = collectWhen (contains var params) var m

collectUsedSVal : SortedSet Var -> SVal -> SortedSet Var -> SortedSet Var
collectUsedSVal params = \case
    SLit _ => id
    SVar var => collectUsedVar params var

collectUsedVal : SortedSet Var -> Val name -> SortedSet Var -> SortedSet Var
collectUsedVal params v m = case v of
    SimpleVal val => collectUsedSVal params val m
    ConstTagNode _ args => foldr (collectUsedSVal params) m args
    ConstTag _ => m
    VarTagNode _ args => foldr (collectUsedSVal params) m args
    VUnit => m

mutual
    collectUsedSExp : SortedSet Var -> SExp name -> SortedSet Var -> SortedSet Var
    collectUsedSExp params e m = case e of
        Do exp => collectUsedExp params exp m
        App _ args => foldr (collectUsedVar params) m args
        Pure val => collectUsedVal params val m
        Store val => collectUsedVal params val m
        Fetch _ var => collectUsedVar params var m
        FetchI _ _ var => collectUsedVar params var m
        Update var val => collectUsedVar params var $ collectUsedVal params val m

    collectUsedExp : SortedSet Var -> Exp name -> SortedSet Var -> SortedSet Var
    collectUsedExp params e m = case e of
        SimpleExp exp => collectUsedSExp params exp m
        Bind _ rhs rest => collectUsedSExp params rhs $ collectUsedExp params rest m
        Case val alts =>
            collectUsedVal params val
            $ foldr (collectUsedExp params . altExp) m alts

    -- collectUsedAlt : SortedSet Var -> Alt name -> SortedSet Var -> SortedSet Var
    -- collectUsedAlt params (MkAlt _ exp) = collectUsedExp params exp

0 UsedVarMap : Type -> Type
UsedVarMap name = SortedMap name (SortedSet Nat)

collectUsedDef : Ord name => Def name -> (name, SortedSet Nat)
collectUsedDef (MkDef n params exp _) =
    let used = Set.toList $ collectUsedExp (fromList params) exp empty
    in (n, fromList [idx | (idx, arg) <- number params, arg `elem` used])

getFnName : Tag name -> Maybe name
getFnName (MkTag ty n) = case ty of
    UThunk => Just n
    NUThunk => Just n
    Partial _ => Just n
    _ => Nothing

removeUnusedArgs : UsedVarMap name -> name -> List a -> List a
removeUnusedArgs nm n xs =
    let usedVars = lookup n nm
        idxUsed : Nat -> Bool
        idxUsed = \idx => case usedVars of
            Nothing => True
            Just used => contains idx used
    in [x | (idx, x) <- number xs, idxUsed idx]

removeUnusedVal : UsedVarMap name -> Val name -> Val name
removeUnusedVal nm = \case
    val@(ConstTagNode tag args) => case getFnName tag of
        Nothing => val
        Just n => ConstTagNode tag $ removeUnusedArgs nm n args
    val => val

removeUnusedCPat : UsedVarMap name -> CasePat name -> CasePat name 
removeUnusedCPat nm pat@(NodePat tag args) = case getFnName tag of
    Nothing => pat
    Just n => NodePat tag $ removeUnusedArgs nm n args
removeUnusedCPat _ pat = pat

mutual
    removeUnusedSExp : UsedVarMap name -> SExp name -> SExp name
    removeUnusedSExp nm = \case
        Do exp => Do (removeUnusedExp nm exp)
        App n args => App n (removeUnusedArgs nm n args)
        Pure val => Pure (removeUnusedVal nm val)
        Store val => Store (removeUnusedVal nm val)
        Fetch i var => Fetch i var
        FetchI i n var => FetchI i n var
        Update var val => Update var (removeUnusedVal nm val)

    removeUnusedExp : UsedVarMap name -> Exp name -> Exp name
    removeUnusedExp nm = \case
        SimpleExp exp => SimpleExp (removeUnusedSExp nm exp)
        Bind val rhs rest => Bind val (removeUnusedSExp nm rhs) (removeUnusedExp nm rest)
        Case val alts => Case val (removeUnusedAlt nm <$> alts)
    
    removeUnusedAlt : UsedVarMap name -> Alt name -> Alt name
    removeUnusedAlt nm (MkAlt pat exp) = MkAlt (removeUnusedCPat nm pat) (removeUnusedExp nm exp)

removeUnusedDef : UsedVarMap name -> Def name -> Def name
removeUnusedDef nm (MkDef n args exp ty) =
    MkDef n (removeUnusedArgs nm n args) (removeUnusedExp nm exp) Nothing

removeUnusedProg : UsedVarMap name -> SortedMap name (Def name) -> SortedMap name (Def name)
removeUnusedProg nm defs = removeUnusedDef nm <$> defs

Semigroup (Prog name) where
    p <+> _ = p

export
unusedParamElim : Ord name => GrinM name ()
unusedParamElim = do
    MkProg exts defs m <- gets prog
    let nm = foldMap (uncurry singleton . collectUsedDef) defs
    putProg $ MkProg exts (removeUnusedProg nm defs) m

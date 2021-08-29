module GRIN.Opts.UnusedVarElim

import Data.SortedSet as Set
import Data.SortedMap

import GRIN.AST
import GRIN.GrinM

collectUsedSVal : SVal -> SortedSet Var
collectUsedSVal (SVar x) = singleton x
collectUsedSVal (SLit x) = empty

collectUsedVal : Val name -> SortedSet Var
collectUsedVal (SimpleVal x) = collectUsedSVal x
collectUsedVal (ConstTagNode x xs) = foldMap collectUsedSVal xs
collectUsedVal (ConstTag x) = empty
collectUsedVal (VarTagNode x xs) = insert x $ foldMap collectUsedSVal xs
collectUsedVal VUnit = empty

mutual
    collectUsedSExp : SExp name -> SortedSet Var
    collectUsedSExp (Do x) = collectUsedExp x
    collectUsedSExp (App x xs) = fromList xs
    collectUsedSExp (Pure x) = collectUsedVal x
    collectUsedSExp (Store x) = collectUsedVal x
    collectUsedSExp (Fetch x y) = singleton y
    collectUsedSExp (FetchI x k y) = singleton y
    collectUsedSExp (Update x y) = empty

    collectUsedExp : Exp name -> SortedSet Var
    collectUsedExp (SimpleExp x) = collectUsedSExp x
    collectUsedExp (Bind x y z) = collectUsedSExp y <+> collectUsedExp z
    collectUsedExp (Case x xs) = collectUsedVal x <+> foldMap collectUsedAlt xs

    collectUsedAlt : Alt name -> SortedSet Var
    collectUsedAlt (MkAlt _ exp) = collectUsedExp exp

mutual
    pureSExp : SExp name -> Bool
    pureSExp (Do x) = pureExp x
    pureSExp (App x xs) = False -- TODO: effect tracking
    pureSExp (Update x y) = False
    pureSExp _ = True

    pureExp : Exp name -> Bool
    pureExp (SimpleExp x) = pureSExp x
    pureExp (Bind x y z) = pureSExp y && pureExp z
    pureExp (Case x xs) = all pureAlt xs

    pureAlt : Alt name -> Bool
    pureAlt (MkAlt _ exp) = pureExp exp

parameters (used : SortedSet Var)
  mutual
    removeUnusedSExp : SExp name -> SExp name
    removeUnusedSExp (Do x) = mkDo $ removeUnusedExp x
    removeUnusedSExp exp = exp

    removeUnusedExp : Exp name -> Exp name
    removeUnusedExp (SimpleExp x) = mkSimpleExp $ removeUnusedSExp x
    removeUnusedExp (Bind v@(SimpleVal $ SVar x) y z) = if contains x used || not (pureSExp y)
        then Bind v (removeUnusedSExp y) (removeUnusedExp z)
        else removeUnusedExp z
    removeUnusedExp (Bind v y z) = Bind v (removeUnusedSExp y) (removeUnusedExp z)
    removeUnusedExp (Case x xs) = Case x $ removeUnusedAlt <$> xs

    removeUnusedAlt : Alt name -> Alt name
    removeUnusedAlt (MkAlt pat exp) = MkAlt pat $ removeUnusedExp exp

removeUnusedDef : Def name -> Def name
removeUnusedDef def =
    let used = collectUsedExp def.body
     in record { body $= removeUnusedExp used } def

export
unusedVarElim : Monad m => Ord name => GrinT name m ()
unusedVarElim = do
    p@(MkProg exts defs _) <- gets prog
    putProg $ record { defs = map removeUnusedDef defs } p
    -- invalidate CallGraph

module GRIN.Opts.UnusedConstructorElim

import Data.List
import Data.SortedSet
import Data.SortedMap

import GRIN.AST
import GRIN.GrinM

collectVal : Ord name => Val name -> SortedSet (Tag name)
collectVal (ConstTagNode t _) = singleton t
collectVal (ConstTag t) = singleton t
collectVal _ = empty

mutual
    collectSExp : Ord name => SExp name -> SortedSet (Tag name)
    collectSExp (Do e) = collectExp e
    collectSExp (Pure v) = collectVal v
    collectSExp (Store v) = collectVal v
    collectSExp (Update _ v) = collectVal v
    collectSExp _ = empty

    collectExp : Ord name => Exp name -> SortedSet (Tag name)
    collectExp (SimpleExp e) = collectSExp e
    collectExp (Bind _ rhs rest) = collectSExp rhs `union` collectExp rest
    collectExp (Case _ alts) = foldMap collectAlt alts

    collectAlt : Ord name => Alt name -> SortedSet (Tag name)
    collectAlt (MkAlt pat e) = case getPatTag pat of
        Just t => delete t $ collectExp e
        Nothing => collectExp e

collectDef : Ord name => Def name -> SortedSet (Tag name)
collectDef = collectExp . body

removeExp : Ord name => SortedSet (Tag name) -> Exp name -> Exp name
removeExp cons (SimpleExp e) = SimpleExp $ mapExpSExp (removeExp cons) e
removeExp cons (Bind val rhs rest) = Bind val (mapExpSExp (removeExp cons) rhs) $ removeExp cons rest
removeExp cons (Case val alts) = Case val $ filter pred alts
  where
    pred : Alt name -> Bool
    pred (MkAlt pat _) = case getPatTag pat of
        Just con => contains con cons
        Nothing => True

export
unusedConsElim : Ord name => GrinM name ()
unusedConsElim = do
    p@(MkProg exts defs _) <- gets prog
    let used = foldMap collectDef defs
    putProg $ mapExpProg (removeExp used) p
    invalidate CallGraphs

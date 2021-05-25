module GRIN.Analysis.MaxVar

import Data.SortedMap
import GRIN.AST

Semigroup Var where
    MkVar x <+> MkVar y = MkVar (max x y)

Monoid Var where
    neutral = MkVar 0

maxVarSVal : SVal -> Var
maxVarSVal (SVar v) = v
maxVarSVal _ = neutral

maxVarVal : Val name -> Var
maxVarVal (SimpleVal v) = maxVarSVal v
maxVarVal (ConstTagNode _ vs) = foldMap maxVarSVal vs
maxVarVal (VarTagNode v vs) = v <+> foldMap maxVarSVal vs
maxVarVal _ = neutral

maxVarCPat : CasePat name -> Var
maxVarCPat (NodePat _ vs) = concat vs
maxVarCPat _ = neutral

mutual
    maxVarSExp : SExp name -> Var
    maxVarSExp (Do e) = maxVarExp e
    maxVarSExp (App _ vs) = concat vs
    maxVarSExp (Pure v) = maxVarVal v
    maxVarSExp (Store v) = maxVarVal v
    maxVarSExp (Fetch _ v) = v
    maxVarSExp (FetchI _ _ v) = v
    maxVarSExp (Update v1 v2) = v1 <+> maxVarVal v2

    maxVarExp : Exp name -> Var
    maxVarExp (SimpleExp e) = maxVarSExp e
    maxVarExp (Bind v rhs rest) = maxVarVal v <+> maxVarSExp rhs <+> maxVarExp rest
    maxVarExp (Case v alts) = maxVarVal v <+> foldMap maxVarAlt alts

    maxVarAlt : Alt name -> Var
    maxVarAlt (MkAlt pat exp) = maxVarCPat pat <+> maxVarExp exp

maxVarDef : Def name -> Var
maxVarDef (MkDef _ as e _) = concat as <+> maxVarExp e

export
maxVar : Prog name -> Var
maxVar (MkProg _ defs _) = foldMap maxVarDef defs

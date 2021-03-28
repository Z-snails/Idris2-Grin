-- I don't know if this will work without full heap points-to analysis so I'll leave it out for now

module Grin.Optimisations.SimpleUnusedConstructorElimination

import Data.List
import Data.SortedSet

import Compiler.Pipeline

import Grin.Syntax

collectUsedVal : Val -> SortedSet Tag
collectUsedVal (VTagNode tag _) = singleton tag
collectUsedVal (VTag tag) = singleton tag
collectUsedVal _ = empty

mutual
    collectUsedSExp : SimpleExp -> SortedSet Tag
    collectUsedSExp (Do exp) = collectUsedExp exp
    collectUsedSExp (App _ _) = empty
    collectUsedSExp (Pure val) = collectUsedVal val
    collectUsedSExp (Store val) = collectUsedVal val
    collectUsedSExp (Fetch _) = empty
    collectUsedSExp (Update _ val) = collectUsedVal val

    collectUsedExp : GrinExp -> SortedSet Tag
    collectUsedExp (Bind val rhs rest) =
        collectUsedVal val <+>
        collectUsedSExp rhs <+>
        collectUsedExp rest
    collectUsedExp (Case val alts) =
        collectUsedVal val <+>
        foldMap collectUsedAlt alts
    collectUsedExp (Simple exp) =
        collectUsedSExp exp
    
    collectUsedAlt : GrinAlt -> SortedSet Tag
    collectUsedAlt (MkAlt pat exp) = maybe id delete (getCaseTag pat) (collectUsedExp exp)

collectUsedDef : GrinDef -> SortedSet Tag
collectUsedDef (MkDef _ _ exp) = collectUsedExp exp

collectUsedProg : GrinProg -> SortedSet Tag
collectUsedProg (MkProg _ defs) = foldMap collectUsedDef defs

isUsed : SortedSet Tag -> CasePat -> Bool
isUsed used (NodePat tag _) = contains tag used
isUsed used (TagPat tag) = contains tag used
isUsed _ _ = False

mutual
    removeUnusedSExp : SortedSet Tag -> SimpleExp -> SimpleExp
    removeUnusedSExp used (Do exp) = Do (removeUnusedExp used exp)
    removeUnusedSExp _ exp = exp

    removeUnusedExp : SortedSet Tag -> GrinExp -> GrinExp
    removeUnusedExp used (Bind val rhs rest) = Bind val (removeUnusedSExp used rhs) rest
    removeUnusedExp used (Case val alts) = Case val (mapMaybe (removeUnusedAlt used) alts)
    removeUnusedExp used (Simple exp) = Simple (removeUnusedSExp used exp)

    removeUnusedAlt : SortedSet Tag -> GrinAlt -> Maybe GrinAlt
    removeUnusedAlt used (MkAlt pat exp) = guard (isUsed used pat) $> MkAlt pat (removeUnusedExp used exp)

removeUnusedDef : SortedSet Tag -> GrinDef -> GrinDef
removeUnusedDef used (MkDef fn args exp) = MkDef fn args (removeUnusedExp used exp)

removeUnusedProg : SortedSet Tag -> GrinProg -> GrinProg
removeUnusedProg used (MkProg ext defs) = MkProg ext (removeUnusedDef used <$> defs)

export
simpleUnusedConstructorElimination : TransInfo (\x => x) GrinProg GrinProg
simpleUnusedConstructorElimination =
    MkTI \prog =>
        let used = collectUsedProg prog
        in removeUnusedProg used prog
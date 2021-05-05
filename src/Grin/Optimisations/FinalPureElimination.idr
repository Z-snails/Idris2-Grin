module Grin.Optimisations.FinalPureElimination

import Compiler.Pipeline

import Grin.Syntax

finalPureExp : GrinExp -> GrinExp
finalPureExp e@(Bind lhs exp (Simple (Pure rhs))) = if lhs == rhs
    then Simple exp
    else e
finalPureExp (Bind lhs exp rest) = Bind lhs exp (finalPureExp rest)
finalPureExp (Case val alts) = Case val (mapAltExp finalPureExp <$> alts)
finalPureExp (Simple exp) = Simple $ mapSimpleExp finalPureExp exp

export
finalPureElimination : TransInfo (\x => x) GrinProg GrinProg
finalPureElimination = MkTI (mapGrinProg finalPureExp)

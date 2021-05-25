module GRIN.Opts.CaseSimplify

import GRIN.AST
import GRIN.GrinM

patToVal : CasePat name -> Val name
patToVal (NodePat tag args) = ConstTagNode tag (SVar <$> args)
patToVal (TagPat tag) = ConstTag tag
patToVal (LitPat lit) = VUnit
patToVal DefaultPat = VUnit

simplify : Exp name -> Exp name
simplify (SimpleExp exp) = SimpleExp $ mapExpSExp simplify exp
simplify (Bind val exp rest) = Bind val (mapExpSExp simplify exp) (simplify rest)
simplify (Case val alts) = case alts of
    [MkAlt DefaultPat exp] => simplify exp
    [MkAlt pat exp] => Bind (patToVal pat) (Pure val) (simplify exp)
    _ => Case val $ map (mapExpAlt simplify) alts

export
caseSimplify : Monad m => GrinT name m ()
caseSimplify = do
    mapProg $ mapExpProg simplify
    invalidate CallGraphs

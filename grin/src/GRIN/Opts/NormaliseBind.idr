module GRIN.Opts.NormaliseBind

import GRIN.AST
import GRIN.GrinM

mutual
    normaliseExp : Exp name -> Exp name
    normaliseExp (SimpleExp (Do e)) = normaliseExp e
    normaliseExp e@(SimpleExp _) = e
    normaliseExp (Bind val (Do e) rest) = bind val e rest
    normaliseExp (Bind val e rest) = Bind val e $ normaliseExp rest
    normaliseExp (Case val alts) = Case val $ mapExpAlt normaliseExp <$> alts

    bind : Val name -> Exp name -> Exp name -> Exp name
    bind v0 e0 = case normaliseExp e0 of
        SimpleExp e1 => Bind v0 e1
        Bind v1 (Do e1) rest => bind v1 e1 . bind v0 rest
        Bind v1 e1 rest => Bind v1 e1 . bind v0 rest
        Case v1 alts => Bind v0 (mkDo $ Case v1 $ mapExpAlt normaliseExp <$> alts)

export
normaliseBind : GrinM name ()
normaliseBind = mapProg $ mapExpProg normaliseExp

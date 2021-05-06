module Grin.Prims.PrimOps

import Grin.Syntax

primopPure :
    (fn : String) ->
    (args : List SimpleType) ->
    (ret : SimpleType) ->
    External
primopPure name args ret = MkExt
    { name
    , retTy = TySimple ret
    , argTy = TySimple <$> args
    , effect = False
    , builtin = True
    }

export
primops : List External
primops = (\(name, args, ret) => primopPure name args ret) <$>
    [ ("idris_add_Int", [Int64Ty, Int64Ty], Int64Ty)
    ]

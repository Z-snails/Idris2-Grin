{-# LANGUAGE QuasiQuotes #-}
module Idris2.PrimOps (
    idris2PrimOps
) where

import Grin.Syntax
import Grin.TH

idris2PrimOps :: Exp
idris2PrimOps = [progConst|

ffi pure
    _prim_add_Integer :: %Integer -> %Integer -> %Integer
    _prim_sub_Integer :: %Integer -> %Integer -> %Integer

primop pure
    _prim_add_Int :: T_Int64 -> T_Int64 -> T_Int64

ffi effectful
    _prim_clear_Integer :: %Integer -> T_Unit
    _prim_print_String :: T_String -> T_Unit

believe_me p0 =
    pure p1

|]
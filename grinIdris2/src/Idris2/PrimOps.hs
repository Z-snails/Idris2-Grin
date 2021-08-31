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
    _prim_cast_String_Integer :: T_String -> %Integer
    _prim_str_append :: T_String -> T_String -> T_String

primop pure
    _prim_add_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_sub_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_mul_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_div_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_lt_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_lte_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_eq_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_gte_Int :: T_Int64 -> T_Int64 -> T_Int64
    _prim_gt_Int :: T_Int64 -> T_Int64 -> T_Int64

ffi effectful
    _prim_clear_Integer :: %Integer -> T_Unit

_prim_believe_me p0 =
    pure p0

|]

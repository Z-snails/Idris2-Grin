{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}

module Idris2.PrimOps (
  idris2PrimOps,
) where

import Data.Bits (Bits (shiftL), FiniteBits (finiteBitSize))
import Data.Maybe
import qualified Data.Text as Text
import Grin.Grin
import Grin.Syntax
import Grin.TH

idris2PrimOps :: Exp
idris2PrimOps =
  concatPrograms
    [ Program [] (generatePrimOp <$> (primops <*> primtypes))
    , [progConst|

ffi pure
    linux "libidris2Grinsupport.so"
    _prim_add_Integer :: %Integer -> %Integer -> %Integer
    _prim_sub_Integer :: %Integer -> %Integer -> %Integer
    _prim_cast_String_Integer :: T_String -> %Integer
    _prim_str_append :: T_String -> T_String -> T_String

primop pure
    _prim_int_add :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_sub :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_mul :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_div :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_and :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_or  :: T_Int64 -> T_Int64 -> T_Int64
    _prim_int_xor :: T_Int64 -> T_Int64 -> T_Int64

    _prim_word_add :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_sub :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_mul :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_div :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_and :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_or  :: T_Word64 -> T_Word64 -> T_Word64
    _prim_word_xor :: T_Word64 -> T_Word64 -> T_Word64

    _prim_int_lt  :: T_Int64 -> T_Int64 -> T_Bool
    _prim_int_lte :: T_Int64 -> T_Int64 -> T_Bool
    _prim_int_eq  :: T_Int64 -> T_Int64 -> T_Bool
    _prim_int_gte :: T_Int64 -> T_Int64 -> T_Bool
    _prim_int_gt  :: T_Int64 -> T_Int64 -> T_Bool

    _prim_word_lt  :: T_Word64 -> T_Word64 -> T_Bool
    _prim_word_lte :: T_Word64 -> T_Word64 -> T_Bool
    _prim_word_eq  :: T_Word64 -> T_Word64 -> T_Bool
    _prim_word_gte :: T_Word64 -> T_Word64 -> T_Bool
    _prim_word_gt  :: T_Word64 -> T_Word64 -> T_Bool

ffi effectful
    linux "libidris2Grinsupport.so"
    _prim_clear_Integer :: %Integer -> T_Unit
    _prim_crash :: T_Unit

_prim_believe_me p0 =
    pure p0

_prim_int_neg _prim_int_neg.0 =
    _prim_int_sub 0 _prim_int_neg.0

|]
    ]
 where
  primops = [OpAdd, OpSub, OpMul, OpDiv, OpNeg, OpShiftL, OpShiftR, OpAnd, OpOr, OpXOr, OpLT, OpLTE, OpEQ, OpGTE, OpGT]
  primtypes = Bounded True Nothing : (Bounded <$> [True, False] <*> [Just 8, Just 16, Just 32, Just 64])

class IdrisName a where
  toIdris :: a -> Name

data IntType = Bounded {signed :: Bool, size :: Maybe Int}

data IdrisPrimop
  = OpAdd IntType
  | OpSub IntType
  | OpMul IntType
  | OpDiv IntType
  | OpNeg IntType
  | OpShiftL IntType
  | OpShiftR IntType
  | OpAnd IntType
  | OpOr IntType
  | OpXOr IntType
  | OpLT IntType
  | OpLTE IntType
  | OpEQ IntType
  | OpGTE IntType
  | OpGT IntType

getType :: IdrisPrimop -> IntType
getType (OpAdd ty) = ty
getType (OpSub ty) = ty
getType (OpMul ty) = ty
getType (OpDiv ty) = ty
getType (OpNeg ty) = ty
getType (OpShiftL ty) = ty
getType (OpShiftR ty) = ty
getType (OpAnd ty) = ty
getType (OpOr ty) = ty
getType (OpXOr ty) = ty
getType (OpLT ty) = ty
getType (OpLTE ty) = ty
getType (OpEQ ty) = ty
getType (OpGTE ty) = ty
getType (OpGT ty) = ty

instance IdrisName IntType where
  toIdris inttype = (if signed inttype then "Int" else "Bits") <> NM (Text.pack (maybe "" show (size inttype)))

instance IdrisName IdrisPrimop where
  toIdris (OpAdd ty) = "_prim_add_" <> toIdris ty
  toIdris (OpSub ty) = "_prim_sub_" <> toIdris ty
  toIdris (OpMul ty) = "_prim_mul_" <> toIdris ty
  toIdris (OpDiv ty) = "_prim_div_" <> toIdris ty
  toIdris (OpNeg ty) = "_prim_neg_" <> toIdris ty
  toIdris (OpShiftL ty) = "_prim_shl_" <> toIdris ty
  toIdris (OpShiftR ty) = "_prim_shr_" <> toIdris ty
  toIdris (OpAnd ty) = "_prim_and_" <> toIdris ty
  toIdris (OpOr ty) = "_prim_or_" <> toIdris ty
  toIdris (OpXOr ty) = "_prim_xor_" <> toIdris ty
  toIdris (OpLT ty) = "_prim_lt_" <> toIdris ty
  toIdris (OpLTE ty) = "_prim_lte_" <> toIdris ty
  toIdris (OpEQ ty) = "_prim_eq_" <> toIdris ty
  toIdris (OpGTE ty) = "_prim_gte_" <> toIdris ty
  toIdris (OpGT ty) = "_prim_gt_" <> toIdris ty

intoBounds :: IntType -> Name -> SimpleExp
intoBounds typ var
  | size typ == Just 64 = SReturn $ Var var
  | isNothing (size typ) = SReturn $ Var var
  | signed typ = SApp "_prim_int_and" [Lit (LInt64 (1 `shiftL` fromMaybe (finiteBitSize @Int 0) (size typ) - 1)), Var var]
  | otherwise = SApp "_prim_word_and" [Lit (LWord64 (1 `shiftL` fromMaybe (finiteBitSize @Int 0) (size typ) - 1)), Var var]

generateBinOp :: IdrisPrimop -> Name -> Def
generateBinOp idris grin =
  let funName = toIdris idris
      x = funName <> ".x"
      y = funName <> ".y"
      res = funName <> ".res"
   in Def funName [x, y] $
        EBind
          (SApp grin [Var x, Var y])
          (Var res)
          (intoBounds (getType idris) res)

generateCmpOp :: IdrisPrimop -> Name -> Def
generateCmpOp idris grin =
  let funName = toIdris idris
      x = funName <> ".x"
      y = funName <> ".y"
      res = funName <> ".res"
   in Def funName [x, y] $
        EBind
          (SApp grin [Var x, Var y])
          (Var res)
          ( ECase
              (Var res)
              [ Alt (LitPat (LBool False)) (SReturn (Lit (LInt64 0)))
              , Alt (LitPat (LBool True)) (SReturn (Lit (LInt64 1)))
              ]
          )

generateUnOp :: IdrisPrimop -> Name -> Def
generateUnOp idris grin =
  let funName = toIdris idris
      x = funName <> ".x"
      res = funName <> ".res"
   in Def funName [x] $
        EBind
          (SApp grin [Var x])
          (Var res)
          (intoBounds (getType idris) res)

generatePrimOp :: IdrisPrimop -> Exp
generatePrimOp grin@(OpAdd ty) = generateBinOp grin "_prim_int_add"
generatePrimOp grin@(OpSub ty) = generateBinOp grin "_prim_int_sub"
generatePrimOp grin@(OpMul ty) = generateBinOp grin "_prim_int_mul"
generatePrimOp grin@(OpDiv ty) = generateBinOp grin "_prim_int_div"
generatePrimOp grin@(OpNeg ty) = generateUnOp grin "_prim_int_neg"
generatePrimOp grin@(OpShiftL ty) = generateBinOp grin "_prim_int_shl"
generatePrimOp grin@(OpShiftR ty) = generateBinOp grin "_prim_int_shr"
generatePrimOp grin@(OpAnd ty) = generateBinOp grin "_prim_int_and"
generatePrimOp grin@(OpOr ty) = generateBinOp grin "_prim_int_or"
generatePrimOp grin@(OpXOr ty) = generateBinOp grin "_prim_int_xor"
generatePrimOp grin@(OpLT ty) = generateCmpOp grin "_prim_int_lt"
generatePrimOp grin@(OpLTE ty) = generateCmpOp grin "_prim_int_lte"
generatePrimOp grin@(OpEQ ty) = generateCmpOp grin "_prim_int_eq"
generatePrimOp grin@(OpGTE ty) = generateCmpOp grin "_prim_int_gte"
generatePrimOp grin@(OpGT ty) = generateCmpOp grin "_prim_int_gt"

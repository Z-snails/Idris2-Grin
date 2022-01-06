module Idris2.EvalPrimOp (
    evalPrimOp
) where

import Control.Exception
import Data.Map
import GHC.Int
import Grin.Grin
import Reducer.Base
import Reducer.Pure
import Data.Word

evalPrimOp :: EvalPlugin
evalPrimOp = EvalPlugin $ fromList
    [ ("_prim_add_Int", intBinOp "_prim_add_Int" int64 (+))
    , ("_prim_sub_Int", intBinOp "_prim_sub_Int" int64 (-))
    , ("_prim_mul_Int", intBinOp "_prim_mul_Int" int64 (*))
    , ("_prim_div_Int", intBinOp "_prim_div_Int" int64 div)

    , ("_prim_add_Bits64", word64BinOp "_prim_add_Bits64" word64 (+))
    , ("_prim_sub_Bits64", word64BinOp "_prim_sub_Bits64" word64 (-))
    , ("_prim_mul_Bits64", word64BinOp "_prim_mul_Bits64" word64 (*))
    , ("_prim_div_Bits64", word64BinOp "_prim_div_Bits64" word64 div)

    , ("_prim_lt_Int" , intCmpOp "_prim_lt_Int"  int64 (<))
    , ("_prim_lte_Int", intCmpOp "_prim_lte_Int" int64 (<=))
    , ("_prim_eq_Int" , intCmpOp "_prim_eq_Int"  int64 (==))
    , ("_prim_gte_Int", intCmpOp "_prim_gte_Int" int64 (>=))
    , ("_prim_gt_Int" , intCmpOp "_prim_gt_Int"  int64 (>))

    , ("_prim_lt_Bits64" , word64CmpOp "_prim_lt_Bits64"  word64 (<))
    , ("_prim_lte_Bits64", word64CmpOp "_prim_lte_Bits64" word64 (<=))
    , ("_prim_eq_Bits64" , word64CmpOp "_prim_eq_Bits64"  word64 (==))
    , ("_prim_gte_Bits64", word64CmpOp "_prim_gte_Bits64" word64 (>=))
    , ("_prim_gt_Bits64" , word64CmpOp "_prim_gt_Bits64"  word64 (>))
    ]
  where
    int64 :: Int64 -> RTVal
    int64 = RT_Lit . LInt64

    word64 :: Word64 -> RTVal
    word64 = RT_Lit . LWord64

    intBinOp :: Name -> (Int64 -> r) -> (Int64 -> Int64 -> Int64) -> [RTVal] -> IO r
    intBinOp fn f op args = case args of
        [RT_Lit (LInt64 x), RT_Lit (LInt64 y)] -> pure $ f (op x y)
        _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args

    word64BinOp :: Name -> (Word64 -> r) -> (Word64 -> Word64 -> Word64) -> [RTVal] -> IO r
    word64BinOp fn f op args = case args of
        [RT_Lit (LWord64 x), RT_Lit (LWord64 y)] -> pure $ f (op x y)
        _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args

    intCmpOp :: Name -> (Int64 -> r) -> (Int64 -> Int64 -> Bool) -> [RTVal] -> IO r
    intCmpOp fn f op = intBinOp fn f (\x y -> boolToNum $ op x y)

    word64CmpOp :: Name -> (Word64 -> r) -> (Word64 -> Word64 -> Bool) -> [RTVal] -> IO r
    word64CmpOp fn f op = word64BinOp fn f (\x y -> boolToNum $ op x y)

    boolToNum :: Num a => Bool -> a
    boolToNum False = 0
    boolToNum _ = 1

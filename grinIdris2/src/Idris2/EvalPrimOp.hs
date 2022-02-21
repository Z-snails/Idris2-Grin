module Idris2.EvalPrimOp
  ( evalPrimOp,
  )
where

import Control.Exception
import Data.Bits
import Data.Map
import Data.Word
import GHC.Int
import Grin.Grin
import Reducer.Base
import Reducer.Pure

evalPrimOp :: EvalPlugin
evalPrimOp =
  EvalPlugin $
    fromList
      [ ("_prim_int_add", intBinOp "_prim_add_Int" int64 (+)),
        ("_prim_int_sub", intBinOp "_prim_sub_Int" int64 (-)),
        ("_prim_int_mul", intBinOp "_prim_mul_Int" int64 (*)),
        ("_prim_int_div", intBinOp "_prim_div_Int" int64 div),
        ("_prim_int_and", intBinOp "_prim_div_Int" int64 (.&.)),
        ("_prim_int_or", intBinOp "_prim_div_Int" int64 (.|.)),
        ("_prim_int_xor", intBinOp "_prim_div_Int" int64 xor),

        ("_prim_word_add", wordBinOp "_prim_add_Bits64" word64 (+)),
        ("_prim_word_sub", wordBinOp "_prim_sub_Bits64" word64 (-)),
        ("_prim_word_mul", wordBinOp "_prim_mul_Bits64" word64 (*)),
        ("_prim_word_div", wordBinOp "_prim_div_Bits64" word64 div),
        ("_prim_word_and", wordBinOp "_prim_div_Bits64" word64 (.&.)),
        ("_prim_word_or", wordBinOp "_prim_div_Bits64" word64 (.|.)),
        ("_prim_word_xor", wordBinOp "_prim_div_Bits64" word64 xor),

        ("_prim_int_lt", intCmpOp "_prim_int_lt" (<)),
        ("_prim_int_lte", intCmpOp "_prim_int_lte" (<=)),
        ("_prim_int_eq", intCmpOp "_prim_int_eq" (==)),
        ("_prim_int_gte", intCmpOp "_prim_int_gte" (>=)),
        ("_prim_int_gt", intCmpOp "_prim_int_gt" (>)),

        ("_prim_word_lt", wordCmpOp "_prim_word_lt" (<)),
        ("_prim_word_lte", wordCmpOp "_prim_word_lte" (<=)),
        ("_prim_word_eq", wordCmpOp "_prim_word_eq" (==)),
        ("_prim_word_gte", wordCmpOp "_prim_word_gte" (>=)),
        ("_prim_word_gt", wordCmpOp "_prim_word_gt" (>))
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

    wordBinOp :: Name -> (Word64 -> r) -> (Word64 -> Word64 -> Word64) -> [RTVal] -> IO r
    wordBinOp fn f op args = case args of
      [RT_Lit (LWord64 x), RT_Lit (LWord64 y)] -> pure $ f (op x y)
      _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args

    intCmpOp :: Name -> (Int64 -> Int64 -> Bool) -> [RTVal] -> IO RTVal
    intCmpOp fn op args = case args of
      [RT_Lit (LInt64 x), RT_Lit (LInt64 y)] -> pure $ RT_Lit $ LBool $ op x y
      _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args

    wordCmpOp :: Name -> (Word64 -> Word64 -> Bool) -> [RTVal] -> IO RTVal
    wordCmpOp fn op args = case args of
      [RT_Lit (LWord64 x), RT_Lit (LWord64 y)] -> pure $ RT_Lit $ LBool $ op x y
      _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args

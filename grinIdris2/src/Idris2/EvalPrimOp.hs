module Idris2.EvalPrimOp (
    evalPrimOp
) where

import Control.Exception
import Data.Map
import GHC.Int
import Grin.Grin
import Reducer.Base
import Reducer.Pure

evalPrimOp :: EvalPlugin
evalPrimOp = EvalPlugin $ fromList
    [ ("_prim_add_Int", intBinOp "_prim_add_Int" int64 (+))
    , ("_prim_sub_Int", intBinOp "_prim_sub_Int" int64 (-))
    , ("_prim_mul_Int", intBinOp "_prim_mul_Int" int64 (*))
    , ("_prim_div_Int", intBinOp "_prim_div_Int" int64 div)
    , ("_prim_lt_Int" , intCmpOp "_prim_lt_Int"  int64 (<))
    , ("_prim_lte_Int", intCmpOp "_prim_lte_Int" int64 (<=))
    , ("_prim_eq_Int" , intCmpOp "_prim_eq_Int"  int64 (==))
    , ("_prim_gte_Int", intCmpOp "_prim_gte_Int" int64 (>=))
    , ("_prim_gt_Int" , intCmpOp "_prim_gt_Int"  int64 (>))
    ]
  where
    int64 :: Int64 -> RTVal
    int64 = RT_Lit . LInt64
    intBinOp :: Name -> (Int64 -> r) -> (Int64 -> Int64 -> Int64) -> [RTVal] -> IO r
    intBinOp fn f op args = case args of
        [RT_Lit (LInt64 a), RT_Lit (LInt64 b)] -> pure $ f (a `op` b)
        _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show args
    intCmpOp :: Name -> (Int64 -> r) -> (Int64 -> Int64 -> Bool) -> [RTVal] -> IO r
    intCmpOp fn f op args = intBinOp fn f (\x y ->boolToInt64 $ op x y) args
    boolToInt64 :: Bool -> Int64
    boolToInt64 False = 0
    boolToInt64 _ = 1

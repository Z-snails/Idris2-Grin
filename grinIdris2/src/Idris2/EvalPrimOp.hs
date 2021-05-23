module Idris2.EvalPrimOp (

) where

import Control.Exception
import GHC.Int
import Grin.Grin
import Reducer.Base

evalPrimOp :: Name -> [Val] -> [RTVal] -> IO RTVal
evalPrimOp fn params args = case fn of
    "_prim_add_Int" -> intBinOp int64 (+)
    _ -> throwIO $ userError $ "unknown primitive operation: " ++ show fn 

  where
    int64 :: Int64 -> RTVal
    int64 = RT_Lit . LInt64
    intBinOp :: (Int64 -> r) -> (Int64 -> Int64 -> Int64) -> IO r
    intBinOp f op = case args of
        [RT_Lit (LInt64 a), RT_Lit (LInt64 b)] -> pure $ f (a `op` b)
        _ -> throwIO $ userError $ "invalid arguments for " ++ show fn ++ ": " ++ show params

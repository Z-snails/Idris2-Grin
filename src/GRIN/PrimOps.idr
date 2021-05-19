module GRIN.PrimOps

import Data.Vect

import Core.Core
import Core.TT

import GRIN.AST
import GRIN.Data

bindArgs :
    Ref NextVar Var =>
    Vect arity (Tag GName) ->
    List Var ->
    (List Var -> Core (Exp GName)) ->
    Core (Exp GName)
bindArgs (tag :: tags) (arg :: args) k = do
    v <- newVar
    rest <- bindArgs tags args (k . (v ::))
    pure $ Bind (ConstTagNode tag [SVar v]) (App (GrinName Eval) [arg]) rest
bindArgs _ _ k = k []

export
primOp :
    Ref NextVar Var =>
    {arity : Nat} ->
    Vect arity (Tag GName) ->
    (primOp : PrimFn arity) ->
    Tag GName ->
    Core (Def GName)
primOp aTags op retTag = do
    args <- replicate arity newVar
    ret <- newVar
    pure $ mkDef (PrimName op) args
         !(bindArgs aTags args
         $ \as => pure $ Bind (VVar ret) (App (PrimFunc op) as)
         $ SimpleExp $ Pure $ ConstTagNode retTag [SVar ret])

mkConstTag : Constant -> Tag GName
mkConstTag c = MkTag Con (ConstName c)

intTag : Tag GName
intTag = mkConstTag $ I 0
int8Tag : Tag GName
int8Tag = mkConstTag $ I8 0
int16Tag : Tag GName
int16Tag = mkConstTag $ I16 0
int32Tag : Tag GName
int32Tag = mkConstTag $ I32 0
int64Tag : Tag GName
int64Tag = mkConstTag $ I64 0
bits8Tag : Tag GName
bits8Tag = mkConstTag $ B8 0
bits16Tag : Tag GName
bits16Tag = mkConstTag $ B16 0
bits32Tag : Tag GName
bits32Tag = mkConstTag $ B32 0
bits64Tag : Tag GName
bits64Tag = mkConstTag $ B64 0
integerTag : Tag GName
integerTag = mkConstTag $ BI 0

intTags : List (Constant, Tag GName)
intTags =
    [ (IntType, intTag)
    , (Int8Type, int8Tag), (Int16Type, int16Tag), (Int32Type, int32Tag), (Int64Type, int64Tag)
    , (Bits8Type, bits8Tag), (Bits16Type, bits16Tag), (Bits32Type, bits32Tag), (Bits64Type, bits64Tag)
    , (IntegerType, integerTag)
    ]

export
primOps : Ref NextVar Var => Core (List (Def GName))
primOps = concat <$> traverse mkBinOps intTags
  where
    mkBinOps : (Constant, Tag GName) -> Core (List (Def GName))
    mkBinOps (ty, tag) = traverse (\fn => primOp [tag, tag] fn tag) [Add ty, Sub ty, Mul ty]

export
externs : List (Extern GName)
externs = []

export
primCons :
    Ref NextVar Var =>
    (ptr : Var) -> Core (List (Alt GName))
primCons _ = traverse mkPrimAlt cons
  where
    cons : List Constant
    cons =
        [I 0, I8 0, I16 0, I32 0,
         I64 0, BI 0, B8 0, B16 0,
         B32 0, B64 0, Str "", Ch '\0',
         Db 0.0, WorldVal, IntType, Int8Type,
         Int16Type, Int32Type, Int64Type, IntegerType,
         Bits8Type, Bits16Type, Bits32Type, Bits64Type,
         StringType, CharType, DoubleType, WorldType]
    mkPrimAlt : Constant -> Core (Alt GName)
    mkPrimAlt c = do
        v <- newVar
        pure $ MkAlt (getConstantNodePat v c) $ SimpleExp $ Pure $ wrapConstant v c

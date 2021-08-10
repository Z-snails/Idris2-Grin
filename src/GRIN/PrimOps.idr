module GRIN.PrimOps

import Data.Vect

import Core.CompileExpr
import Core.Core
import Core.TT

import GRIN.AST
import GRIN.Data

%default total

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

stringTag : Tag GName
stringTag = mkConstTag $ Str ""
charTag : Tag GName
charTag = mkConstTag $ Ch '\0'
doubleTag : Tag GName
doubleTag = mkConstTag $ Db 0.0

intTags : List (Constant, Tag GName)
intTags =
    [ (IntType, intTag)
    , (Int8Type, int8Tag), (Int16Type, int16Tag), (Int32Type, int32Tag), (Int64Type, int64Tag)
    , (Bits8Type, bits8Tag), (Bits16Type, bits16Tag), (Bits32Type, bits32Tag), (Bits64Type, bits64Tag)
    , (IntegerType, integerTag)
    ]

concatTraverse : (a -> Core (List b)) -> List a -> Core (List b)
concatTraverse f = map concat . traverse f

concatCore : List (Core (List a)) -> Core (List a)
concatCore [] = pure []
concatCore (xs :: xss) = [| xs ++ concatCore xss |]

export
primOps : Ref NextVar Var => Core (List (Def GName))
primOps = concatCore
    [ concatTraverse mkBinOps intTags
    , concatTraverse mkCmpOps intTags
    ]
  where
    mkBinOps : (Constant, Tag GName) -> Core (List (Def GName))
    mkBinOps (ty, tag) = traverse (\fn => primOp [tag, tag] fn tag) [Add ty, Sub ty, Mul ty, Div ty]

    mkCmpOps : (Constant, Tag GName) -> Core (List (Def GName))
    mkCmpOps (ty, tag) = traverse (\fn => primOp [tag, tag] fn intTag) [LT ty, LTE ty, EQ ty, GTE ty, GT ty]

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

getCFTypeCon : CFType -> Maybe (Maybe (Tag GName))
getCFTypeCon = \case
    CFUnit => Just Nothing
    CFInt => just2 intTag
    CFInteger => just2 integerTag
    CFInt8 => just2 int8Tag
    CFInt16 => just2 int16Tag
    CFInt32 => just2 int32Tag
    CFInt64 => just2 int64Tag
    CFUnsigned8 => just2 bits8Tag
    CFUnsigned16 => just2 bits16Tag
    CFUnsigned32 => just2 bits32Tag
    CFUnsigned64 => just2 bits64Tag
    CFString => just2 stringTag
    CFDouble => just2 doubleTag
    CFChar => just2 charTag
    CFPtr => just2 $ MkTag Con $ GrinName PtrVar
    CFGCPtr => just2 $ MkTag Con $ GrinName PtrVar
    CFBuffer => just2 $ MkTag Con $ GrinName PtrVar
    CFForeignObj => just2 $ MkTag Con $ GrinName PtrVar
    CFWorld => just2 $ MkTag Con $ GrinName PtrVar
    CFFun _ _ => Nothing
    CFIORes ty => assert_total $ getCFTypeCon ty
    CFStruct _ _ => Nothing
    CFUser _ _ => Nothing
  where
    just2 : a -> Maybe (Maybe a)
    just2 = Just . Just

getCFTypeCons : List CFType -> Maybe (arity ** Vect arity (Tag GName))
getCFTypeCons [] = Just (_ ** [])
getCFTypeCons (CFWorld :: args) = getCFTypeCons args
getCFTypeCons (arg :: args) = case getCFTypeCon arg of
    Nothing => Nothing
    Just Nothing => Nothing -- CFUnit can't be an argument
    Just (Just tag) => case getCFTypeCons args of
        Nothing => Nothing
        Just (_ ** tags) => Just (_ ** tag :: tags)

export
mkFFIWrapper :
    Ref NextVar Var =>
    List CFType ->
    CFType ->
    GName -> -- primitive function
    List Var ->
    Core (Exp GName)
mkFFIWrapper args ret op vs = do
    let Just (ar ** argCons) = getCFTypeCons args
        | Nothing => throw $ InternalError "Unsupported type in ffi."
    let Just retCon = getCFTypeCon ret
        | Nothing => throw $ InternalError "Unsupported type in ffi."
    ret <- newVar
    bindArgs argCons vs $ \vs' =>
        case retCon of
            Nothing => pure $ SimpleExp $ App op vs'
            Just retCon' =>
                pure $ Bind (VVar ret) (App op vs')
                     $ SimpleExp $ Pure $ ConstTagNode retCon' [SVar ret]

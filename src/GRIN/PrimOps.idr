module GRIN.PrimOps

import Data.Vect

import Core.CompileExpr
import Core.Core
import Core.Name
import Core.TT

import GRIN.AST
import GRIN.Data

%default total

bindArgs :
    Ref NextVar Var =>
    List (Tag GName) ->
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
         !(bindArgs (toList aTags) args
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

ioResTag : Tag GName
ioResTag = MkTag Con $ IdrName $ NS primIONS $ UN "MkIORes"

intTags : List (Constant, Tag GName)
intTags =
    [ (IntType, intTag)
    , (Int8Type, int8Tag), (Int16Type, int16Tag), (Int32Type, int32Tag), (Int64Type, int64Tag)
    , (Bits8Type, bits8Tag), (Bits16Type, bits16Tag), (Bits32Type, bits32Tag), (Bits64Type, bits64Tag)
    , (IntegerType, integerTag)
    ]

cmpTags : List (Constant, Tag GName)
cmpTags = [(StringType, stringTag), (CharType, charTag), (DoubleType, doubleTag)] ++ intTags

concatTraverse : (a -> Core (List b)) -> List a -> Core (List b)
concatTraverse f = map concat . traverse f

concatCore : List (Core (List a)) -> Core (List a)
concatCore [] = pure []
concatCore (xs :: xss) = [| xs ++ concatCore xss |]

export
primOps : Ref NextVar Var => Core (List (Def GName))
primOps = concatCore
    [ concatTraverse mkBinOps intTags
    , concatTraverse mkCmpOps cmpTags
    , stringOps
    , miscOps
    ]
  where
    mkBinOps : (Constant, Tag GName) -> Core (List (Def GName))
    mkBinOps (ty, tag) = traverse (\fn => primOp [tag, tag] fn tag) [Add ty, Sub ty, Mul ty, Div ty]

    mkCmpOps : (Constant, Tag GName) -> Core (List (Def GName))
    mkCmpOps (ty, tag) = traverse (\fn => primOp [tag, tag] fn intTag) [LT ty, LTE ty, EQ ty, GTE ty, GT ty]

    stringOps : Core (List (Def GName))
    stringOps = sequence
        [ primOp [stringTag] StrLength intTag
        , primOp [stringTag] StrHead charTag
        , primOp [stringTag] StrTail stringTag
        , primOp [stringTag, intTag] StrIndex charTag
        , primOp [charTag, stringTag] StrCons stringTag
        , primOp [stringTag, stringTag] StrAppend stringTag
        , primOp [stringTag] StrReverse stringTag
        , primOp [intTag, intTag, stringTag] StrSubstr stringTag
        ]

    miscOps : Core (List (Def GName))
    miscOps = sequence
        [ do
            ty1 <- newVar
            ty2 <- newVar
            arg <- newVar
            pure $ mkDef (PrimName BelieveMe) [ty1, ty2, arg] $ SimpleExp $ App (PrimFunc BelieveMe) [ty1, ty2, arg]
        ]

export
externs : List (Extern GName)
externs = []

export
primCons :
    Ref NextVar Var =>
    (ptr : Var) -> Core (List (Alt GName))
primCons _ = [| miscPrimAlts ++ traverse mkPrimAlt cons |]
  where
    cons : List Constant
    cons =
        [I 0, I8 0, I16 0, I32 0,
         I64 0, BI 0, B8 0, B16 0,
         B32 0, B64 0, Str "", Ch '\0',
         Db 0.0, WorldVal]
    mkPrimAlt : Constant -> Core (Alt GName)
    mkPrimAlt c = do
        v <- newVar
        pure $ MkAlt (getConstantNodePat v c) $ SimpleExp $ Pure $ wrapConstant v c
    miscPrimAlts : Core (List (Alt GName))
    miscPrimAlts = pure
        [ MkAlt (NodePat nullTag []) $ SimpleExp $ Pure $ ConstTagNode nullTag []
        ]

getCFTypeCon : CFType -> Tag GName
getCFTypeCon CFUnit = intTag
getCFTypeCon CFInt = intTag
getCFTypeCon CFInteger = integerTag
getCFTypeCon CFInt8 = int8Tag
getCFTypeCon CFInt16 = int16Tag
getCFTypeCon CFInt32 = int32Tag
getCFTypeCon CFInt64 = int64Tag
getCFTypeCon CFUnsigned8 = bits8Tag
getCFTypeCon CFUnsigned16 = bits16Tag
getCFTypeCon CFUnsigned32 = bits32Tag
getCFTypeCon CFUnsigned64 = bits64Tag
getCFTypeCon CFString = stringTag
getCFTypeCon CFDouble = doubleTag
getCFTypeCon CFChar = charTag
getCFTypeCon CFPtr = MkTag Con $ GrinName PtrVar
getCFTypeCon CFGCPtr = MkTag Con $ GrinName PtrVar
getCFTypeCon CFBuffer = MkTag Con $ GrinName PtrVar
getCFTypeCon CFForeignObj = MkTag Con $ GrinName PtrVar
getCFTypeCon CFWorld = MkTag Con $ GrinName PtrVar
getCFTypeCon (CFFun _ _) = MkTag Con $ GrinName PtrVar
getCFTypeCon (CFIORes ty) = assert_total $ getCFTypeCon ty
getCFTypeCon (CFStruct _ _) = MkTag Con $ GrinName PtrVar
getCFTypeCon (CFUser _ _) = MkTag Con $ GrinName PtrVar

%inline
getCFTypeCons : List CFType -> List (Tag GName)
getCFTypeCons = map getCFTypeCon

bindArgsWithWorld :
    Ref NextVar Var =>
    List CFType ->
    List Var ->
    (List Var -> Var -> Core (Exp GName)) ->
    Core (Exp GName)
bindArgsWithWorld tys args f = doBind tys args Nothing $ handleNoWorld f
  where
    doBind :
        List CFType ->
        List Var ->
        Maybe Var ->
        (List Var -> Maybe Var -> Core (Exp GName)) ->
        Core (Exp GName)
    doBind [] [] world k = k [] world
    doBind (CFWorld :: tys) (arg :: args) _ k = doBind tys args (Just arg) k
    doBind (ty :: tys) (arg :: args) world k = do
        v <- newVar
        rest <- doBind tys args world (k . (v ::))
        pure $ Bind (ConstTagNode (getCFTypeCon ty) [SVar v]) (App (GrinName Eval) [arg])
             rest
    doBind _ _ _ _ = throw $ InternalError "Mismatch between number of arguments and number of types"

    handleNoWorld :
        (List Var ->       Var -> Core (Exp GName)) ->
        (List Var -> Maybe Var -> Core (Exp GName))
    handleNoWorld f vs Nothing = throw $ InternalError "Unable to find World in ffi call"
    handleNoWorld f vs (Just world) = f vs world

export
mkFFIWrapper :
    Ref NextVar Var =>
    GName ->
    List CFType ->
    CFType ->
    GName -> -- primitive function
    Core (Def GName)
mkFFIWrapper fn args ret@(CFIORes innerRet) op = do
    vs <- traverse (\_ => newVar) args
    exp <- bindArgsWithWorld args vs $ \vs', world => do
        res <- newVar
        let res' = if isUnit innerRet then SLit (LInt 0) else SVar res
        pure $ Bind (VVar res) (App op vs')
             $ SimpleExp $ Pure $ ConstTagNode (getCFTypeCon ret) [res']
    pure $ mkDef fn vs exp
  where
    isUnit : CFType -> Bool
    isUnit CFUnit = True
    isUnit _ = False

mkFFIWrapper fn args ret op = do
    vs <- traverse (\_ => newVar) args
    let argCons = getCFTypeCons args
    exp <- bindArgs argCons vs $ \vs' => do
        res <- newVar
        pure $ Bind (VVar res) (App op vs')
             $ SimpleExp $ Pure $ ConstTagNode (getCFTypeCon ret) [SVar res]
    pure $ mkDef fn vs exp

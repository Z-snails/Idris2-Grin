module GRIN.Data

import Data.Vect
import Data.SortedSet
import Libraries.Data.IntMap

import Compiler.Common
import Core.CompileExpr
import Core.Core
import Core.TT

import GRIN.AST

%default total

export
replicate : Nat -> Core a -> Core (List a)
replicate 0 _ = pure []
replicate (S k) act = [| act :: replicate k act |]

-- missing instances
namespace Instances
    export
    constantTag : Constant -> Int
    constantTag (I _) = 0
    constantTag (I8 _) = 1
    constantTag (I16 _) = 2
    constantTag (I32 _) = 3
    constantTag (I64 _) = 4
    constantTag (BI _) = 5
    constantTag (B8 _) = 6
    constantTag (B16 _) = 7
    constantTag (B32 _) = 8
    constantTag (B64 _) = 9
    constantTag (Str _) = 10
    constantTag (Ch _) = 11
    constantTag (Db _) = 12
    constantTag WorldVal = 13
    constantTag IntType = 14
    constantTag Int8Type = 15
    constantTag Int16Type = 16
    constantTag Int32Type = 17
    constantTag Int64Type = 18
    constantTag IntegerType = 19
    constantTag Bits8Type = 20
    constantTag Bits16Type = 21
    constantTag Bits32Type = 22
    constantTag Bits64Type = 23
    constantTag StringType = 24
    constantTag CharType = 25
    constantTag DoubleType = 26
    constantTag WorldType = 27

    export
    Ord Constant where
        I x `compare` I y = compare x y
        I8 x `compare` I8 y = compare x y
        I16 x `compare` I16 y = compare x y
        I32 x `compare` I32 y = compare x y
        I64 x `compare` I64 y = compare x y
        BI x `compare` BI y = compare x y
        B8 x `compare` B8 y = compare x y
        B16 x `compare` B16 y = compare x y
        B32 x `compare` B32 y = compare x y
        B64 x `compare` B64 y = compare x y
        Str x `compare` Str y = compare x y
        Ch x `compare` Ch y = compare x y
        Db x `compare` Db y = compare x y
        compare x y = compare (constantTag x) (constantTag y)

    export
    cmpPrimFn : PrimFn n -> PrimFn m -> Ordering
    cmpPrimFn (Add x) (Add y) = compare x y
    cmpPrimFn (Sub x) (Sub y) = compare x y
    cmpPrimFn (Mul x) (Mul y) = compare x y
    cmpPrimFn (Div x) (Div y) = compare x y
    cmpPrimFn (Mod x) (Mod y) = compare x y
    cmpPrimFn (Neg x) (Neg y) = compare x y
    cmpPrimFn (ShiftL x) (ShiftL y) = compare x y
    cmpPrimFn (ShiftR x) (ShiftR y) = compare x y
    cmpPrimFn (BAnd x) (BAnd y) = compare x y
    cmpPrimFn (BOr x) (BOr y) = compare x y
    cmpPrimFn (BXOr x) (BXOr y) = compare x y
    cmpPrimFn (LT x) (LT y) = compare x y
    cmpPrimFn (LTE x) (LTE y) = compare x y
    cmpPrimFn (EQ x) (EQ y) = compare x y
    cmpPrimFn (GTE x) (GTE y) = compare x y
    cmpPrimFn (GT x) (GT y) = compare x y
    cmpPrimFn (Cast f1 t1) (Cast f2 t2) = compare f1 f2 <+> compare t1 t2
    cmpPrimFn fn1 fn2 = tag fn1 `compare` tag fn2
      where
        tag : forall arity. PrimFn arity -> Int
        tag (Add _) = 0
        tag (Sub _) = 1
        tag (Mul _) = 2
        tag (Div _) = 3
        tag (Mod _) = 4
        tag (Neg _) = 5
        tag (ShiftL _) = 6
        tag (ShiftR _) = 7
        tag (BAnd _) = 8
        tag (BOr _) = 9
        tag (BXOr _) = 10
        tag (LT _) = 11
        tag (LTE _) = 12
        tag (EQ _) = 13
        tag (GTE _) = 14
        tag (GT _) = 15
        tag StrLength = 16
        tag StrHead = 17
        tag StrTail = 18
        tag StrIndex = 19
        tag StrCons = 20
        tag StrAppend = 21
        tag StrReverse = 22
        tag StrSubstr = 23
        tag DoubleExp = 24
        tag DoubleLog = 25
        tag DoublePow = 26
        tag DoubleSin = 27
        tag DoubleCos = 28
        tag DoubleTan = 29
        tag DoubleASin = 30
        tag DoubleACos = 31
        tag DoubleATan = 32
        tag DoubleSqrt = 33
        tag DoubleFloor = 34
        tag DoubleCeiling = 35
        tag (Cast _ _) = 36
        tag BelieveMe = 37
        tag Crash = 38

public export
data GrinFn
    = Apply
    | ApplyU
    | ApplyNU
    | Crash
    | Eval
    | IntegerVar
    | Main
    | Null
    | PtrVar

export
Show GrinFn where
    show Apply = "apply"
    show ApplyU = "applyU"
    show ApplyNU = "applyNU"
    show Crash = "_prim_crash"
    show Eval = "eval"
    show IntegerVar = "Integer"
    show Main = "grinMain"
    show Null = "Null"
    show PtrVar = "Ptr"

%inline
grinFnTag : GrinFn -> Int
grinFnTag Apply = 0
grinFnTag ApplyU = 1
grinFnTag ApplyNU = 2
grinFnTag Crash = 3
grinFnTag Eval = 4
grinFnTag IntegerVar = 5
grinFnTag Main = 6
grinFnTag Null = 7
grinFnTag PtrVar = 8

export
Eq GrinFn where
    f == g = grinFnTag f == grinFnTag g

export
Ord GrinFn where
    f `compare` g = grinFnTag f `compare` grinFnTag g

public export
data GName : Type where
    IdrName : Name -> GName
    FFIName : String -> GName
    GrinName : GrinFn -> GName
    PrimName : PrimFn arity -> GName
    PrimFunc : PrimFn arity -> GName
    ConstName : Constant -> GName

quote : String -> String
quote s = "\"" ++ s ++ "\""

export
Show GName where
    show (IdrName n) = quote $ showFull n
      where
        showFull : Name -> String
        showFull (NS ns n) = fastConcat [showNSWithSep "." ns, ".", showFull n]
        showFull (UN str) = str
        showFull (MN str i) = fastConcat ["{", str, ":", show i, "}"]
        showFull (PV n d) = fastConcat ["{P:", showFull n, ":", show d]
        showFull (DN _ n) = showFull n
        showFull (RF s) = fastConcat ["rf_", s]
        showFull (Nested (x, y) n) = fastConcat [show x, ":", show y, ":", showFull n]
        showFull (CaseBlock str i) = fastConcat ["cb_", str, show i]
        showFull (WithBlock str i) = fastConcat ["wb_", str, show i]
        showFull (Resolved i) = "$" ++ show i
    show (FFIName fn) = fn
    show (GrinName fn) = show fn
    show (PrimName op) = quote $ show op
    show (PrimFunc op) = "_prim_" ++ showPrimFn op
      where
        showPrimFn : forall ar. PrimFn ar -> String
        showPrimFn = \case
            Add ty => "add_" ++ show ty
            Sub ty => "sub_" ++ show ty
            Mul ty => "mul_" ++ show ty
            Div ty => "div_" ++ show ty
            Mod ty => "mod_" ++ show ty
            Neg ty => "neg_" ++ show ty
            ShiftL ty => "shl_" ++ show ty
            ShiftR ty => "shr_" ++ show ty
            BAnd ty => "and_" ++ show ty
            BOr ty => "or_" ++ show ty
            BXOr ty => "xor_" ++ show ty
            LT ty => "lt_" ++ show ty
            LTE ty => "lte_" ++ show ty
            EQ ty => "eq_" ++ show ty
            GTE ty => "gte_" ++ show ty
            GT ty => "gt_" ++ show ty
            StrLength => "str_length"
            StrHead => "str_head"
            StrTail => "str_tail"
            StrIndex => "str_index"
            StrCons => "str_cons"
            StrAppend => "str_append"
            StrReverse => "str_reverse"
            StrSubstr => "str_substr"
            DoubleExp => "double_exp"
            DoubleLog => "double_log"
            DoublePow => "double_pow"
            DoubleSin => "double_sin"
            DoubleCos => "double_cos"
            DoubleTan => "double_tan"
            DoubleASin => "double_asin"
            DoubleACos => "double_acos"
            DoubleATan => "double_atan"
            DoubleSqrt => "double_sqrt"
            DoubleFloor => "double_floor"
            DoubleCeiling => "double_ceiling"
            Cast from to => fastConcat ["cast_", show from, "_", show to]
            BelieveMe => "believe_me"
            Crash => "crash"
    show (ConstName c) = showConstName c
      where
        showConstName : Constant -> String
        showConstName = \case
            I _ => "Int"
            I8 _ => "Int8"
            I16 _ => "Int16"
            I32 _ => "Int32"
            I64 _ => "Int64"
            BI _ => "Integer"
            B8 _ => "Bits8"
            B16 _ => "Bits16"
            B32 _ => "Bits32"
            B64 _ => "Bits64"
            Str _ => "String"
            Ch _ => "Char"
            Db _ => "Double"
            WorldVal => "MkWorld"
            IntType => "IntType"
            Int8Type => "Int8Type"
            Int16Type => "Int16Type"
            Int32Type => "Int32Type"
            Int64Type => "Int64Type"
            IntegerType => "IntegerType"
            Bits8Type => "Bits8Type"
            Bits16Type => "Bits16Type"
            Bits32Type => "Bits32Type"
            Bits64Type => "Bits64Type"
            StringType => "StringType"
            CharType => "CharType"
            DoubleType => "DoubleType"
            WorldType => "WorldType"

export
Eq GName where
    IdrName n == IdrName m = n == m
    FFIName n == FFIName m = n == m
    GrinName n == GrinName m = n == m
    PrimName o == PrimName p = cmpPrimFn o p == EQ
    PrimFunc o == PrimFunc p = cmpPrimFn o p == EQ
    ConstName c == ConstName d = constantTag c == constantTag d
    _ == _ = False

export
Ord GName where
    IdrName n `compare` IdrName m = n `compare` m
    FFIName n `compare` FFIName m = n `compare` m
    GrinName n `compare` GrinName m = n `compare` m
    PrimName n `compare` PrimName m = n `cmpPrimFn` m
    PrimFunc n `compare` PrimFunc m = n `cmpPrimFn` m
    ConstName c `compare` ConstName d = constantTag c `compare` constantTag d
    n `compare` m = tag n `compare` tag m
      where
        tag : GName -> Int
        tag (IdrName _) = 0
        tag (FFIName _) = 1
        tag (GrinName _) = 2
        tag (PrimName _) = 3
        tag (PrimFunc _) = 4
        tag (ConstName _) = 5

public export data AVars : Type where
public export data Ptrs : Type where
public export data NextVar : Type where
public export data Build : Type where

public export
0 AVarMap : Type
AVarMap = IntMap Var

public export
0 PtrSet : Type
PtrSet = SortedSet Var

export
nullTag : Tag GName
nullTag = MkTag Con (GrinName Null)

export
nullVal : Val GName
nullVal = ConstTagNode nullTag []

export
newVar : Ref NextVar Var => Core Var
newVar = do
    v <- get NextVar
    put NextVar (incVar v)
    pure v

constant :
    (onInteger : Constant -> Integer -> r) ->
    (onInt : Constant -> Int -> r) ->
    (onString : Constant -> String -> r) ->
    (onChar : Constant -> Char -> r) ->
    (onDouble : Constant -> Double -> r) ->
    (onNone : Constant -> r) ->
    Constant -> r
constant onBI onI onStr onCh onD onC c = case c of
    I x   => onI c x
    I8 x  => onBI c x
    I16 x => onBI c x
    I32 x => onBI c x
    I64 x => onBI c x
    BI x  => onBI c x
    B8 x  => onI c x
    B16 x => onI c x
    B32 x => onI c x
    B64 x => onBI c x
    Str x => onStr c x
    Ch x  => onCh c x
    Db x  => onD c x
    _     => onC c

export
getConstantLitPat : Constant -> CasePat GName
getConstantLitPat = constant
    (\_ => LitPat . LInt)
    (\_ => LitPat . LInt . cast)
    (\_ => LitPat . LString)
    (\_ => LitPat . LChar)
    (\_ => LitPat . LDouble)
    (\c => NodePat (MkTag Con (ConstName c)) [])

export
getConstantNodePat : Var -> Constant -> CasePat GName
getConstantNodePat v = constant
    (\c, _ => NodePat (MkTag Con (ConstName c)) [v])
    (\c, _ => NodePat (MkTag Con (ConstName c)) [v])
    (\c, _ => NodePat (MkTag Con (ConstName c)) [v])
    (\c, _ => NodePat (MkTag Con (ConstName c)) [v])
    (\c, _ => NodePat (MkTag Con (ConstName c)) [v])
    (\c => NodePat (MkTag Con (ConstName c)) [])

export
anfConstant : Constant -> Val GName
anfConstant = constant
    (\c, x => ConstTagNode (MkTag Con (ConstName (removeVal c))) [SLit $ LInt x])
    (\c, x => ConstTagNode (MkTag Con (ConstName (removeVal c))) [SLit $ LInt $ cast x])
    (\c, x => ConstTagNode (MkTag Con (ConstName (removeVal c))) [SLit $ LString x])
    (\c, x => ConstTagNode (MkTag Con (ConstName (removeVal c))) [SLit $ LChar x])
    (\c, x => ConstTagNode (MkTag Con (ConstName (removeVal c))) [SLit $ LDouble x])
    (\c => ConstTagNode (MkTag Con (ConstName c)) [])
  where
    removeVal : Constant -> Constant
    removeVal (I x) = I 0
    removeVal (I8 x) = I8 0
    removeVal (I16 x) = I16 0
    removeVal (I32 x) = I32 0
    removeVal (I64 x) = I64 0
    removeVal (BI x) = BI 0
    removeVal (B8 x) = B8 0
    removeVal (B16 x) = B16 0
    removeVal (B32 x) = B32 0
    removeVal (B64 x) = B64 0
    removeVal (Str x) = Str ""
    removeVal (Ch x) = Ch '\0'
    removeVal (Db x) = Db 0
    removeVal x = x


export
unwrapConstant : Var -> Constant -> Val GName
unwrapConstant v = constant
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c => VVar v)

export
wrapConstant : Var -> Constant -> Val GName
wrapConstant v = constant
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c, _ => ConstTagNode (MkTag Con (ConstName c)) [SVar v])
    (\c => ConstTagNode (MkTag Con (ConstName c)) [])

export
getCFType : CFType -> Maybe (GType GName)
getCFType = \case
    CFUnit => Just $ SimpleType UnitTy
    CFInt => Just $ SimpleType $ IntTy $ Signed 64
    CFInteger => Just $  TyVar $ GrinName IntegerVar
    CFInt8 => Just $ SimpleType $ IntTy $ Signed 8
    CFInt16 => Just $ SimpleType $ IntTy $ Signed 16
    CFInt32 => Just $ SimpleType $ IntTy $ Signed 32
    CFInt64 => Just $ SimpleType $ IntTy $ Signed 64
    CFUnsigned8 => Just $ SimpleType $ IntTy $ Unsigned 8
    CFUnsigned16 => Just $ SimpleType $ IntTy $ Unsigned 16
    CFUnsigned32 => Just $ SimpleType $ IntTy $ Unsigned 32
    CFUnsigned64 => Just $ SimpleType $ IntTy $ Unsigned 64
    CFString => Just $ SimpleType StringTy
    CFDouble => Just $ SimpleType DoubleTy
    CFChar => Just $ SimpleType CharTy
    CFPtr => Just $ TyVar $ GrinName PtrVar
    CFGCPtr => Just $ TyVar $ GrinName PtrVar
    CFBuffer => Just $ TyVar $ GrinName PtrVar
    CFForeignObj => Just $ TyVar $ GrinName PtrVar
    CFWorld => Just $ TyVar $ GrinName PtrVar
    CFFun _ _ => Nothing
    CFIORes ty => assert_total $ getCFType ty
    CFStruct _ _ => Nothing
    CFUser _ _ => Nothing

export
getFFIType : List CFType -> CFType -> Either String (FuncType GName)
getFFIType args ret = do
    argsTy <- getCFTypes args
    pure (MkFuncType argsTy !(getCFTypeEither ret))
  where
    getCFTypeEither : CFType -> Either String (GType GName)
    getCFTypeEither ty = case getCFType ty of
        Just ty' => Right ty'
        Nothing => Left $ assert_total $ show ty

    getCFTypes : List CFType -> Either String (List (GType GName))
    getCFTypes [] = Right []
    getCFTypes (CFWorld :: tys) = getCFTypes tys
    getCFTypes (ty :: tys) = do
        ty' <- getCFTypeEither ty
        (ty' ::) <$> getCFTypes tys

export
isEff : CFType -> Effectful
isEff (CFIORes _) = Effect
isEff _ = NoEffect

export
getCC : List String -> Maybe String
getCC ccs = case parseCC ["C"] ccs of
    Just (_, (fn :: _)) => Just fn
    _ => Nothing

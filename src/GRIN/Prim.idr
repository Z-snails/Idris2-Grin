module GRIN.Prim

import Data.Vect
import Data.List

import Core.TT
import Core.Core
import Compiler.ANF

import GRIN.Syntax

getPrimTypeName : Constant -> String
getPrimTypeName = \case
    IntType => "Int"
    IntegerType => "Integer"
    Bits8Type => "Bits8"
    Bits16Type => "Bits16"
    Bits32Type => "Bits32"
    Bits64Type => "Bits64"
    StringType => "String"
    CharType => "Char"
    DoubleType => "Double"
    WorldType => "World"
    _ => "Unexpected Value instead of type"

||| Get the grin name of a prim function.
-- Note: These look very like the not quite so prim
-- versions of these functions generated by idris
-- but they have no 'n' at the start
{- example definition of a primitive function
prim__add_Int x y =
    (CInt x') <- eval x
    (CInt y') <- eval y
    z <- _prim_int_add x' y'
    pure (CInt z)
-}
export
getPrimFnName : PrimFn arity -> String
getPrimFnName = \case
    Add ty => "prim__add_" ++ getPrimTypeName ty
    Sub ty => "prim__sub_" ++ getPrimTypeName ty
    Mul ty => "prim__mul_" ++ getPrimTypeName ty
    Div ty => "prim__div_" ++ getPrimTypeName ty
    Mod ty => "prim__mod_" ++ getPrimTypeName ty
    Neg ty => "prim__neg_" ++ getPrimTypeName ty
    ShiftL ty => "prim__shl" ++ getPrimTypeName ty
    ShiftR ty => "prim__shr" ++ getPrimTypeName ty

    BAnd ty => "prim__and_" ++ getPrimTypeName ty
    BOr ty => "prim__or_" ++ getPrimTypeName ty
    BXOr ty => "prim__xor_" ++ getPrimTypeName ty

    LT ty => "prim__lt_" ++ getPrimTypeName ty
    LTE ty => "prim__lte_" ++ getPrimTypeName ty
    EQ ty => "prim__eq_" ++ getPrimTypeName ty
    GT ty => "prim__gt_" ++ getPrimTypeName ty
    GTE ty => "prim__gte_" ++ getPrimTypeName ty

    StrLength => "prim__strLength"
    StrHead => "prim__strHead"
    StrTail => "prim__strTail"
    StrIndex => "prim__strIndex"
    StrCons => "prim__strCons"
    StrAppend => "prim__strAppend"
    StrReverse => "prim__strReverse"
    StrSubstr => "prim__strSubstr"

    DoubleExp => "prim__exp_Double"
    DoubleLog => "prim__log_Double"
    DoubleSin => "prim__sin_Double"
    DoubleCos => "prim__cos_Double"
    DoubleTan => "prim__tan_Double"
    DoubleASin => "prim__asin_Double"
    DoubleACos => "prim__acos_Double"
    DoubleATan => "prim__atan_Double"
    DoubleSqrt => "prim__sqrt_Double"
    DoubleFloor => "prim__floor_Double"
    DoubleCeiling => "prim__ceil_Double"

    Cast from to => "prim__cast_" ++ getPrimTypeName from ++ "_" ++ getPrimTypeName to
    BelieveMe => "prim__believe_me"
    Crash => "prim__crash"

||| Make a primitive Tag.
primTag : String -> Tag
primTag = MkTag Con . Right

||| Make a unary primitive Tag.
export
primTagNode : String -> GrinLit -> Val
primTagNode n val = VTagNode (primTag n) [SLit val]

||| Make a primitive Tag as a value.
primTagVal : String -> Val
primTagVal = VTag . primTag

||| Convert constant to a GRIN value.
export
getConstVal : Constant -> Val -- all these look very similar, generalise into one?
getConstVal = \case
    I i => primTagNode "Int" $ LInt i
    BI i => primTagNode "Integer" $ LInt $ cast i
    B8 i => primTagNode "Bits8" $ LBits64 $ cast i
    B16 i => primTagNode "Bits16" $ LBits64 $ cast i
    B32 i => primTagNode "Bits32" $ LBits64 $ cast i
    B64 i => primTagNode "Bits64" $ LBits64 $ cast i
    Str s => primTagNode "String" $ LString s
    Ch c => primTagNode "Char" $ LChar c
    Db d => primTagNode "Double" $ LDouble d
    WorldVal => primTagVal "World"
    IntType => primTagVal "IntType"
    IntegerType => primTagVal "IntegerType"
    Bits8Type => primTagVal "Bits8Type"
    Bits16Type => primTagVal "Bits16Type"
    Bits32Type => primTagVal "Bits32Type"
    Bits64Type => primTagVal "Bits64Type"
    StringType => primTagVal "StringType"
    CharType => primTagVal "CharType"
    DoubleType => primTagVal "DoubleType"
    WorldType => primTagVal "WorldType"

||| Get a case pattern for a primtive constant
export
getConstPat : Constant -> CasePat
getConstPat = \case
    I i => LitPat $ LInt i
    BI i => LitPat $ LInt $ cast i
    B8 i => LitPat $ LBits64 $ cast i
    B16 i => LitPat $ LBits64 $ cast i
    B32 i => LitPat $ LBits64 $ cast i
    B64 i => LitPat $ LBits64 $ cast i
    Str s => LitPat $ LString s
    Ch c => LitPat $ LChar c
    Db d => LitPat $ LDouble d
    WorldVal => TagPat $ primTag "World"
    IntType => TagPat $ primTag "IntType"
    IntegerType => TagPat $ primTag "IntegerType"
    Bits8Type => TagPat $ primTag "Bits8Type"
    Bits16Type => TagPat $ primTag "Bits16Type"
    Bits32Type => TagPat $ primTag "Bits32Type"
    Bits64Type => TagPat $ primTag "Bits64Type"
    StringType => TagPat $ primTag "StringType"
    CharType => TagPat $ primTag "CharType"
    DoubleType => TagPat $ primTag "DoubleType"
    WorldType => TagPat $ primTag "WorldType"

||| Unwrap a primitve value.
export
unwrapPrim : AConstAlt -> GrinVar -> Val
unwrapPrim (MkAConstAlt c _) v = case c of
    I _ => VTagNode (primTag "Int") [SVar v]
    BI _ => VTagNode (primTag "Integer") [SVar v]
    B8 _ => VTagNode (primTag "Bits8") [SVar v]
    B16 _ => VTagNode (primTag "Bits16") [SVar v]
    B32 _ => VTagNode (primTag "Bits32") [SVar v]
    B64 _ => VTagNode (primTag "Bits64") [SVar v]
    Str _ => VTagNode (primTag "String") [SVar v]
    Ch _ => VTagNode (primTag "Char") [SVar v]
    Db _ => VTagNode (primTag "Double") [SVar v]
    WorldVal => VVar v
    IntType => VVar v
    IntegerType => VVar v
    Bits8Type => VVar v
    Bits16Type => VVar v
    Bits32Type => VVar v
    Bits64Type => VVar v
    StringType => VVar v
    CharType => VVar v
    DoubleType => VVar v
    WorldType => VVar v

mkPrimFn :
    (fn : String) ->
    (binds : List String) ->
    (prim : String) ->
    (ret : String) ->
    GrinDef
mkPrimFn fn [] prim ret =
    MkDef
        (Grin fn)
        []
        $ Bind (VVar $ Var 0) (App (Grin prim) [])
        $ Simple $ Pure (VTagNode (MkTag Con $ Right ret) [SVar $ Var 0])
mkPrimFn fn binds prim ret =
    let ca = cast $ length binds
        args = Var <$> [0 .. ca - 1]
        bounds = Var <$> [ca .. ca * 2 - 1]
        bindings =
            zipWith
                (\bi, bo => VTagNode (MkTag Con $ Right bi) [SVar bo])
                binds
                bounds
    in MkDef
        (Grin fn)
        args
        $ bindArgs args bindings
        $ Bind (VVar $ Var $ ca * 2) (App (Grin prim) $ bounds)
        $ Simple $ Pure $ VTagNode (MkTag Con $ Right ret) [SVar $ Var $ ca * 2] 
  where
    bindArgs : List GrinVar -> List Val -> GrinExp -> GrinExp
    bindArgs [] _ k = k
    bindArgs _ [] k = k
    bindArgs (arg :: rArgs) (bind :: rBinds) k =
        Bind bind (App (Grin "eval") [arg])
        $ bindArgs rArgs rBinds k

unaryFromTo :
    ( String
    , String
    , String
    , String
    ) ->
    GrinDef
unaryFromTo (fn, from, prim, to) = mkPrimFn fn [from] prim to

unary :
    ( String
    , String
    , String
    ) ->
    GrinDef
unary (fn, bind, prim) = mkPrimFn fn [bind] prim bind

binary :
    ( String
    , String
    , String
    ) ->
    GrinDef
binary (fn, bind, prim) = mkPrimFn fn [bind, bind] prim bind

||| Primitive functions.
-- Todo: complete
export
prims : List GrinDef
prims =
    (unary <$>
        [ ("prim__strTail", "String", "_prim_string_tail")
        ]
    ) ++
    (unaryFromTo <$>
        [ ("prim__strLength", "String", "_prim_string_len", "Int")
        ]
    ) ++
    (binary <$>
        [ ("prim__add_Int", "Int", "_prim_int_add")
        ]
    )
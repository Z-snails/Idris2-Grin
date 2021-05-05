module Grin.Syntax

import Core.Name

||| Grin variable.
{-
TODO: Make this into two types
- Function name
- Arguments
-}
public export
data GrinVar : Type where
    ||| Local variable.
    Var : Int -> GrinVar
    ||| Known variable (e.g. functions or constructors).
    Fixed : Name -> GrinVar
    ||| Grin function.
    Grin : String -> GrinVar
    -- Note: never start a `Grin` var with v
    -- as this can clash with `Fixed` `GrinVar`s

export
Eq GrinVar where
    Var i == Var j = i == j
    Fixed n == Fixed m = n == m
    Grin n == Grin m = n == m
    _ == _ = False

export
Ord GrinVar where
    compare (Var i) (Var j) = compare i j
    compare (Var _) _ = LT
    compare _ (Var _) = GT
    compare (Fixed n) (Fixed m) = compare n m
    compare (Fixed _) _ = LT
    compare _ (Fixed _) = GT
    compare (Grin n) (Grin m) = compare n m

||| Type of a tag (constructor).
public export
data TagType : Type where
    ||| Normal constructor.
    Con : TagType
    ||| Lazy thunk.
    Thunk : TagType
    ||| Inf thunk.
    InfThunk : TagType
    ||| Partially applied function.
    Missing : (missing : Nat) -> TagType

tagTypeToNat : TagType -> Nat
tagTypeToNat Con = 0
tagTypeToNat Thunk = 1
tagTypeToNat InfThunk = 2
tagTypeToNat (Missing m) = 3 + m

export
Eq TagType where
    (==) = (==) `on` tagTypeToNat

export
Ord TagType where
    compare = compare `on` tagTypeToNat

||| Constructor.
public export
record Tag where
    constructor MkTag
    ||| Type of tag.
    tagType : TagType
    ||| name
    tagName : GrinVar

export
Eq Tag where
    t1 == t2 = t1.tagType == t2.tagType && t1.tagName == t2.tagName

thenCmp : Ordering -> Lazy Ordering -> Ordering
thenCmp LT _ = LT
thenCmp EQ y = y
thenCmp GT _ = GT

export
Ord Tag where
    t1 `compare` t2 = (t1.tagType `compare` t2.tagType) `thenCmp` (t1.tagName `compare` t2.tagName)

||| Literal in GRIN.
||| Note there is no Bool literal because Idris removes it
public export
data GrinLit : Type where
    LBool : Bool -> GrinLit
    LInt : Int -> GrinLit
    LInteger : Integer -> GrinLit
    LBits64 : Bits64 -> GrinLit
    LDouble : Double -> GrinLit
    LChar : Char -> GrinLit
    LString : String -> GrinLit

export
Eq GrinLit where
    LInt i1 == LInt i2 = i1 == i2
    LInteger i1 == LInteger i2 = i1 == i2
    LBits64 b1 == LBits64 b2 = b1 == b2
    LDouble d1 == LDouble d2 = d1 == d2
    LChar c1 == LChar c2 = c1 == c2
    LString s1 == LString s2 = s1 == s2
    _ == _ = False

||| Builtin GRIN type.
-- Hopefully native Bits<n> types will be added to GRIN
public export
data SimpleType : Type where
    BoolTy : SimpleType
    Int64Ty : SimpleType
    Bits64Ty : SimpleType
    DoubleTy : SimpleType
    UnitTy : SimpleType
    PtrTy : SimpleType
    CharTy : SimpleType
    StringTy : SimpleType

export
simpleTypeIntTag : SimpleType -> Int
simpleTypeIntTag = \case
    BoolTy => 0
    Int64Ty => 1
    Bits64Ty => 2
    DoubleTy => 3
    UnitTy => 4
    PtrTy => 5
    CharTy => 6
    StringTy => 7

export
Eq SimpleType where
    x == y = simpleTypeIntTag x == simpleTypeIntTag y

||| GRIN type.
public export
data GrinType : Type where
    TyCon : GrinVar -> List GrinType -> GrinType
    TySimple : SimpleType -> GrinType

export
Eq GrinType where
    TyCon t1 as1 == TyCon t2 as2 = t1 == t2 && as1 == as2
    TySimple t1 == TySimple t2 = t1 == t2
    _ == _ = False

||| A simple GRIN value.
public export
data SimpleVal : Type where
    ||| Grin literal.
    SLit : GrinLit -> SimpleVal
    ||| Variable.
    SVar : GrinVar -> SimpleVal
    ||| Undefined value.
    SUndefined : GrinType -> SimpleVal

export
Eq SimpleVal where
    SLit l1 == SLit l2 = l1 == l2
    SVar v1 == SVar v2 = v1 == v2
    SUndefined t1 == SUndefined t2 = t1 == t2
    _ == _ = False

||| A GRIN value.
public export
data Val : Type where
    ||| A constructor applied to arguments.
    VTagNode : Tag -> List SimpleVal -> Val
    ||| A constructor with no arguments.
    VTag : Tag -> Val
    ||| A simple value.
    VSimpleVal : SimpleVal -> Val
    ||| Unit.
    VUnit : Val

export
Eq Val where
    VTagNode t1 as1 == VTagNode t2 as2 = t1 == t2 && as1 == as2
    VTag t1 == VTag t2 = t1 == t2
    VSimpleVal v1 == VSimpleVal v2 = v1 == v2
    VUnit == VUnit = True
    _ == _ = False

||| Grin literal.
public export
VLit : GrinLit -> Val 
VLit = VSimpleVal . SLit

||| Variable.
public export
VVar : GrinVar -> Val
VVar = VSimpleVal . SVar

||| Signals result of rhs is discarded
public export
VUndefined : GrinType -> Val
VUndefined = VSimpleVal . SUndefined

||| Pattern in a case statement.
public export
data CasePat : Type where
    NodePat : Tag -> List GrinVar -> CasePat
    TagPat : Tag -> CasePat
    LitPat : GrinLit -> CasePat
    Default : CasePat

public export
FalsePat : CasePat
FalsePat = LitPat (LBool False)

public export
TruePat : CasePat
TruePat = LitPat (LBool True)

||| Get the tag from a case pattern
export
getCaseTag : CasePat -> Maybe Tag
getCaseTag (NodePat tag _) = Just tag
getCaseTag (TagPat tag) = Just tag
getCaseTag _ = Nothing

mutual
    ||| Simple GRIN expression.
    public export
    data SimpleExp : Type where
        ||| Makes pretty printing easier.
        Do : GrinExp -> SimpleExp
        ||| Apply a known function.
        App : GrinVar -> List GrinVar -> SimpleExp
        ||| Pure value.
        Pure : Val -> SimpleExp
        ||| Store a value in memory
        Store : Val -> SimpleExp
        ||| Fetch a value from memory
        Fetch : GrinVar -> SimpleExp
        ||| Update a value in memory
        Update : GrinVar -> Val -> SimpleExp

    ||| GRIN expression.
    public export
    data GrinExp : Type where
        ||| Bind an expression to a value.
        Bind : Val -> SimpleExp -> GrinExp -> GrinExp
        ||| Case statement.
        Case : Val -> List GrinAlt -> GrinExp
        ||| A Simple Expression.
        Simple : SimpleExp -> GrinExp
    
    ||| Alternative in a case statement.
    public export
    data GrinAlt : Type where
        MkAlt : CasePat -> GrinExp -> GrinAlt

export
mapSimpleExp : (GrinExp -> GrinExp) -> SimpleExp -> SimpleExp
mapSimpleExp f (Do exp) = Do (f exp)
mapSimpleExp _ exp = exp

export
mapAltExp : (GrinExp -> GrinExp) -> GrinAlt -> GrinAlt
mapAltExp f (MkAlt pat exp) = MkAlt pat (f exp)

||| Top level GRIN definition.
public export
data GrinDef : Type where
    MkDef :
        (name : GrinVar) -> -- should only be Fixed or Grin
        (args : List GrinVar) ->
        GrinExp ->
        GrinDef

export
mapGrinDef : (GrinExp -> GrinExp) -> GrinDef -> GrinDef
mapGrinDef f (MkDef n as exp) = MkDef n as (f exp)

||| Information about an external function.
public export
record External where
    constructor MkExt
    ||| Name of the external function.
    name : String
    ||| Return type of the function
    retTy : GrinType
    ||| Argument types
    argTy : List GrinType
    ||| Effectful?
    effect : Bool
    ||| Is it built in to GRIN
    builtin : Bool

||| Split a list of external functions into each type.type
||| (builtin pure, builtin effectful, ffi pure, ffi effectful)
export
splitExterns : List External -> (List External, List External, List External, List External)
splitExterns [] = ([], [], [], [])
splitExterns (x :: xs) =
    let (primPure, primEff, ffiPure, ffiEff) = splitExterns xs
    in case (x.builtin, x.effect) of
        (True, False) => (x :: primPure, primEff, ffiPure, ffiEff)
        (True, True) => (primPure, x :: primEff, ffiPure, ffiEff)
        (False, False) => (primPure, primEff, x :: ffiPure, ffiEff)
        (False, True) => (primPure, primEff, ffiPure, x :: ffiEff)

||| Entire GRIN program.
public export
data GrinProg : Type where
    MkProg :
        List External ->
        List GrinDef ->
        GrinProg

export
mapGrinProg : (GrinExp -> GrinExp) -> GrinProg -> GrinProg
mapGrinProg f (MkProg exts defs) = MkProg exts (mapGrinDef f <$> defs)

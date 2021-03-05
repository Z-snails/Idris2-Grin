module GRIN.Syntax

import Core.Name

||| Grin variable.
public export
data GrinVar : Type where
    ||| ANF index.
    -- used to make generating new names easier.
    Anf : Int -> GrinVar
    ||| Local variable.
    Var : Int -> GrinVar
    ||| Known variable (e.g. functions or constructors).
    Fixed : Name -> GrinVar
    ||| Grin function.
    Grin : String -> GrinVar

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

||| Constructor.
public export
record Tag where
    constructor MkTag
    ||| Type of tag.
    tagType : TagType
    ||| name
    tagName : Name

||| Literal in GRIN.
||| Note there is no Bool literal because Idris removes it
public export
data GrinLit : Type where
    LInt : Int -> GrinLit
    LBits64 : Bits64 -> GrinLit
    LDouble : Double -> GrinLit
    LChar : Char -> GrinLit
    LString : String -> GrinLit

||| Builtin GRIN type.
-- if GRIN all the way to LLVM is added to this
-- add Bits8, 16 etc.
public export
data SimpleType : Type where
    IntTy : SimpleType
    Bits64Ty : SimpleType
    DoubleTy : SimpleType
    CharTy : SimpleType
    StringTy : SimpleType

||| GRIN type.
public export
data GrinType : Type where
    TyCon : GrinVar -> List GrinType -> GrinType
    TySimple : SimpleType -> GrinType

||| A simple GRIN value.
public export
data SimpleVal : Type where
    ||| Grin literal.
    SLit : GrinLit -> SimpleVal
    ||| Variable.
    SVar : GrinVar -> SimpleVal

||| A GRIN value.
public export
data Val : Type where
    ||| A constructor applied to arguments.
    VTagNode : Tag -> List SimpleVal -> Val
    ||| A constructor with no arguments.
    VTag : Tag -> Val
    ||| A simple value.
    VSimpleVal : SimpleVal -> Val

||| Grin literal.
public export
VLit : GrinLit -> Val 
VLit = VSimpleVal . SLit

||| Variable.
public export
VVar : GrinVar -> Val
VVar = VSimpleVal . SVar

||| Pattern in a case statement.
public export
data CasePat : Type where
    NodePat : Tag -> List Val -> CasePat
    TagPat : Tag -> CasePat
    LitPat : GrinLit -> CasePat
    Default : CasePat

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

||| Top level GRIN definition.
public export
data GrinDef : Type where
    MkDef :
        GrinVar -> -- should only be Fixed or Grin
        (args : List GrinVar) ->
        GrinExp ->
        GrinDef

||| Information about an external function.
public export
record External where
    constructor MkExt
    ||| Name of the external function.
    name : GrinVar
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
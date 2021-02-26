module GRIN.Syntax

||| Primitive names
public export
data PrimName
    = World
    | WorldTy
    | IntTy
    | IntegerTy
    | Bits8Ty
    | Bits16Ty
    | Bits32Ty
    | Bits64Ty
    | CharTy
    | StringTy
    | DoubleTy


||| A GRIN name
public export
data Name
    = ||| User generated name u_<String>
        User String
    | ||| Name index v_<Int>
        Ind Int
    | ||| Generated variable based on existing name
        Gen Name Int
    | ||| Name as displayed in grin output
        Grin String
    | ||| Null (I don't know what it does in ANF)
        Null
    | ||| Primitive type constructors or world
        Prim PrimName

||| Generate a name based on an existing name
export
nextName : Name -> Name
nextName (Gen name i) = Gen name (i + 1)
nextName name = Gen name 0

||| Modify a user name
export
mapUN : (String -> String) -> Name -> Name
mapUN f (User name) = User (f name)
mapUN _ name = name

||| Simple/Builtin Type
public export
data SimpleTy
    = TInt
    | TWord
    | TFloat
    | TBool
    | TUnit
    | TChar
    | TString
    | TDead

||| Type
public export
data Ty
    = TyCon Name (List Ty)
    | TyVar Name
    | TySimple SimpleTy

||| Info about an external function
public export
record External where
    constructor MkExternal
    ||| Name of external function
    name : Name
    ||| Return type of the function
    retTy : Ty
    ||| Type of arguments to the function
    argTy : List Ty
    ||| Is function builtin
    builtin : Bool
    ||| Is function effectful
    effect : Bool

||| Type of a Tag
public export
data TagType
    = ||| Actual constructor
        C
    | ||| Unevaluated thunk
        F
    | ||| Unevaluated infinite thunk
        FInf
    | ||| Partially applied function with missing paramter count
        P Nat

||| Full Tag
public export
record Tag where
    constructor MkTag
    ||| What sort of tag
    type : TagType
    ||| Name of tag
    name : Name

||| Literal
public export
data Lit : Type where
    LInt : Int -> Lit
    LWord : Bits64 -> Lit
    LFloat : Double -> Lit
    LBool : Bool -> Lit
    LChar : Char -> Lit
    LString : String -> Lit


||| Type of a value
public export
data ValType
    = AnyVal
    | SimpleVal

||| Value
public export
data Val : Type where
    ConstTagNode : Tag -> List Val -> Val
    VarTagNode : Name -> List Val -> Val
    ValTag : Tag -> Val
    VUnit : Val

    VLit : Lit -> Val
    Var : Name -> Val
    Undefined : Ty -> Val

||| Pattern in case
public export
data CPat
    = NodePat Tag (List Name)
    | TagPat Tag
    | LitPat Lit
    | DefaultPat

||| Expression, Program or Definition
public export
data Expr : Type where
    Prog : List External -> List Expr -> Expr 

    Def : Name -> List Name -> Expr -> Expr

    Bind : Val -> Expr -> Expr -> Expr
    Discard : Expr -> Expr -> Expr
    Case : Val -> List Expr -> Expr

    App : Name -> List Val -> Expr
    Pure : Val -> Expr
    Store : Val -> Expr
    Fetch : Name -> Expr
    Update : Name -> Val -> Expr

    Alt : CPat -> Expr -> Expr

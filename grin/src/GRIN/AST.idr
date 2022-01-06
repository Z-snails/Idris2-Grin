module GRIN.AST

import Data.SortedMap

||| A bound variable or function argument.
public export
data Var : Type where
    MkVar : Int -> Var

export
incVar : Var -> Var
incVar (MkVar x) = MkVar (x + 1)

export
Eq Var where
    MkVar x == MkVar y = x == y

export
Ord Var where
    MkVar x `compare` MkVar y = x `compare` y

||| A type of a tag.
public export
data TagType : Type where
    ||| Data constructor.
    Con : TagType
    ||| Updating thunk.
    UThunk : TagType
    ||| Non-updating thunk.
    NUThunk : TagType
    ||| Partially applied function.
    Partial : Nat -> TagType

tagTypeToNat : TagType -> Nat
tagTypeToNat Con = 0
tagTypeToNat UThunk = 1
tagTypeToNat NUThunk = 2
tagTypeToNat (Partial k) = k + 3

export
Eq TagType where
    (==) = (==) `on` tagTypeToNat

export
Ord TagType where
    compare = compare `on` tagTypeToNat

||| A constructor tag.
public export
record Tag name where
    constructor MkTag
    tagType : TagType
    tag : name

export
Eq name => Eq (Tag name) where
    MkTag ty1 tag1 == MkTag ty2 tag2 = ty1 == ty2 && tag1 == tag2

export
Ord name => Ord (Tag name) where
    MkTag ty1 tag1 `compare` MkTag ty2 tag2 = case compare ty1 ty2 of
        EQ => compare tag1 tag2
        o => o

export
Functor Tag where
    map f (MkTag ty tag) = MkTag ty (f tag)

export
Foldable Tag where
    foldl f z (MkTag ty tag) = f z tag
    foldr f z (MkTag ty tag) = f tag z

export
Traversable Tag where
    traverse f (MkTag ty tag) = MkTag ty <$> f tag

||| A literal value.
public export
data Lit : Type where
    LInt : Integer -> Lit
    LDouble : Double -> Lit
    LString : String -> Lit
    LChar : Char -> Lit

export
Eq Lit where
    LInt x == LInt y = x == y
    LDouble x == LDouble y = x == y
    LString x == LString y = x == y
    LChar x == LChar y = x == y
    _ == _ = False

||| The precision and signed-ness of an integer.
public export
data IntPrec : Type where
    Signed : Nat -> IntPrec
    Unsigned : Nat -> IntPrec

export
Eq IntPrec where
    Signed x == Signed y = x == y
    Unsigned x == Unsigned y = x == y
    _ == _ = False

||| Id of the store instuction a `HeapPtr` came from
public export
StoreId : Type
StoreId = Int

||| A simple type.
public export
data SType : Type where
    IntTy : IntPrec -> SType
    DoubleTy : SType
    CharTy : SType
    StringTy : SType
    UnitTy : SType
    HeapPtr : StoreId -> SType

export
Eq SType where
    IntTy x == IntTy y = x == y
    DoubleTy == DoubleTy = True
    CharTy == CharTy = True
    StringTy == StringTy = True
    UnitTy == UnitTy = True
    HeapPtr x == HeapPtr y = x == y
    _ == _ = False

||| A type of a value.
public export
data GType : (name : Type) -> Type where
    SimpleType : SType -> GType name
    TyVar : name -> GType name
    Cons : GType name -- TODO: HPT

Eq name => Eq (GType name) where
    SimpleType ty1 == SimpleType ty2 = ty1 == ty2
    Cons == Cons = True
    _ == _ = False

export
Functor GType where
    map _ (SimpleType ty) = SimpleType ty
    map f (TyVar x) = TyVar (f x)
    map _ Cons = Cons

export
Foldable GType where
    foldl f z Cons = z
    foldl f z (TyVar x) = f z x
    foldl _ z _ = z

    foldr f z Cons = z
    foldr f z (TyVar x) = f x z
    foldr _ z _ = z

export
Traversable GType where
    traverse _ (SimpleType ty) = pure (SimpleType ty)
    traverse f (TyVar x) = TyVar <$> f x
    traverse f Cons = pure Cons

||| A type of a function.
public export
record FuncType name where
    constructor MkFuncType
    args : List (GType name)
    ret : GType name

export
Eq name => Eq (FuncType name) where
    MkFuncType as1 r1 == MkFuncType as2 r2 = as1 == as2 && r1 == r2

export
Functor FuncType where
    map f (MkFuncType args ret) = MkFuncType (map (map f) args) (map f ret)

export
Foldable FuncType where
    foldl f z0 (MkFuncType args ret) =
        let z1 = foldl (foldl f) z0 args
        in foldl f z1 ret
    
    foldr f z0 (MkFuncType args ret) =
        let z1 = foldr f z0 ret
        in foldr (flip $ foldr f) z1 args

export
Traversable FuncType where
    traverse f (MkFuncType args ret) = [| MkFuncType (traverse (traverse f) args) (traverse f ret) |]

||| A simple value.
public export
data SVal : Type where
    SVar : Var -> SVal
    SLit : Lit -> SVal

export
Eq SVal where
    SVar x == SVar y = x == y
    SLit x == SLit y = x == y
    _ == _ = False

||| A value.
public export
data Val : (name : Type) -> Type where
    SimpleVal : SVal -> Val name
    ||| A known constructor applied to any number of arguments.
    ||| ```
    ||| pure (CInt 10)`
    ||| ```
    ConstTagNode : Tag name -> List SVal -> Val name
    ||| A known constructor applied to no arguments.
    ||| ```
    ||| pure CInt
    ||| ```
    ConstTag : Tag name -> Val name
    ||| A variable constructor applied to any number of arguments.
    ||| ```
    ||| con <- pure CInt
    ||| pure (con 10)
    ||| ```
    VarTagNode : Var -> List SVal -> Val name
    ||| Discard.
    VUnit : Val name

export
Eq name => Eq (Val name) where
    SimpleVal x == SimpleVal y = x == y
    ConstTagNode t1 vs1 == ConstTagNode t2 vs2 = vs1 == vs2 && t1 == t2
    ConstTag t1 == ConstTag t2 = t1 == t2
    VarTagNode x vs1 == VarTagNode y vs2 = x == y && vs1 == vs2
    VUnit == VUnit = True
    _ == _ = False

public export
VVar : Var -> Val name
VVar = SimpleVal . SVar

public export
VLit : Lit -> Val name
VLit = SimpleVal . SLit

export
mkCon : name -> List SVal -> Val name
mkCon con = ConstTagNode (MkTag Con con)

export
mkUThunk : name -> List SVal -> Val name
mkUThunk fn = ConstTagNode (MkTag UThunk fn)

export
mkNUThunk : name -> List SVal -> Val name
mkNUThunk fn = ConstTagNode (MkTag NUThunk fn)

export
mkPartial : name -> Nat -> List SVal -> Val name
mkPartial fn m = ConstTagNode (MkTag (Partial m) fn)

export
Functor Val where
    map _ (SimpleVal val) = SimpleVal val
    map f (ConstTagNode tag args) = ConstTagNode (map f tag) args
    map f (ConstTag tag) = ConstTag (map f tag)
    map _ (VarTagNode var args) = VarTagNode var args
    map _ VUnit = VUnit

export
Foldable Val where
    foldl f z (ConstTagNode tag _) = foldl f z tag
    foldl f z (ConstTag tag) = foldl f z tag
    foldl _ z _ = z

    foldr f z = foldl (flip f) z

export
Traversable Val where
    traverse _ (SimpleVal val) = pure $ SimpleVal val
    traverse f (ConstTagNode tag args) = (\tag' => ConstTagNode tag' args) <$> traverse f tag
    traverse f (ConstTag tag) = ConstTag <$> traverse f tag
    traverse _ (VarTagNode var args) = pure $ VarTagNode var args
    traverse _ VUnit = pure VUnit

||| Pattern on the LHS of a case alternative.
public export
data CasePat : (name : Type) -> Type where
    ||| A known constructor applied to any number of arguments.
    ||| ```
    ||| (CInt x) -> ...
    ||| ```
    NodePat : Tag name -> List Var -> CasePat name
    ||| A known constructor.
    ||| ```
    ||| CInt -> ...
    ||| ```
    TagPat : Tag name -> CasePat name
    ||| A literal.
    ||| ```
    ||| 10 -> ...
    ||| ```
    LitPat : Lit -> CasePat name
    ||| Default pattern.
    ||| ```
    ||| #default -> ...
    ||| ```
    DefaultPat : CasePat name

export
getPatTag : CasePat name -> Maybe (Tag name)
getPatTag (NodePat t _) = Just t
getPatTag (TagPat t) = Just t
getPatTag _ = Nothing

export
Eq name => Eq (CasePat name) where
    NodePat t1 as1 == NodePat t2 as2 = as1 == as2 && t1 == t2
    TagPat t1 == TagPat t2 = t1 == t2
    LitPat x == LitPat y = x == y
    DefaultPat == DefaultPat = True
    _ == _ = False

export
Functor CasePat where
    map f (NodePat tag args) = NodePat (map f tag) args
    map f (TagPat tag) = TagPat (map f tag)
    map _ (LitPat lit) = LitPat lit
    map _ DefaultPat = DefaultPat

export
Foldable CasePat where
    foldl f z (NodePat tag _) = foldl f z tag
    foldl f z (TagPat tag) = foldl f z tag
    foldl _ z _ = z

    foldr f = foldl (flip f)

export
Traversable CasePat where
    traverse f (NodePat tag args) = (\tag' => NodePat tag' args) <$> traverse f tag
    traverse f (TagPat tag) = TagPat <$> traverse f tag
    traverse _ (LitPat lit) = pure $ LitPat lit
    traverse _ DefaultPat = pure DefaultPat

mutual
    ||| A simple expression.
    public export
    data SExp : (name : Type) -> Type where
        ||| A full expression. Allows for easier inlining and phi nodes.
        Do : Exp name -> SExp name
        ||| Apply a known function to the correct number of arguments.
        App : name -> List Var -> SExp name
        ||| A value.
        Pure : Val name -> SExp name
        ||| Return a pointer to a value.
        Store : Val name -> SExp name
        ||| Fetch the value at a pointer
        Fetch : Maybe StoreId -> Var -> SExp name
        ||| Fetch a specific component of the value at a pointer.
        FetchI : Maybe StoreId -> Nat -> Var -> SExp name
        ||| Update the value at a pointer to a new value.
        Update : Var -> Val name -> SExp name

    ||| An Expression.
    public export
    data Exp : (name : Type) -> Type where
        ||| A simple value.
        SimpleExp : SExp name -> Exp name
        ||| Bind the result of a simple expression to a variable.
        Bind : Val name -> SExp name -> Exp name -> Exp name
        ||| Split to different code paths depending on provided value.
        Case : Val name -> List (Alt name) -> Exp name

    ||| A case alternative.
    public export
    data Alt : Type -> Type where
        MkAlt : CasePat name -> Exp name -> Alt name

export
altPat : Alt name -> CasePat name
altPat (MkAlt pat _) = pat

export
altExp : Alt name -> Exp name
altExp (MkAlt _ exp) = exp

export
mkDo : Exp name -> SExp name
mkDo (SimpleExp exp) = exp
mkDo exp = Do exp

export
mkSimpleExp : SExp name -> Exp name
mkSimpleExp (Do exp) = exp
mkSimpleExp exp = SimpleExp exp

export
fetch : Var -> SExp name
fetch = Fetch Nothing

export
fetchI : Nat -> Var -> SExp name
fetchI = FetchI Nothing

mutual
    export
    Eq name => Eq (SExp name) where
        Do e1 == Do e2 = assert_total $ e1 == e2
        App f1 as1 == App f2 as2 = as1 == as2 && f1 == f2
        Pure x == Pure y = x == y
        Store x == Store y = x == y
        Fetch i1 v1 == Fetch i2 v2 = i1 == i2 && v1 == v2
        FetchI i1 n1 v1 == FetchI i2 n2 v2 = i1 == i2 && n1 == n2 && v1 == v2
        Update x v1 == Update y v2 = x == y && v1 == v2
        _ == _ = False
    
    export
    Eq name => Eq (Exp name) where
        SimpleExp e1 == SimpleExp e2 = e1 == e2
        Bind v1 rhs1 rest1 == Bind v2 rhs2 rest2 = v1 == v2 && rhs1 == rhs2 && rest1 == rest2
        Case v1 alts1 == Case v2 alts2 = v1 == v2 && assert_total (alts1 == alts2)
        _ == _ = False

    export covering
    Eq name => Eq (Alt name) where
        MkAlt p1 e1 == MkAlt p2 e2 = p1 == p2 && e1 == e2

mutual
    export
    Functor SExp where
        map f (Do exp) = Do $ map f exp
        map f (App fun args) = App (f fun) args
        map f (Pure val) = Pure $ map f val
        map f (Store val) = Store $ map f val
        map _ (Fetch i var) = Fetch i var
        map _ (FetchI i idx var) = FetchI i idx var
        map f (Update var val) = Update var $ map f val
    
    export
    Functor Exp where
        map f (SimpleExp exp) = SimpleExp $ map f exp
        map f (Bind lhs rhs rest) = Bind (map f lhs) (map f rhs) (map f rest)
        map f (Case val alts) = Case (map f val) (map (map f) alts)
    
    export
    Functor Alt where
        map f (MkAlt pat exp) = MkAlt (map f pat) (map f exp)

mutual
    export
    Foldable SExp where
        foldl f z (Do exp) = foldl f z exp
        foldl f z (App fun _) = f z fun
        foldl f z (Pure val) = foldl f z val
        foldl f z (Store val) = foldl f z val
        foldl _ z (Fetch _ _) = z
        foldl _ z (FetchI _ _ _) = z
        foldl f z (Update _ val) = foldl f z val
        
        foldr f z (Do exp) = foldr f z exp
        foldr f z (App fun _) = f fun z
        foldr f z (Pure val) = foldr f z val
        foldr f z (Store val) = foldr f z val
        foldr _ z (Fetch _ _) = z
        foldr _ z (FetchI _ _ _) = z
        foldr f z (Update _ val) = foldr f z val

    export
    Foldable Exp where
        foldl f z (SimpleExp exp) = foldl f z exp
        foldl f z0 (Bind val rhs rest) =
            let z1 = foldl f z0 val
                z2 = foldl f z1 rhs
            in foldl f z2 rest
        foldl f z0 (Case val alts) =
            let z1 = foldl f z0 val
            in foldl (foldl f) z1 alts
        
        foldr f z (SimpleExp exp) = foldr f z exp
        foldr f z0 (Bind val rhs rest) =
            let z1 = foldr f z0 rest
                z2 = foldr f z1 rhs
            in foldr f z2 val
        foldr f z0 (Case val alts) =
            let z1 = foldr (flip $ foldr f) z0 alts
            in foldr f z1 val

    export
    Foldable Alt where
        foldl f z0 (MkAlt pat exp) =
            let z1 = foldl f z0 pat
            in foldl f z1 exp
    
        foldr f z0 (MkAlt pat exp) =
            let z1 = foldr f z0 exp
            in foldr f z1 pat

mutual
    export
    Traversable SExp where
        traverse f (Do exp) = Do <$> traverse f exp
        traverse f (App fun args) = (\fun' => App fun' args) <$> f fun
        traverse f (Pure val) = Pure <$> traverse f val
        traverse f (Store val) = Store <$> traverse f val
        traverse _ (Fetch i var) = pure $ Fetch i var
        traverse _ (FetchI i idx var) = pure $ FetchI i idx var 
        traverse f (Update var val) = Update var <$> traverse f val
    
    export
    Traversable Exp where
        traverse f (SimpleExp exp) = SimpleExp <$> traverse f exp
        traverse f (Bind lhs rhs rest) =
            [| Bind (traverse f lhs) (traverse f rhs) (traverse f rest) |]
        traverse f (Case val alts) =
            [| Case (traverse f val) (traverse (traverse f) alts) |]

    export
    Traversable Alt where
        traverse f (MkAlt pat exp) = [| MkAlt (traverse f pat) (traverse f exp) |]

export
mapExpSExp : (Exp name -> Exp name) -> SExp name -> SExp name
mapExpSExp f (Do exp) = Do (f exp)
mapExpSExp _ exp = exp

export
mapExpAlt : (Exp name -> Exp name) -> Alt name -> Alt name
mapExpAlt f (MkAlt pat exp) = MkAlt pat (f exp)

mutual
    export
    mapSExpExp : (SExp name -> SExp name) -> Exp name -> Exp name
    mapSExpExp f (SimpleExp e) = SimpleExp (f e)
    mapSExpExp f (Bind v rhs rest) = Bind v (f rhs) (mapSExpExp f rest)
    mapSExpExp f (Case v alts) = Case v (mapSExpAlt f <$> alts)

    export
    mapSExpAlt : (SExp name -> SExp name) -> Alt name -> Alt name
    mapSExpAlt f (MkAlt pat exp) = MkAlt pat (mapSExpExp f exp)

public export
record Def name where
    constructor MkDef
    defName : name
    args : List Var
    body : Exp name
    type : Maybe (FuncType name)

export
mkDef : name -> List Var -> Exp name -> Def name
mkDef defName args body = MkDef defName args body Nothing

export
Eq name => Eq (Def name) where
    MkDef n1 as1 e1 t1 == MkDef n2 as2 e2 t2 = n1 == n2 && as1 == as2 && e1 == e2 && t1 == t2

export
Functor Def where
    map f (MkDef n as b ty) = MkDef (f n) as (map f b) (map (map f) ty)

export
Foldable Def where
    foldl f z0 (MkDef n _ b ty) =
        let z1 = f z0 n
            z2 = foldl (foldl f) z1 ty
        in foldl f z2 b
    foldr f z0 (MkDef n _ b ty) =
        let z1 = foldr f z0 b
            z2 = foldr (flip $ foldr f) z1 ty
        in f n z2

export
Traversable Def where
    traverse f (MkDef n as b ty) = [| (\n', b' => MkDef n' as b') (f n) (traverse f b) (traverse (traverse f) ty) |]

export %inline
mapExpDef : (Exp name -> Exp name) -> Def name -> Def name
mapExpDef f (MkDef n as b ty) = MkDef n as (f b) ty

public export
data ExternPrim = Primop | FFI

export
Eq ExternPrim where
    Primop == Primop = True
    FFI == FFI = True
    _ == _ = False

public export
data Effectful = NoEffect | Effect

export
Eq Effectful where
    NoEffect == NoEffect = True
    Effect == Effect = True
    _ == _ = False

public export
data OS = Darwin | FreeBSD | Linux | Android | MinGW | Win | NetBSD | OpenBSD

namespace OS
    osToInt : OS -> Int
    osToInt Darwin = 0
    osToInt FreeBSD = 1
    osToInt Linux = 2
    osToInt Android = 3
    osToInt MinGW = 4
    osToInt Win = 5
    osToInt NetBSD = 6
    osToInt OpenBSD = 7

    export
    Eq OS where
        x == y = osToInt x == osToInt y

    export
    Ord OS where
        compare x y = osToInt x `compare` osToInt y

public export
record Extern name where
    constructor MkExtern
    extName : name
    type : FuncType name
    prim : ExternPrim
    eff : Effectful
    libs : List (OS, String)

export
Eq name => Eq (Extern name) where
    MkExtern n1 t1 p1 e1 ls1 == MkExtern n2 t2 p2 e2 ls2
        = p1 == p2 && e1 == e2 && n1 == n2 && t1 == t2 && ls1 == ls2

export
Functor Extern where
    map f (MkExtern n ty prim eff libs) = MkExtern (f n) (map f ty) prim eff libs

export
Foldable Extern where
    foldl f z (MkExtern n ty _ _ _) = foldl f (f z n) ty
    foldr f z (MkExtern n ty _ _ _) = f n $ foldr f z ty

infixl 2 <&>
(<&>) : Functor f => f (a -> b) -> a -> f b
f <&> x = ($ x) <$> f

export
Traversable Extern where
    traverse f (MkExtern n ty prim eff libs) = [| MkExtern (f n) (traverse f ty) |] <&> prim <&> eff <&> libs

||| An entire program.
public export
record Prog name where
    constructor MkProg
    ||| External functions.
    externs : SortedMap name (Extern name)
    ||| GRIN functions.
    defs : SortedMap name (Def name)
    ||| Main function.
    mainFn : name

export
mkProg : Ord name => List (Extern name) -> List (Def name) -> (main : name) -> Prog name
mkProg exts defs m = MkProg (fromList $ pairExt <$> exts) (fromList $ pairDef <$> defs) m
  where
    pairExt : forall name. Extern name -> (name, Extern name)
    pairExt ext = (ext.extName, ext)
    pairDef : forall name. Def name -> (name, Def name)
    pairDef def = (def.defName, def)

export
Eq name => Eq (Prog name) where
    MkProg exts1 defs1 m1 == MkProg exts2 defs2 m2 = m1 == m2 && exts1 == exts2 && defs1 == defs2

export %inline
mapProg : Ord new => (old -> new) -> Prog old -> Prog new
mapProg f (MkProg exts defs m) =
    let exts' = fromList $ bimap f (map f) <$> toList exts
        defs' = fromList $ bimap f (map f) <$> toList defs
    in MkProg exts' defs' (f m)

export
Foldable Prog where
    foldl f z0 (MkProg exts defs m) =
        let z1 = foldl (foldl f) z0 exts
            z2 = foldl (foldl f) z1 defs
        in f z2 m
    foldr f z0 (MkProg exts defs m) =
        let z1 = f m z0
            z2 = foldr (flip $ foldr f) z0 exts
        in foldr (flip $ foldr f) z1 defs

export
traverseProg : Applicative t => Ord new => (old -> t new) -> Prog old -> t (Prog new)
traverseProg f (MkProg exts defs m) =
    let exts' = fromList <$> traverse (bitraverse f (traverse f)) (toList exts)
        defs' = fromList <$> traverse (bitraverse f (traverse f)) (toList defs)
    in [| MkProg exts' defs' (f m) |]

export %inline
mapExpProg : (Exp name -> Exp name) -> Prog name -> Prog name
mapExpProg f (MkProg exts defs m) = MkProg exts (map (mapExpDef f) defs) m

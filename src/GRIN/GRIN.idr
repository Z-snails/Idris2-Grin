module GRIN.GRIN

import Data.List
import Data.Vect
import Data.String
import Data.SortedSet
import System.File
import System

import Libraries.Utils.Path

import Core.Core
import Core.CompileExpr
import Core.TT
import Core.Name as Core
import Core.Context
import Compiler.ANF
import Compiler.Common

import GRIN.Syntax as GRIN
import GRIN.Pretty

forgetLen : Vect len a -> List a
forgetLen [] = []
forgetLen (x :: xs) = x :: forgetLen xs

||| Pretty print a String
export
grinString : String -> String
grinString = fastAppend . map safeChar . fastUnpack
  where
    safeChar : Char -> String
    safeChar c = if isAlphaNum c
        then cast c
        else case c of
            '_' => "_us"
            '<' => "_lt"
            '>' => "_gt"
            '=' => "_eq"
            '*' => "_st"
            '-' => "-"
            _ => "c" <+> show (cast {to=Int} c)

grinNS : Namespace -> String
grinNS = showNSWithSep "_"

grinName : Core.Name -> GRIN.Name
grinName = User . grinName'
  where
    grinName' : Core.Name -> String
    grinName' (NS ns name) = grinNS ns <+> "_" <+> grinName' name
    grinName' (UN name) = grinString name
    grinName' (MN name i) = grinString name <+> show i
    grinName' (PV name i) = "pv_" <+> (grinName' name) <+> show i
    grinName' (DN _ name) = grinName' name
    grinName' (RF name) = "rf_" <+> grinString name
    grinName' (Nested (i, j) name) = "n_" <+> show i <+> "_" <+> show j <+> "_" <+> grinName' name
    grinName' (CaseBlock name i) = "case_" <+> grinString name <+> "_" <+> show i
    grinName' (WithBlock name i) = "with_" <+> grinString name <+> "_" <+> show i
    grinName' (Resolved i) = "res_" <+> show i

data ApplyFn : Type where
data EvalFn : Type where
data PrimFns : Type where

grinAVar' : AVar -> GRIN.Name
grinAVar' (ALocal i) = Ind i
grinAVar' ANull = Null

grinAVar : AVar -> Val
grinAVar = Var . grinAVar'

grinLitConst : Constant -> Lit
grinLitConst = \case
    I i => LInt i
    BI i => LWord (cast i)
    B8 i => LWord (cast i)
    B16 i => LWord (cast i)
    B32 i => LWord (cast i)
    B64 i => LWord (cast i)
    Ch c => LChar c
    Str str => LString str
    Db d => LFloat d
    c => assert_total $ idris_crash $ "Internal Error: " ++ show c ++ " is not a constant"

grinConst : Constant -> Val
grinConst = \case
    I i => VLit $ LInt i
    BI i => VLit $ LWord (cast i)
    B8 i => VLit $ LWord (cast i)
    B16 i => VLit $ LWord (cast i)
    B32 i => VLit $ LWord (cast i)
    B64 i => VLit $ LWord (cast i)
    Ch c => VLit $ LChar c
    Str str => VLit $ LString str
    Db d => VLit $ LFloat d
    WorldVal => mkPrimVal World
    IntType => mkPrimVal IntTy
    IntegerType => mkPrimVal IntegerTy
    Bits8Type => mkPrimVal Bits8Ty
    Bits16Type => mkPrimVal Bits16Ty
    Bits32Type => mkPrimVal Bits32Ty
    Bits64Type => mkPrimVal Bits64Ty
    CharType => mkPrimVal CharTy
    StringType => mkPrimVal StringTy
    DoubleType => mkPrimVal DoubleTy
    WorldType => mkPrimVal WorldTy
  where
    mkPrimVal : PrimName -> Val
    mkPrimVal = ValTag . MkTag C . Prim

mkCTag : GRIN.Name -> Tag
mkCTag = MkTag C

getConstTag : Constant -> Tag
getConstTag = mkCTag . Grin . \case
    I _ => "Int"
    BI _ => "Integer"
    B8 _ => "Bits8"
    B16 _ => "Bits16"
    B32 _ => "Bits32"
    B64 _ => "Bits64"
    Ch _ => "Char"
    Str _ => "String"
    Db _ => "Double"
    IntType => "Int"
    IntegerType => "Integer"
    Bits8Type => "Bits8"
    Bits16Type => "Bits16"
    Bits32Type => "Bits32"
    Bits64Type => "Bits64"
    CharType => "Char"
    StringType => "String"
    DoubleType => "Double"
    c => assert_total $ idris_crash $ "Internal Error: " ++ show c ++ " is not a literal"

litCon : Constant -> GRIN.Name -> Val
litCon c var = ConstTagNode (getConstTag c) [Var var]

mkFTag : GRIN.Name -> Tag
mkFTag = MkTag F

mkFInfTag : GRIN.Name -> Tag
mkFInfTag = MkTag FInf

mkPTag : GRIN.Name -> (missing : Nat) -> Tag
mkPTag name missing = MkTag (P missing) name

||| Force a value
eval : Val -> Expr
eval var = App (Grin "eval") [var]

||| Strictly apply a closure to one more argument
appS : AVar -> AVar -> Expr
appS fun arg = App (Grin "appS") $ grinAVar <$> [fun, arg]

||| Lazily apply a closure to one more argument
appL : AVar -> AVar -> Expr
appL fun arg = App (Grin "appL") $ grinAVar <$> [fun, arg]

||| Lazily (Inf) apply a closure to one more argument
appInf : AVar -> AVar -> Expr
appInf fun arg = App (Grin "appInf") $ grinAVar <$> [fun, arg]

||| Forget the length of a Vect
forget : Vect _ a -> List a
forget [] = []
forget (x :: xs) = x :: forget xs

showTy : Constant -> String
showTy = \case
    IntType => "Int"
    c => assert_total $ idris_crash $ "Internal Error: " ++ show c ++ " Not a Type"

addPrimFnToPreamble : PrimFn arity -> Core ()
addPrimFnToPreamble _ = pure ()

primFnNameMap : PrimFn arity -> GRIN.Name
primFnNameMap = Grin . \case
    Add ty => "_prim_add_" ++ showTy ty
    _ => "Not yet implemented"

||| Get the argument types and return type of a PrimFn.
getTy : PrimFn arity -> Vect (S arity) Constant
getTy (Add ty) = [ty, ty, ty]
getTy (Sub ty) = [ty, ty, ty]
getTy (Mul ty) = [ty, ty, ty]
getTy (Div ty) = [ty, ty, ty]
getTy (Mod ty) = [ty, ty, ty]
getTy (Neg ty) = [ty, ty]
getTy (ShiftL ty) = [ty, ty, ty]
getTy (ShiftR ty) = [ty, ty, ty]
getTy (BAnd ty) = [ty, ty, ty]
getTy (BOr ty) = [ty, ty, ty]
getTy (BXOr ty) = [ty, ty, ty]
getTy (LT ty) = [ty, ty, IntType]
getTy (LTE ty) = [ty, ty, IntType]
getTy (GT ty) = [ty, ty, IntType]
getTy (GTE ty) = [ty, ty, IntType]
getTy (EQ ty) = [ty, ty, IntType]
getTy StrLength = [StringType, IntType]
getTy StrHead = [StringType, CharType]
getTy StrTail = [StringType, CharType]
getTy StrIndex = [StringType, IntType, CharType]
getTy StrCons = [CharType, StringType, StringType]
getTy StrAppend = [StringType, StringType, StringType]
getTy StrReverse = [StringType, StringType]
getTy StrSubstr = [IntType, IntType, StringType, StringType]
getTy DoubleExp = [DoubleType, DoubleType]
getTy DoubleLog = [DoubleType, DoubleType]
getTy DoubleSin = [DoubleType, DoubleType]
getTy DoubleCos = [DoubleType, DoubleType]
getTy DoubleTan = [DoubleType, DoubleType]
getTy DoubleASin = [DoubleType, DoubleType]
getTy DoubleACos = [DoubleType, DoubleType]
getTy DoubleATan = [DoubleType, DoubleType]
getTy DoubleSqrt = [DoubleType, DoubleType]
getTy DoubleFloor = [DoubleType, DoubleType]
getTy DoubleCeiling = [DoubleType, DoubleType]
getTy (Cast from to) = [from, to]
getTy BelieveMe = assert_total $ idris_crash "Internal Error: BelieveMe not caught by primFnS"
getTy Crash = assert_total $ idris_crash "Internal Error: Crash not caught by primFnS"

primFnS : PrimFn arity -> Vect arity AVar -> Core Expr -- add to apply
primFnS prim [x] = do
    addPrimFnToPreamble prim
    let x' = nextName $ grinAVar' x
    pure $ Bind (litCon (index 0 $ getTy prim) x') (eval $ grinAVar x)
         $ Bind (Var (Grin "ret")) (App (primFnNameMap prim) [Var x'])
         $ Pure $ litCon (index 1 $ getTy prim) (Grin "ret")
primFnS Crash [_, msg] = do
    let msg' = nextName $ grinAVar' msg
    pure $ Bind (litCon StringType msg') (eval $ grinAVar msg)
         $ App (Grin "crash") [Var msg']
primFnS prim [x, y] = do
    addPrimFnToPreamble prim
    let x' = nextName $ grinAVar' x
    let y' = nextName $ grinAVar' y
    pure $ Bind (litCon (index 0 $ getTy prim) x') (eval $ grinAVar x)
         $ Bind (litCon (index 1 $ getTy prim) y') (eval $ grinAVar y)
         $ Bind (Var (Grin "ret")) (App (primFnNameMap prim) [Var x', Var y'])
         $ Pure $ litCon (index 2 $ getTy prim) (Grin "ret")
primFnS BelieveMe [_, _, x] = pure $ Pure $ grinAVar x
primFnS prim [x, y, z] = do
    addPrimFnToPreamble prim
    let x' = nextName $ grinAVar' x
    let y' = nextName $ grinAVar' y
    let z' = nextName $ grinAVar' z
    pure $ Bind (litCon (index 0 $ getTy prim) x') (eval $ grinAVar x)
         $ Bind (litCon (index 1 $ getTy prim) y') (eval $ grinAVar y)
         $ Bind (litCon (index 2 $ getTy prim) z') (eval $ grinAVar z)
         $ Bind (Var (Grin "ret")) (App (primFnNameMap prim) [Var x', Var y', Var z'])
         $ Pure $ litCon (index 3 $ getTy prim) (Grin "ret")
primFnS _ _ = assert_total $ idris_crash "Not yet implemented"

primFnL : PrimFn arity -> Vect arity AVar -> Core Expr -- call and discard primFnS to add fn to apply
primFnL fn args = do
    ignore $ primFnS fn args
    pure $ Pure (Var $ primFnNameMap fn)

primFnInf : PrimFn arity -> Vect arity AVar -> Core Expr -- call and discard primFnS to add fn to apply
primFnInf fn args = do
    ignore $ primFnS fn args
    pure $ Pure (Var $ primFnNameMap fn)


mutual
    compileANF : ANF -> Core Expr
    compileANF (AV _ x) = pure $ Pure $ grinAVar x
    compileANF (AAppName _ Nothing name args) = pure $ App (grinName name) $ grinAVar <$> args
    compileANF (AAppName _ (Just LInf) name args) = pure $ Pure $ ConstTagNode (mkFInfTag $ grinName name) $ grinAVar <$> args
    compileANF (AAppName _ (Just _) name args) = pure $ Pure $ ConstTagNode (mkFTag $ grinName name) $ grinAVar <$> args
    compileANF (AUnderApp _ name missing args) = pure $ Pure $ ConstTagNode (mkPTag (grinName name) missing) $ grinAVar <$> args
    compileANF (AApp _ Nothing name arg) = pure $ appS name arg
    compileANF (AApp _ (Just LInf) name arg) = pure $ appInf name arg
    compileANF (AApp _ (Just _) name arg) = pure $ appL name arg
    compileANF (ALet _ var rhs rest) =
        pure $ Bind (Var $ Ind var)
            !(compileANF rhs)
            !(compileANF rest)
    compileANF (ACon _ name _ args) = pure $ Pure $ ConstTagNode (mkCTag $ grinName name) $ grinAVar <$> args
    compileANF (AOp _ Nothing prim args) = primFnS prim args
    compileANF (AOp _ (Just LInf) prim args) = primFnInf prim args
    compileANF (AOp _ (Just _) prim args) = primFnL prim args
    compileANF (AExtPrim _ Nothing name args) = pure $ App (grinName name) $ grinAVar <$> args
    compileANF (AExtPrim _ (Just LInf) name args) = pure $ Pure $ ConstTagNode (mkFInfTag $ grinName name) $ grinAVar <$> args
    compileANF (AExtPrim _ (Just _) name args) = pure $ Pure $ ConstTagNode (mkFTag $ grinName name) $ grinAVar <$> args
    compileANF (AConCase _ var alts Nothing) = -- force the value before case statement
        let name = nextName (grinAVar' var) in
        pure $ Bind (Var name) (eval $ grinAVar var)
        $ Case (Var name)
            !(traverse anfConCase alts)
    compileANF (AConCase _ var alts (Just exp)) =
        let name = nextName (grinAVar' var) in
        pure $ Bind (Var name) (eval $ grinAVar var)
        $ Case (grinAVar var)
            $ !(traverse anfConCase alts)
            ++ [Alt DefaultPat !(compileANF exp)]
    compileANF (AConstCase _ var alts@(MkAConstAlt c _ :: _) Nothing) =
        let tag = getConstTag c
            name = nextName (grinAVar' var) in
        pure $ Bind (ConstTagNode tag [Var name]) (eval $ grinAVar var)
        $ Case (Var name)
            !(traverse anfConstCase alts)
    compileANF (AConstCase _ var alts@(MkAConstAlt c _ :: _) (Just exp)) =
        let tag = getConstTag c
            name = nextName (grinAVar' var) in
        pure $ Bind (ConstTagNode tag [Var name]) (eval $ grinAVar var)
        $ Case (Var name)
            $ !(traverse anfConstCase alts)
            ++ [Alt DefaultPat !(compileANF exp)]
    compileANF (AConstCase _ var [] (Just exp)) = compileANF exp
    compileANF (AConstCase fc var [] Nothing) = assert_total $ idris_crash $ "Internal Error: empty case at " ++ show fc
    compileANF (APrimVal _ constant) = pure $ Pure $ grinConst constant
    compileANF (AErased _) = pure $ Pure $ ValTag $ mkCTag $ Grin "Erased"
    compileANF (ACrash _ msg) = pure $ App (Grin "_prim_crash") [VLit $ LString msg]

    anfConCase : AConAlt -> Core Expr
    anfConCase (MkAConAlt name _ args exp) =
        pure $ Alt (NodePat (mkCTag $ grinName name) (Ind <$> args)) !(compileANF exp)

    anfConstCase : AConstAlt -> Core Expr
    anfConstCase (MkAConstAlt const exp) = pure $ Alt (LitPat (grinLitConst const)) !(compileANF exp)

||| List of definitions
data GrinDefs : Type where

||| Eval function alts
data Eval : Type where

||| AppS function alts
data AppS : Type where
||| AppL function alts
data AppL : Type where
||| AppInf function alts
data AppInf : Type where

compileANFDef :
    Ref GrinDefs (List Expr) => -- top level definitions
    Ref Eval (List Expr) => -- alternatives in eval function
    Ref AppS (List Expr) => -- alternatives in apply function
    Ref AppL (List Expr) => -- alternatives in apply function
    Ref AppInf (List Expr) => -- alternatives in apply function
    (Core.Name, ANFDef) -> Core ()
compileANFDef (name, MkAFun args exp) = do -- add to app functions
    def <- pure $ Def (grinName name) (Ind <$> args) !(compileANF exp)
    update GrinDefs (def ::)
compileANFDef (name, MkACon tag arity nt) = pure () -- add constructor to eval function
                                                    -- already fully applied so don't add to app
compileANFDef (name, MkAForeign cc argTy retTy) = -- strip World, parse cc
    case retTy of
        CFIORes ret => let argTy' = filter (\case CFWorld => False ; _ => True) argTy in ?io
        _ => ?pure
compileANFDef (name, MkAError exp) = do -- add to app functions
    def <- pure $ Def (grinName name) [] !(compileANF exp)
    update GrinDefs (def ::)


compileExpr :
    Ref Ctxt Defs -> (tmpDir : String) -> (outDir : String) ->
    ClosedTerm -> (outFile : String) -> Core (Maybe String)
compileExpr defs tmpDir outDir tm outFile = do
    let outGrinFile = outDir </> tmpDir <.> "grin"

    cdata <- getCompileData True ANF tm

    defRef <- newRef GrinDefs $ the (List _) []
    evalRef <- newRef Eval $ the (List _) []
    applyRef <- newRef AppS $ the (List _) []
    applyRef <- newRef AppL $ the (List _) []
    applyRef <- newRef AppInf $ the (List _) []

    traverse_ compileANFDef cdata.anf

    defs <- get GrinDefs

    eval <- get Eval
    let evalExpr =
        Def (Grin "eval") [Ind 0] $
        Case (Var $ Ind 0) eval
    appS <- get Eval
    let appSExpr =
        Def (Grin "appS") [Ind 0, Ind 1] $
        Case (Var $ Ind 0) appS
    appL <- get Eval
    let appLExpr =
        Def (Grin "appL") [Ind 0, Ind 1] $
        Case (Var $ Ind 0) appL
    appInf <- get Eval
    let appInfExpr =
        Def (Grin "appInf") [Ind 0, Ind 1] $
        Case (Var $ Ind 0) appInf

    let outGrin = runBuilder $ prettyExpr (Prog []
            (evalExpr :: appSExpr :: appLExpr :: appInfExpr :: defs))

    coreLift_ $ writeFile outGrinFile outGrin

    pure Nothing

executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c _ tm = do
    coreLift_ $ putStrLn "Execute expression not yet implemented for grin"
    coreLift_ $ system "false"

export
grin : Codegen
grin = MkCG compileExpr executeExpr
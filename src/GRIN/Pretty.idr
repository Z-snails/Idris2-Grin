module GRIN.Pretty

import Data.String
import Data.List

import GRIN.Syntax

||| Diff List allowing for O(1) appending
data DList a = MkDList (List a -> List a)

Semigroup (DList a) where
    MkDList l <+> MkDList r = MkDList (l . r)


Monoid (DList a) where
    neutral = MkDList id

||| Diff List of Strings
Builder : Type
Builder = DList String

FromString Builder where
    fromString = MkDList . (::)

fromChar : Char -> Builder
fromChar = fromString . cast

escapedString : String -> Builder
escapedString = concat . map escapeChar . fastUnpack
  where
    escapeChar : Char -> Builder
    escapeChar = \case
        '"' => "\""
        '\\' => "\\\\"
        '\a' => "\\a"
        '\b' => "\\b"
        '\f' => "\\f"
        '\n' => "\\n"
        '\r' => "\\r"
        '\t' => "\\t"
        '\v' => "\\v"

        c => fromChar c

infixl 6 <->

||| Append two builder 
(<->) : Builder -> Builder -> Builder
MkDList l <-> MkDList r = MkDList (l . (" " ::) . r)

||| Convert something with a Show instance to a Builder
showB : Show a => a -> Builder
showB = fromString . show

||| Run a Builder returning a String
export
runBuilder : Builder -> String
runBuilder (MkDList strs) = fastAppend (strs [])

||| Append a list of Builders seperated by sep
intercalate : Builder -> List Builder -> Builder
intercalate _ [] = neutral
intercalate _ [x] = x
intercalate sep (x :: xs) = x <+> go sep xs
  where
    go : Builder -> List Builder -> Builder
    go _ [] = neutral
    go sep (x :: xs) = x <+> sep <+> go sep xs

spaceSep : List Builder -> Builder
spaceSep = intercalate " "

||| Put braces round a Builder
braces : Builder -> Builder
braces b = "{" <+> b <+> "}"

||| Put brackets round a Builder
bracket : Builder -> Builder
bracket b = "(" <+> b <+> ")"

||| Repeat a Char some number of times
repeat : Nat -> Char -> Builder
repeat n c = fromString $ fastPack $ replicate n c

||| Indent a builder n spaces
indent : {ind : Nat} -> Builder -> Builder
indent {ind} b = repeat ind ' ' <+> b

||| Pretty print a primitive Name
export
prettyPrimName : PrimName -> Builder
prettyPrimName = \case
    World => "World"
    WorldTy => "WorldTy"
    IntTy => "IntTy"
    IntegerTy => "IntegerTy"
    Bits8Ty => "Bits8Ty"
    Bits16Ty => "Bits16Ty"
    Bits32Ty => "Bits32Ty"
    Bits64Ty => "Bits64Ty"
    CharTy => "CharTy"
    StringTy => "StringTy"
    DoubleTy => "DoubleTy"

||| Pretty print a Name
export
prettyName : Name -> Builder
prettyName (User name) = "u_" <+> fromString name
prettyName (Ind i) = "v_" <+> showB i
prettyName (Gen name i) = prettyName name <+> "_" <+> showB i
prettyName (Grin name) = fromString name
prettyName Null = "null"
prettyName (Prim name) = "prim_" <+> prettyPrimName name

||| Pretty print a Simple Type
export
prettySimpleTy : SimpleTy -> Builder
prettySimpleTy = \case
    TInt => "T_Int64"
    TWord => "T_Word64"
    TFloat => "T_Float"
    TBool => "T_Bool"
    TUnit => "T_Unit"
    TChar => "T_Char"
    TString => "T_String"
    TDead => "T_Dead"

||| Pretty print a type
export
prettyTy : Ty -> Builder
prettyTy (TyCon name args) = braces
    (prettyName name <-> spaceSep (prettyTy <$> args))
prettyTy (TyVar name) = "%" <+> prettyName name
prettyTy (TySimple simple) = prettySimpleTy simple

||| Pretty print if a function is builtin
export
prettyBuiltin : Bool -> Builder
prettyBuiltin False = "ffi"
prettyBuiltin True = "primop"

||| Pretty print if a function is effectful
export
prettyEffect : Bool -> Builder
prettyEffect False = "pure"
prettyEffect True = "effectful"

||| Pretty print external function info
export
prettyExternal : External -> Builder
prettyExternal (MkExternal{name, retTy, argTy, builtin, effect}) =
    prettyBuiltin builtin <-> prettyEffect effect
    <+> indent {ind = 4}
        ( prettyName name
        <-> "::"
        <-> intercalate " -> " (prettyTy <$> argTy)
        <+> " -> " <+> prettyTy retTy
        )

||| Pretty print a tag
export
prettyTag : Tag -> Builder
prettyTag (MkTag{type, name}) = case type of
    C => "C" <+> prettyName name
    F => "F" <+> prettyName name
    FInf => "FInf" <+> prettyName name
    P missing => "P" <+> prettyName name <+> "_" <+> showB missing

||| Pretty print a literal
export
prettyLit : Lit -> Builder
prettyLit = \case
    LInt i => showB i
    LWord w => showB w
    LFloat f => showB f
    LBool True => "#True"
    LBool False => "#False"
    LChar c => "#'" <+> fromChar c <+> "'"
    LString str => "#\"" <+> escapedString str <+> "\""

||| Pretty print a value
export
prettyVal : Val -> Builder
prettyVal (ConstTagNode tag args) =
    bracket
        ( prettyTag tag
        <-> spaceSep (prettyVal <$> args)
        )
prettyVal (VarTagNode name args) =
    bracket
        ( prettyName name
        <-> spaceSep (prettyVal <$> args)
        )
prettyVal (ValTag tag) = prettyTag tag
prettyVal VUnit = "()"
prettyVal (VLit lit) = prettyLit lit
prettyVal (Var name) = prettyName name
prettyVal (Undefined ty) =
    bracket
        ( "#undefined ::" <-> prettyTy ty )

||| Pretty print a case pattern
export
prettyCPat : CPat -> Builder
prettyCPat (NodePat tag args) =
    prettyTag tag <-> spaceSep (prettyName <$> args)
prettyCPat (TagPat tag) = prettyTag tag
prettyCPat (LitPat lit) = prettyLit lit
prettyCPat DefaultPat = "#default"

||| Pretty print an Expr
export
prettyExpr : {default 0 ind : Nat} -> Expr -> Builder

prettyExpr (Prog externs defs) =
    intercalate "\n" (prettyExternal <$> externs)
    <+> "\n"
    <+> intercalate "\n" (prettyExpr <$> defs)

prettyExpr (Def name args expr) =
    prettyName name
    <-> spaceSep (prettyName <$> args)
    <-> "=\n"
    <+> indent {ind = 4 + ind}
        ( prettyExpr {ind = 4 + ind} expr )

prettyExpr (Bind val rhs rest) =
    prettyVal val
    <-> "<-" <-> prettyExpr {ind} rhs
    <+> "\n" <+> indent {ind} (prettyExpr {ind} rest)
prettyExpr (Discard rhs rest) =
    prettyExpr {ind} rhs
    <+> "\n" <+> indent {ind} (prettyExpr {ind} rest)
prettyExpr (Case val alts) =
    "case" <-> prettyVal val <-> "of\n"
    <+> intercalate "\n"
        ( indent {ind = 4 + ind}
        . prettyExpr {ind = 4 + ind}
        <$> alts
        )

prettyExpr (App name args) = 
    bracket
        (prettyName name <-> spaceSep (prettyVal <$> args)
        )
prettyExpr (Pure val) = "pure" <-> prettyVal val
prettyExpr (Store val) = "store" <-> prettyVal val
prettyExpr (Fetch name) = "fetch" <-> prettyName name
prettyExpr (Update name val) = "update" <-> prettyName name <-> prettyVal val

prettyExpr (Alt pat rhs) =
    prettyCPat pat <-> "->"
    <+> "\n" <+> indent {ind = 4 + ind}
        ( prettyExpr {ind = 4 + ind} rhs )

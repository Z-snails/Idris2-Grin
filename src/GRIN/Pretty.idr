module GRIN.Pretty

import Data.String
import Data.List

import Core.Name

import Compiler.Pipeline

import GRIN.Syntax

||| Number of spaces to indent.
indentSize : Nat
indentSize = 4

||| Diff List allowing for O(1) appending.
data DList a = MkDList (List a -> List a)

Semigroup (DList a) where
    MkDList l <+> MkDList r = MkDList (l . r)

Monoid (DList a) where
    neutral = MkDList id

||| Diff List of Strings, for O(1) appending.
Builder : Type
Builder = DList String

FromString Builder where
    fromString = MkDList . (::)

fromChar : Char -> Builder
fromChar = fromString . cast

escapedChar : Char -> Builder
escapedChar = \case
    '\"' => "\\\""
    '\\' => "\\\\"
    '\a' => "\\a"
    '\b' => "\\b"
    '\f' => "\\f"
    '\n' => "\\n"
    '\r' => "\\r"
    '\t' => "\\t"
    '\v' => "\\v"
    c => fromChar c

||| Pretty print a string with escape characters.
escapedString : String -> Builder
escapedString = concat . map escapedChar . fastUnpack

infixl 6 <->

||| Append two builder.
(<->) : Builder -> Builder -> Builder
l <-> r = l <+> " " <+> r

||| Put spaces before every builder in a foldable
spaceSep : Foldable t => t Builder -> Builder
spaceSep = foldMap (" " <+>)

||| Put newlines before every builder in a foldable
nlSep : Foldable t => t Builder -> Builder
nlSep = foldMap ("\n" <+>)

bracket : Builder -> Builder
bracket b = "(" <+> b <+> ")"

indent : Nat -> Builder
indent Z = ""
indent (S k) = " " <+> indent k

||| Convert something with a Show instance to a Builder.
showB : Show a => a -> Builder
showB = fromString . show

||| Run a Builder returning a String.
export
runBuilder : Builder -> String
runBuilder (MkDList strs) = fastAppend (strs [])

||| Pretty print a grin name.
prettyName : Name -> Builder
prettyName (NS ns n) = showB ns <+> "." <+> prettyName n
prettyName (UN n) = fromString n
prettyName (MN n i) = fromString n <+> "." <+> showB i
prettyName (PV n i) = "pv_" <+> prettyName n <+> "." <+> showB i
prettyName (DN _ n) = prettyName n
prettyName (RF n) = "rf_" <+> fromString n
prettyName (Nested (x, y) n) = "n" <+> showB x <+> showB y <+> "_" <+> prettyName n
prettyName (CaseBlock n i) = "cb" <+> showB i <+> "_" <+> fromString n
prettyName (WithBlock n i) = "wb" <+> showB i <+> "_" <+> fromString n
prettyName (Resolved i) = "r" <+> showB i -- 'r' not 'v' to not conflict with GrinVar

||| Pretty print a grin variable.
prettyGrinVar : GrinVar -> Builder
prettyGrinVar (Var x) = "v" <+> showB x
prettyGrinVar (Fixed n) = "\"n" <+> prettyName n <+> "\""
prettyGrinVar (Grin n) = fromString n

||| Pretty print a tag type.
prettyTagType : TagType -> Builder
prettyTagType Con = "C"
prettyTagType Thunk = "F"
prettyTagType InfThunk = "F\"Inf\\"
prettyTagType (Missing missing) = "P" <+> showB missing

||| Pretty print a tag.
prettyTag : Tag -> Builder
prettyTag (MkTag{tagType, tagName = (Fixed tagName)}) =
    prettyTagType tagType <+> "\"" <+> prettyName tagName <+> "\""
prettyTag (MkTag{tagType, tagName = (Grin tagName)}) =
    prettyTagType tagType <+> fromString tagName
prettyTag (MkTag{tagType, tagName = (Var _)}) =
    "Internal Error: Unexpected `Var` in `Tag`"

||| Pretty print a GRIN literal.
prettyGrinLit : GrinLit -> Builder
prettyGrinLit = \case
    LInt i => showB i
    LBits64 i => showB i <+> "u"
    LDouble d => showB d
    LChar c => "#'" <+> escapedChar c <+> "'"
    LString s => "#\"" <+> escapedString s <+> "\""

||| Pretty print a simple type.
prettySimpleType : SimpleType -> Builder
prettySimpleType = \case
    IntTy => "T_Int64"
    Bits64Ty => "T_Word64"
    DoubleTy => "T_Float"
    CharTy => "T_Char"
    StringTy => "T_String"

||| Pretty print a GRIN type.
prettyGrinType : GrinType -> Builder
prettyGrinType (TyCon var args) =
    prettyGrinVar var <+> spaceSep (prettyGrinType <$> args)
prettyGrinType (TySimple ty) = prettySimpleType ty

||| Pretty print a simple value.
prettySimpleVal : SimpleVal -> Builder
prettySimpleVal (SLit lit) = prettyGrinLit lit
prettySimpleVal (SVar var) = prettyGrinVar var
prettySimpleVal (SUndefined ty) = "#undefined :: " <+> prettyGrinType ty

||| Pretty print a GRIN value.
prettyVal : Val -> Builder
prettyVal (VTagNode tag args) =
    bracket $ prettyTag tag <+> spaceSep (prettySimpleVal <$> args)
prettyVal (VTag tag) = prettyTag tag
prettyVal (VSimpleVal val) = prettySimpleVal val
prettyVal VUnit = "()"

||| Pretty print a case pattern.
prettyCPat : CasePat -> Builder
prettyCPat (NodePat tag args) = bracket $ prettyTag tag <+> spaceSep (prettyGrinVar <$> args)
prettyCPat (TagPat tag) = bracket $ prettyTag tag
prettyCPat (LitPat lit) = prettyGrinLit lit
prettyCPat Default = "#default"

mutual
    ||| Pretty print a simple expression.
    prettySimpleExp : (indent : Nat) -> SimpleExp -> Builder
    prettySimpleExp ind (Do exp) = "do\n" <+> prettyGrinExp (ind + indentSize) exp
    prettySimpleExp ind (App f args) =
        prettyGrinVar f <+> spaceSep (prettyGrinVar <$> args)
    prettySimpleExp ind (Pure val) = "pure" <-> prettyVal val
    prettySimpleExp ind (Store val) = "store" <-> prettyVal val
    prettySimpleExp ind (Fetch var) = "fetch" <-> prettyGrinVar var
    prettySimpleExp ind (Update var val) =
        "update" <-> prettyGrinVar var <-> prettyVal val

    ||| Pretty print a GRIN expression.
    prettyGrinExp : (indent : Nat) -> GrinExp -> Builder
    prettyGrinExp ind (Bind VUnit exp rest) =
        prettySimpleExp ind exp <+> "\n"
        <+> indent ind <+> prettyGrinExp ind rest
    prettyGrinExp ind (Bind val exp rest) =
        prettyVal val <-> "<-" <-> prettySimpleExp ind exp <+> "\n"
        <+> indent ind <+> prettyGrinExp ind rest
    prettyGrinExp ind (Case val alts) =
        "case" <-> prettyVal val <-> "of"
        <+> nlSep (prettyGrinAlt (ind + indentSize) <$> alts)
    prettyGrinExp ind (Simple exp) = prettySimpleExp ind exp
    
    prettyGrinAlt : (indent : Nat) -> GrinAlt -> Builder
    prettyGrinAlt ind (MkAlt pat exp) =
        indent ind <+> prettyCPat pat <-> "->\n" <+> indent (ind + indentSize) <+> prettyGrinExp (ind + indentSize) exp

||| Pretty print a top level definition.
prettyGrinDef : GrinDef -> Builder
prettyGrinDef (MkDef n args exp) =
    prettyGrinVar n <+> spaceSep (prettyGrinVar <$> args)
    <-> "=\n" <+> indent indentSize <+> prettyGrinExp indentSize exp

||| Pretty print external information.
prettyExternal : (indent : Nat) -> External -> Builder
prettyExternal ind ext =
    indent ind <+> foldMap (<+> " -> ") (prettyGrinType <$> ext.argTy) <+>
    prettyGrinType ext.retTy

||| Include a Builder if a list is non-empty.
ifCons : List a -> Builder -> Builder
ifCons [] _ = ""
ifCons _ b = b

||| Pretty print an entire program.
prettyProg : GrinProg -> Builder
prettyProg (MkProg exts defs) =
    let (primPure, primEff, ffiPure, ffiEff) = splitExterns exts in
    ifCons primPure ("\nprimop pure" <+> nlSep (prettyExternal indentSize <$> primPure)) <+>
    ifCons primPure ("\nprimop effectful" <+> nlSep (prettyExternal indentSize <$> primPure)) <+>
    ifCons primPure ("\nffi pure" <+> nlSep (prettyExternal indentSize <$> primPure)) <+>
    ifCons primPure ("\nffi effectful" <+> nlSep (prettyExternal indentSize <$> primPure)) <+>
    "\n" <+> nlSep (prettyGrinDef <$> defs)

export
prettyGrin : TransInfo (\x => x) GrinProg String
prettyGrin = MkTI $ runBuilder . prettyProg
||| Pretty printing compatible with this [grin](https://github.com/grin-compiler/grin).
module GRIN.PrettyCompatB

import Data.SortedMap
import Data.String.Builder

import GRIN.AST
import GRIN.Name

export
ShowB Var where
    showB (MkVar i) = "v" <+> showB @{FromShow} i

export
ShowB TagType where
    showB Con = "C"
    showB UThunk = "FU"
    showB NUThunk = "FNU"
    showB (Partial missing) = "P" <+> showB @{FromShow} missing

escapeChar : Char -> String
escapeChar = \case
    '"' => "\\\""
    '\\' => "\\\\"
    '\a' => "\\a"
    '\b' => "\\b"
    '\f' => "\\f"
    '\n' => "\\n"
    '\r' => "\\r"
    '\t' => "\\t"
    '\v' => "\\v"
    c => cast c

escapeString : String -> Builder
escapeString = fromString . fastConcat . map escapeChar . unpack

escapeBuilder : Builder -> Builder
escapeBuilder = mapString $ fastConcat . map escapeChar . unpack

export
Show name => ShowB (Tag name) where
    showB (MkTag tagType tag) = "C\"" <+> showB tagType <+> escapeString (show tag) <+> "\""

export
ShowB Lit where
    showB (LInt i) = showB @{FromShow} i
    showB (LDouble x) = showB @{FromShow} x
    showB (LString s) = "#\"" <+> escapeString s <+> "\""
    showB (LChar c) = "#'" <+> fromString (escapeChar c) <+> "'"

ShowB IntPrec where
    showB (Signed n) = "T_Int" <+> showB @{FromShow} n
    showB (UnSigned n) = "T_Word" <+> showB @{FromShow} n

export
ShowB SType where
    showB (IntType prec) = showB prec
    showB (HeapPtr i) = "T_Location" <+> showB @{FromShow} i

export
Show name => ShowB (GType name) where
    showB (SimpleType ty) = showB ty
    showB Cons = "Constructor"

export
Show name => ShowB (FuncType name) where
    showB (MkFuncType args ret) =
        foldMap (\arg => showB arg <+> " -> ") args <+> showB ret

export
ShowB SVal where
    showB (SVar v) = showB v
    showB (SLit l) = showB l

export
Show name => ShowB (Val name) where
    showB (SimpleVal val) = showB val
    showB (ConstTagNode tag args) = parens $ function tag args
    showB (ConstTag tag) = showB tag
    showB (VarTagNode tag args) = parens $ function tag args
    showB VUnit = "()"

export
Show name => ShowB (CasePat name) where
    showB (NodePat tag args) = parens $ function tag args
    showB (TagPat tag) = showB tag
    showB (LitPat lit) = showB lit
    showB DefaultPat = "#default"

mutual
    showBSExp : Show name => (indent : Nat) -> SExp name -> Builder
    showBSExp i (Do exp) = "do\n"
        <+> indent (1 + i) (showBExp (1 + i) exp) 
    showBSExp _ (App f args) = function @{FromShow} f args
    showBSExp _ (Pure val) = "pure " <+> showB val
    showBSExp _ (Store val) = "store " <+> showB val
    showBSExp _ (Fetch _ var) = "fetch " <+> showB var
    showBSExp _ (FetchI _ i var) =
        "fetch " <+> showB var <+> bracket (showB @{FromShow} i)
    showBSExp _ (Update var val) =
        "update " <+> showB var <+> " " <+> showB val

    showBExp : Show name => (indent : Nat) -> Exp name -> Builder
    showBExp i (SimpleExp exp) = showBSExp i exp
    showBExp i (Bind VUnit rhs rest) =
        showBSExp i rhs <+> "\n"
        <+> indent i (showBExp i rest)
    showBExp i (Bind val rhs rest) =
        showB val <+> " <- " <+> showBSExp i rhs <+> "\n"
        <+> indent i (showBExp i rest)
    showBExp i (Case val alts) =
        "case " <+> showB val <+> " of"
        <+> foldMap (\alt => "\n"
            <+> indent (1 + i) (showBAlt (i + 1) alt))
            alts

    showBAlt : Show name => (indent : Nat) -> Alt name -> Builder
    showBAlt i (MkAlt pat exp) =
        showB pat <+> " ->\n"
        <+> indent (i + 1) (showBExp (i + 1) exp)

export
Show name => ShowB (SExp name) where
    showB = showBSExp 0

export
Show name => ShowB (Exp name) where
    showB = showBExp 0

export
Show name => ShowB (Alt name) where
    showB = showBAlt 0

export
Show name => ShowB (Def name) where
    showB (MkDef fn args exp _) = function @{FromShow} fn args <+> " =\n" <+> indent 1 (showBExp 1 exp)

export
Show name => ShowB (Prog name) where
    showB (MkProg exts defs _) =
        -- showB externs
        nlSep $ values defs

||| Pretty printing compatible with this [grin](https://github.com/grin-compiler/grin).
module GRIN.PrettyCompat

import Data.SortedMap
import Data.String.Utils

import GRIN.AST
import GRIN.Name

export
Show Var where
    show (MkVar i) = "v" ++ show i

export
Show TagType where
    show Con = "C"
    show UThunk = "FU"
    show NUThunk = "FNU"
    show (Partial missing) = "P" ++ show missing

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

escapeString : String -> String
escapeString = fastConcat . map escapeChar . unpack

export
Show name => Show (Tag name) where
    show (MkTag tagType tag) = "C\"" ++ show tagType ++ escapeString (show tag) ++ "\""

export
Show Lit where
    show (LInt i) = show i
    show (LDouble x) = show x
    show (LString s) = "#\"" ++ escapeString s ++ "\""
    show (LChar c) = "#'" ++ escapeChar c ++ "'"

Show IntPrec where
    show (Signed n) = "T_Int" ++ show n
    show (Unsigned n) = "T_Word" ++ show n

export
Show SType where
    show (IntTy prec) = show prec
    show DoubleTy = "T_Float"
    show CharTy = "T_Char"
    show StringTy = "T_String"
    show UnitTy = "T_Unit"
    show (HeapPtr i) = "T_Location" ++ show i

export
Show name => Show (GType name) where
    show (SimpleType ty) = show ty
    show (TyVar x) = "%" ++ show x
    show Cons = "Constructor"

export
Show name => Show (FuncType name) where
    show (MkFuncType args ret) =
        foldMap (\arg => show arg ++ " -> ") args ++ show ret

export
Show SVal where
    show (SVar v) = show v
    show (SLit l) = show l

export
Show name => Show (Val name) where
    show (SimpleVal val) = show val
    show (ConstTagNode tag args) = parens $ function tag args
    show (ConstTag tag) = show tag
    show (VarTagNode tag args) = parens $ function tag args
    show VUnit = "()"

export
Show name => Show (CasePat name) where
    show (NodePat tag args) = parens $ function tag args
    show (TagPat tag) = show tag
    show (LitPat lit) = show lit
    show DefaultPat = "#default"

mutual
    showBSExp : Show name => (indent : Nat) -> SExp name -> String
    showBSExp i (Do exp) = "do\n"
        ++ indent (1 + i) (showBExp (1 + i) exp) 
    showBSExp _ (App f args) = function f args
    showBSExp _ (Pure val) = "pure " ++ show val
    showBSExp _ (Store val) = "store " ++ show val
    showBSExp _ (Fetch _ var) = "fetch " ++ show var
    showBSExp _ (FetchI _ i var) =
        "fetch " ++ show var ++ bracket (show i)
    showBSExp _ (Update var val) =
        "update " ++ show var ++ " " ++ show val

    showBExp : Show name => (indent : Nat) -> Exp name -> String
    showBExp i (SimpleExp exp) = showBSExp i exp
    showBExp i (Bind VUnit rhs rest) =
        showBSExp i rhs ++ "\n"
        ++ indent i (showBExp i rest)
    showBExp i (Bind val rhs rest) =
        show val ++ " <- " ++ showBSExp i rhs ++ "\n"
        ++ indent i (showBExp i rest)
    showBExp i (Case val alts) =
        "case " ++ show val ++ " of"
        ++ foldMap (\alt => "\n"
            ++ indent (1 + i) (showBAlt (i + 1) alt))
            alts

    showBAlt : Show name => (indent : Nat) -> Alt name -> String
    showBAlt i (MkAlt pat exp) =
        show pat ++ " ->\n"
        ++ indent (i + 1) (showBExp (i + 1) exp)

export covering
Show name => Show (SExp name) where
    show = showBSExp 0

export covering
Show name => Show (Exp name) where
    show = showBExp 0

export covering
Show name => Show (Alt name) where
    show = showBAlt 0

export covering
Show name => Show (Def name) where
    show (MkDef fn args exp _) = function fn args ++ " =\n" ++ indent 1 (showBExp 1 exp)

export covering
Show name => Show (Prog name) where
    show (MkProg exts defs _) =
        -- show externs
        nlSep $ values defs

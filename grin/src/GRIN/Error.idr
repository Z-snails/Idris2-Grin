module GRIN.Error

import System.File

import GRIN.AST

public export
data Error
    = FileErr String FileError
    | MissingVar Var

export
Show Error where
    show (FileErr f err) = "File error with file " ++ show f ++ "\n" ++ show err ++ "\n\n"
    show (MissingVar (MkVar v)) = "Missing variable from VarMap (v" ++ show v ++ ")\n\n"

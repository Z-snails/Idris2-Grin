module Grin.Prims.Functions

import Data.Vect
import Data.List

import Core.Core
import Compiler.ANF

import Grin.Syntax

export
replicateCore : Nat -> Core a -> Core (List a)
replicateCore Z act = pure []
replicateCore (S k) act = (::) <$> act <*> replicateCore k act

||| Next variable (Int).
export
data NextId : Type where

export
nextId : Ref NextId Int => Core Int
nextId = do
    i <- get NextId
    put NextId (i + 1)
    pure i

export
nextVar : Ref NextId Int => Core GrinVar
nextVar = Var <$> nextId

||| Make a primitive Tag.
export
primTag : String -> Tag
primTag = MkTag Con . Grin

||| Make a unary primitive Tag.
export
primTagUnary : String -> GrinLit -> Val
primTagUnary n val = VTagNode (primTag n) [SLit val]

||| Make a 0-arity primitive Tag.
export
primTagNullary : String -> Val
primTagNullary tag = VTagNode (primTag tag) []

export
mkPrimFn :
    Ref NextId Int =>
    (fn : String) -> -- prim__<fn>
    (binds : List String) -> -- constructors for arguments
    (prim : String) -> -- _prim_<prim>
    (ret : String) -> -- constructor for return type
    Core GrinDef
mkPrimFn fn [] prim ret = do
    r <- nextVar
    pure $ MkDef
        (Grin fn)
        []
        $ Bind (VVar r) (App (Grin prim) [])
        $ Simple $ Pure (VTagNode (primTag ret) [SVar r])
mkPrimFn fn binds prim ret = do
    let ca = length binds
    args <- replicateCore ca nextVar
    bounds <- replicateCore ca nextVar
    let bindings =
            zipWith
                (\bi, bo => VTagNode (primTag bi) [SVar bo])
                binds
                bounds
    r <- nextVar
    pure $ MkDef
        (Grin fn)
        args
        $ bindArgs args bindings
        $ Bind (VVar r) (App (Grin prim) $ bounds)
        $ Simple $ Pure $ VTagNode (primTag ret) [SVar r] 
  where
    bindArgs : List GrinVar -> List Val -> GrinExp -> GrinExp
    bindArgs [] _ k = k
    bindArgs _ [] k = k
    bindArgs (arg :: rArgs) (bind :: rBinds) k =
        Bind bind (App (Grin "eval") [arg])
        $ bindArgs rArgs rBinds k

export
unaryFromTo :
    Ref NextId Int =>
    ( String -- function name
    , String -- constructor for arguments
    , String -- primitive function
    , String -- constructor for return type
    ) ->
    Core GrinDef
unaryFromTo (fn, from, prim, to) = mkPrimFn ("prim__" ++ fn) [from] prim to

export
unary :
    Ref NextId Int =>
    ( String -- function name
    , String -- constructor
    , String -- primitive function
    ) ->
    Core GrinDef
unary (fn, bind, prim) = unaryFromTo (fn, bind, prim, bind)

export
binaryFromTo :
    Ref NextId Int =>
    ( String -- function name
    , String -- constructor for arguments
    , String -- primitive function
    , String -- constructor for return type
    ) ->
    Core GrinDef
binaryFromTo (fn, from, prim, to) = mkPrimFn ("prim__" ++ fn) [from, from] prim to

export
binary :
    Ref NextId Int =>
    ( String -- function name
    , String -- constructor
    , String -- primitive function
    ) ->
    Core GrinDef
binary (fn, bind, prim) = binaryFromTo (fn, bind, prim, bind)

export
binaryBoolToInt :
    Ref NextId Int =>
    (fn : String) -> -- function name
    (binds : List String) -> -- constructor for arguments
    (prim : String) -> -- primitive function
    (ret : String) -> -- constructor for return type
    Core GrinDef
binaryBoolToInt fn [] prim ret = do
    r <- nextVar
    pure $ MkDef
        (Grin fn)
        []
        $ Bind (VVar r) (App (Grin prim) [])
        $ Case (VVar r)
            [ MkAlt FalsePat
                $ Simple $ Pure $ VTagNode (primTag ret) [SLit $ LInt 0]
            , MkAlt TruePat
                $ Simple $ Pure $ VTagNode (primTag ret) [SLit $ LInt 1]
            ]
binaryBoolToInt fn binds prim ret = do
    let ca = length binds
    args <- replicateCore ca nextVar
    bounds <- replicateCore ca nextVar
    let bindings =
            zipWith
                (\bi, bo => VTagNode (primTag bi) [SVar bo])
                binds
                bounds
    r <- nextVar
    pure $ MkDef
        (Grin fn)
        args
        $ bindArgs args bindings
        $ Bind (VVar r) (App (Grin prim) $ bounds)
        $ Case (VVar r)
            [ MkAlt FalsePat
                $ Simple $ Pure $ VTagNode (primTag ret) [SLit $ LInt 0]
            , MkAlt TruePat
                $ Simple $ Pure $ VTagNode (primTag ret) [SLit $ LInt 1]
            ]
  where
    bindArgs : List GrinVar -> List Val -> GrinExp -> GrinExp
    bindArgs [] _ k = k
    bindArgs _ [] k = k
    bindArgs (arg :: rArgs) (bind :: rBinds) k =
        Bind bind (App (Grin "eval") [arg])
        $ bindArgs rArgs rBinds k

export
binaryBool :
    Ref NextId Int =>
    ( String -- function name
    , String -- constructor for arguments
    , String -- primitive function
    , String -- constructor for return type
    ) ->
    Core GrinDef
binaryBool (fn, arg, prim, ret) = binaryBoolToInt ("prim__" ++ fn) [arg, arg] prim ret

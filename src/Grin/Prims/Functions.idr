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
    (fn : String) ->
    (binds : List String) ->
    (prim : String) ->
    (ret : String) ->
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
    ( String
    , String
    , String
    , String
    ) ->
    Core GrinDef
unaryFromTo (fn, from, prim, to) = mkPrimFn ("prim__" ++ fn) [from] prim to

export
unary :
    Ref NextId Int =>
    ( String
    , String
    , String
    ) ->
    Core GrinDef
unary (fn, bind, prim) = mkPrimFn ("prim__" ++ fn) [bind] prim bind

export
binary :
    Ref NextId Int =>
    ( String
    , String
    , String
    ) ->
    Core GrinDef
binary (fn, bind, prim) = mkPrimFn ("prim__" ++ fn) [bind, bind] prim bind
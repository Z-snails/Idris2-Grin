module GRIN.ANF

import Data.Vect
import Data.SortedSet
import Data.Maybe
import Data.List

import System
import System.File

import Libraries.Data.IntMap
import Libraries.Utils.Path

import Core.Core
import Core.Context
import Core.CompileExpr
import Core.TT

import Compiler.ANF
import Compiler.Common
import Compiler.Pipeline

import GRIN.Syntax
import GRIN.Pretty
import GRIN.Prim

||| Map from ANF indexes to GRIN variables
data VarMap : Type where

||| Get the GRIN var for an ANF index
||| Creates a new variable if necessary
getAnfVar :
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Int -> Core GrinVar
getAnfVar i = do
    map <- get VarMap
    case lookup i map of
        Nothing => do
            i' <- nextVar
            update VarMap (insert i i')
            pure i'
        Just i' => pure i'

||| Set the GRIN var for an ANF index
setAnfVar :
    Ref VarMap (IntMap GrinVar) =>
    Int -> GrinVar -> Core ()
setAnfVar i var = update VarMap $ insert i var

||| Whether each variable is a pointer or value.
data PointerMap : Type where

||| Check if a variable is a pointer.
||| Defaults to is a pointer.
varIsPointer : Ref PointerMap (SortedSet GrinVar) => GrinVar -> Core Bool
varIsPointer var = pure $ contains var !(get PointerMap)

||| Set if a variable is a pointer.
||| Overwriting is allowed.
-- No need to set as false as that is default
-- I don't expect it'll ever have to set to False
-- But I'm not sure so I'll leave it in for now
setVarPointer :
    Ref PointerMap (SortedSet GrinVar) =>
    GrinVar -> (isPointer : Bool) -> Core ()
setVarPointer var isPointer = update PointerMap
    $ if isPointer
        then insert var
        else delete var

nextVar' :
    Ref NextId Int =>
    Ref PointerMap (SortedSet GrinVar) =>
    (isPointer : Bool) -> Core GrinVar
nextVar' ip = do
    var <- nextVar
    setVarPointer var ip
    pure var

||| Returns constructor for lazy version of a function.
getLazyTag : LazyReason -> GrinVar -> Tag
getLazyTag LInf n = MkTag InfThunk n
getLazyTag _ n = MkTag Thunk n

||| Returns constructor for partial function application.
getPartialTag : (missing : Nat) -> GrinVar -> Tag
getPartialTag = MkTag . Missing

||| Return app function with correct laziness.
getAppVar : Maybe LazyReason -> GrinVar
getAppVar Nothing = Grin "appS"
getAppVar (Just LInf) = Grin "appInf"
getAppVar (Just _) = Grin "appL"

erasedTag : Tag
erasedTag = MkTag Con $ Grin "Erased"

eval : {auto 1 expTy : Either (exp = SimpleExp) (exp = GrinExp)} -> GrinVar -> exp
eval {expTy = Left prf} var = rewrite prf in App (Grin "eval") [var]
eval {expTy = Right prf} var = rewrite prf in Simple $ App (Grin "eval") [var]

fromToPointer' : {auto p : Either (exp = SimpleExp) (exp = GrinExp)} -> (fromPointer : Bool) -> (needPointer : Bool) -> GrinVar -> exp
fromToPointer' {p = Left prf} False False = rewrite prf in Pure . VVar
fromToPointer' {p = Left prf} False True = rewrite prf in Store . VVar
fromToPointer' {p = Left prf} True False = rewrite prf in Fetch
fromToPointer' {p = Left prf} True True = rewrite prf in Pure . VVar
fromToPointer' {p = Right prf} fp np = rewrite prf in Simple . fromToPointer' {p = Left Refl} fp np

fromToPointer :
    {auto p : Either (exp = SimpleExp) (exp = GrinExp)} ->
    Ref PointerMap (SortedSet GrinVar) =>
    (needPointer : Bool) -> GrinVar ->
    Core exp
fromToPointer np var = pure $ fromToPointer' !(varIsPointer var) np var

getPointer :
    {auto p : Either (exp = SimpleExp) (exp = GrinExp)} ->
    (needPointer : Bool) -> Val ->
    exp
getPointer {p = Left prf} np v =
    rewrite prf in if np then Store v else Pure v
getPointer {p = Right prf} np v =
    rewrite prf in Simple $ getPointer {p = Left Refl} np v

fetches :
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    List AVar ->
    (List GrinVar -> Core GrinExp) ->
    Core GrinExp
fetches args k = go args []
  where
    go : List AVar -> List GrinVar -> Core GrinExp
    go [] acc = k (reverse acc)
    go (ANull :: args) acc = do
        var <- nextVar' True
        pure $ Bind (VVar var) (getPointer True $ VTag erasedTag)
             !(go args (var :: acc))
    go (ALocal i :: args) acc = do
        var <- getAnfVar i
        var' <- nextVar' True
        pure $ Bind (VVar var') !(fromToPointer True var) -- function arguments are pointers
             !(go args (var' :: acc))

||| Forget the length of a vector.
forgetLen : Vect h a -> List a
forgetLen [] = []
forgetLen (x :: xs) = x :: forgetLen xs

compilePrimFn : 
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    (needPointer : Bool) -> -- whether a pointer is required
    Maybe LazyReason ->
    PrimFn arity ->
    Vect arity AVar ->
    (GrinVar -> Core GrinExp) -> -- rest of the grin expression
    Core GrinExp
compilePrimFn np Nothing fn args k = do -- strict
    -- Todo: add primitive functions to output when they're used
    -- for now just add them all
    res <- nextVar
    ret <- nextVar
    setVarPointer ret np
    fetches (forgetLen args) \args' =>
        pure $ Bind (VVar res) (App (Grin $ getPrimFnName fn) args')
             $ Bind (VVar ret) !(fromToPointer np res)
             !(k ret)
compilePrimFn np (Just lazy) fn args k = -- lazy
    fetches (forgetLen args) \args' => do
        ret <- nextVar
        setVarPointer ret np
        pure $ Bind (VVar ret) (getPointer np $ VTagNode (getLazyTag lazy $ Grin $ getPrimFnName fn) $ SVar <$> args')
             !(k ret)

compileExtPrim : 
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    (needPointer : Bool) -> -- whether a pointer is required
    Maybe LazyReason ->
    Name ->
    List AVar ->
    (GrinVar -> Core GrinExp) -> -- rest of the grin expression
    Core GrinExp
compileExtPrim np ret _ f args = assert_total $ idris_crash "compileExtPrim is not yet implemented"
-- Todo: Get external function expected type
-- if primtive then unwrap else just pass it

mutual
    ||| Compile an ANF expression.
    ||| Takes a continuation of what to do with the result. 
    compileANF :
        Ref NextId Int =>
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        ANF -> -- ANF expression to compile
        (GrinVar -> Core GrinExp) -> -- rest of the grin expression
        Core GrinExp
    compileANF np (AV _ ANull) k = do
        ret <- nextVar' np
        pure $ Bind (VVar ret) (getPointer np $ VTag erasedTag) -- for now this is just a tag
             !(k ret)                                   -- but I'd like it to be removed entirely
                                                        -- I don't know if actually removing the argument
                                                        -- will be added to `CExp` backends.
    compileANF np (AV _ (ALocal ai)) k = do
        i <- getAnfVar ai -- get the GRIN variable
        ret <- nextVar' np
        pure $ Bind (VVar ret) !(fromToPointer np i)
             !(k ret)
    compileANF np (AAppName _ Nothing n args) k = do
        i <- nextVar -- result of function
        fetches args \args' => do
            ret <- nextVar' np
            pure $ Bind (VVar i) (App (Fixed n) args') -- functions always return values
                 $ Bind (VVar ret) !(fromToPointer np i) -- GRIN will optimise this if pure
                 !(k ret)
    compileANF np (AAppName _ (Just lazy) n args) k =
        fetches args \args' => do
            ret <- nextVar' np
            pure $ Bind (VVar ret) (getPointer np $ VTagNode (getLazyTag lazy $ Fixed n) (SVar <$> args'))
                 !(k ret)
    compileANF np (AUnderApp _ n missing args) k =
        fetches args \args' => do
            ret <- nextVar' np
            pure $ Bind (VVar ret) (getPointer np $ VTagNode (getPartialTag missing $ Fixed n) (SVar <$> args'))
                 !(k ret)
    compileANF np (AApp _ lazy af aarg) k = do
        let ALocal af' = af
            | ANull => throw $ InternalError "Erased argument can't be called as a function"
        f <- getAnfVar af'
        ret <- nextVar' np
        case aarg of
            ALocal iarg => do
                arg <- getAnfVar iarg
                pure $ Bind (VVar ret) (App (getAppVar lazy) [f, arg])
                     !(k ret)
            ANull => do
                arg <- nextVar' True -- function arguments are pointers
                pure $ Bind (VVar arg) (getPointer True $ VTag erasedTag)
                     $ Bind (VVar ret) (App (getAppVar lazy) [f, arg])
                     !(k ret)
    compileANF np (ALet _ anf rhs rest) k = do
        compileANF False rhs \res => do
            setAnfVar anf res
            compileANF np rest k
    compileANF np (ACon _ n _ []) k = do -- Constructors are always fully applied
        ret <- nextVar' np
        pure $ Bind (VVar ret) (getPointer np $ VTag $ MkTag Con $ Fixed n)
             !(k ret)
    compileANF np (ACon _ n _ args) k =
        fetches args \args' => do
            ret <- nextVar' np
            pure $ Bind (VVar ret) (getPointer np $ VTagNode (MkTag Con $ Fixed n) $ SVar <$> args')
                 !(k ret)
    compileANF np (AOp _ lazy op args) k = compilePrimFn np lazy op args k
        -- basically a normal function that calls the correct grin primitive
    compileANF np (AExtPrim _ lazy op args) k = compileExtPrim np lazy op args k
    compileANF _ (AConCase _ ANull _ _) _ = throw $ InternalError "Attempt to match on erased in ANF"
    compileANF np (AConCase _ (ALocal var) alts def) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        evaled <- nextVar
        pure $ Bind (VVar fetched) !(fromToPointer True var') -- make pointer before passing to eval
             $ Bind (VVar evaled) (eval fetched)
             $ Case (VVar evaled)
                !(case def of
                    Nothing => (traverse (\alt => compileAConAlt np alt k) alts)
                    Just exp => do
                        alts <- traverse (\alt => compileAConAlt np alt k) alts
                        defAlt <- pure [MkAlt Default !(compileANF np exp k)]
                        pure $ alts ++ defAlt
                )
    compileANF _ (AConstCase _ ANull _ _) _ = throw $ InternalError "Attempt to match on erased in ANF"
    compileANF np (AConstCase _ (ALocal var) alts@(alt :: _) def) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        evaledUnwrapped <- nextVar
        pure $ Bind (VVar fetched) !(fromToPointer True var') -- make pointer before passing to eval
             $ Bind (unwrapPrim alt evaledUnwrapped) (eval fetched) -- unwrap primitive before passing to case
             $ Case (VVar evaledUnwrapped)
                !(case def of
                    Nothing => (traverse (\alt => compileAConstAlt np alt k) alts)
                    Just exp => do
                        alts <- traverse (\alt => compileAConstAlt np alt k) alts
                        defAlt <- pure [MkAlt Default !(compileANF np exp k)]
                        pure $ alts ++ defAlt
                )
    compileANF np (AConstCase _ (ALocal var) [] (Just exp)) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        ign <- nextVar
        pure $ Bind (VVar fetched) !(fromToPointer True var') -- make pointer before passing to eval
             $ Bind (VVar ign) (eval fetched) -- evaluate to ensure correct laziness semantics (I think)
             !(compileANF np exp k)
    compileANF _ (AConstCase _ _ [] Nothing) _ = throw $ InternalError "Empty case block"
    compileANF np (APrimVal _ val) k = do
        ret <- nextVar' np
        pure $ Bind (VVar ret) (getPointer np $ getConstVal val)
             !(k ret)
    compileANF np (AErased _) k = do
        ret <- nextVar' np
        pure $ Bind (VVar ret) (getPointer np $ VTag erasedTag)
             !(k ret)
    compileANF np (ACrash _ msg) _ = do
        msg' <- nextVar
        pure $ Bind (VVar msg') (Pure $ primTagNode "String" $ LString msg)
             $ Simple $ App (Grin "prim__idris_crash") [msg']

    compileAConAlt :
        Ref NextId Int =>
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        AConAlt ->
        (GrinVar -> Core GrinExp) -> -- rest of the grin expression
        Core GrinAlt
    compileAConAlt np (MkAConAlt n _ [] exp) k =
        pure $ MkAlt (TagPat $ MkTag Con $ Fixed n) !(compileANF np exp k)
    compileAConAlt np (MkAConAlt n _ args exp) k = do
        args' <- traverse getAnfVar args
        pure $ MkAlt (NodePat (MkTag Con $ Fixed n) $ VVar <$> args')
             !(compileANF np exp k)

    compileAConstAlt :
        Ref NextId Int =>
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        AConstAlt ->
        (GrinVar -> Core GrinExp) -> -- rest of the grin expression
        Core GrinAlt
    compileAConstAlt np (MkAConstAlt c exp) k =
        pure $ MkAlt (getConstPat c) !(compileANF np exp k)

data GrinDefs : Type where -- top level grin defs
data Eval : Type where -- eval function alternatives
data AppDefs : Type where -- app_ function alternatives

||| App_ alternatives
record AppInfo where
    constructor MkAI
    appS : List (GrinVar -> Core GrinAlt)
    appL : List (GrinVar -> Core GrinAlt)
    appLInf : List (GrinVar -> Core GrinAlt)

addApps :
    Ref AppDefs AppInfo =>
    (GrinVar -> Core GrinAlt, GrinVar -> Core GrinAlt, GrinVar -> Core GrinAlt) ->
    Core ()
addApps (s, l, inf) = update AppDefs
    (record {appS $= (s ::), appL $= (l ::), appLInf $= (inf ::)})

||| Add a function to the various eval functions.
addFunToApp :
    Ref AppDefs AppInfo =>
    Ref NextId Int =>
    Name -> Nat -> Core ()
addFunToApp fn 0 = pure () -- can't apply a function with no arguments
addFunToApp fn arity = traverse_ addArity [1 .. arity] -- how many are missing
  where
    addArity : Nat -> Core ()
    addArity missing =
        let tag = getPartialTag missing $ Fixed fn
            tag1 = getPartialTag (missing `minus` 1) $ Fixed fn
            altS = \arg => do
                args <- replicateCore (arity `minus` missing) nextVar
                pure $ MkAlt
                    (if missing == arity then TagPat tag else NodePat tag $ VVar <$> args)
                    $ case missing of
                        1 => Simple $ App (Fixed fn) ((if arity <= missing then [] else args) ++ [arg])
                        _ => Simple $ Pure $ VTagNode tag1 (SVar <$> args ++ [arg])
            altL = \lazy, arg => do
                args <- replicateCore (arity `minus` missing) nextVar
                pure $ MkAlt
                    (if missing == arity then TagPat tag else NodePat tag $ VVar <$> args)
                    $ case missing of
                        1 => Simple $ Pure $ VTagNode (getLazyTag lazy $ Fixed fn)
                                (SVar <$> (if arity <= missing then [] else args) ++ [arg])
                        _ => Simple $ Pure $ VTagNode tag1 (SVar <$> args ++ [arg])
        in addApps (altS, altL LLazy, altL LInf)

||| Add a function to the various eval functions.
addFunToEval :
    Ref Eval (List (GrinVar -> Core GrinAlt)) =>
    Ref NextId Int =>
    Name -> Nat -> Core ()
addFunToEval fn arity =
    let evalExp : Bool -> GrinVar -> List GrinVar -> Core GrinExp
        evalExp = \linf, arg, args =>
            case linf of
                False => do
                    res <- nextVar
                    pure $ Bind (VVar res) (App (Fixed fn) args)
                            $ Bind VUnit (Update arg (VVar res))
                            $ Simple $ Pure $ VVar res
                True => pure $ Simple $ App (Fixed fn) args
        evalFn : Bool -> GrinVar -> Core GrinAlt
        evalFn = \linf, arg => do
            args <- replicateCore arity nextVar
            pure $ MkAlt (NodePat (getLazyTag (if linf then LInf else LLazy) (Fixed fn)) (VVar <$> args))
                 !(evalExp linf arg args)
    in update Eval ((evalFn False ::) . (evalFn True ::))

data PFInfo : Type where -- information about primitive/ffi functions
record PrimFnInfo where
    constructor MkPF
    externs : List External
    wrapper : List GrinDef

Semigroup PrimFnInfo where
    l <+> r = MkPF (l.externs ++ r.externs) (l.wrapper ++ r.wrapper)

compileCFFI : Ref PFInfo PrimFnInfo =>
    Name -> List CFType ->
    CFType ->
    (cFunction : String) ->
    (cLibrary : String) ->
    Core ()
compileCFFI fn args ret cfn clib = pure ()

compileFFI : Ref PFInfo PrimFnInfo =>
    Name ->
    (ccs : List String) ->
    List CFType ->
    CFType ->
    Core ()
compileFFI fn [] args ret = throw $ NoForeignCC emptyFC -- get actual FC
compileFFI fn (cc :: ccs) args ret = case parseCC cc of
    Just ("C", [cfn, clib]) => compileCFFI fn args ret cfn clib
    Just ("C", [cfn, clib, chdr]) => compileCFFI fn args ret cfn clib
    _ => compileFFI fn ccs args ret

||| compile an ANF definition.
compileANFDef :
    Ref NextId Int =>
    Ref GrinDefs (List GrinDef) =>
    Ref Eval (List (GrinVar -> Core GrinAlt)) =>
    Ref AppDefs AppInfo =>
    Ref PFInfo PrimFnInfo =>
    (Name, ANFDef) -> Core ()
compileANFDef (name, MkAFun args exp) = do
    varMapRef <- newRef VarMap empty
    pointerMapRef <- newRef PointerMap empty
    args' <- traverse (\arg => do
        arg' <- getAnfVar arg
        setVarPointer arg' True -- function arguments are always pointers
        pure arg') args
    ret <- nextVar
    def <- pure $ (MkDef
            (Fixed name)
            args'
            !(compileANF False exp \ret =>
            (pure $ Simple $ Pure $ VVar ret)))
    let arity = length args
    addFunToApp name arity
    addFunToEval name arity
    update GrinDefs (def ::)
compileANFDef (name, MkACon _ arity _) = do -- for now ignore newtype but maybe later add if grin supports it?
    let tag = MkTag Con $ Fixed name
        evalAlt : GrinVar -> Core GrinAlt
        evalAlt = \argv => case arity of
            Z => pure $ MkAlt (TagPat tag) (Simple $ Pure $ VVar $ argv)
            _ => do
                args <- replicateCore arity nextVar
                pure $ MkAlt (NodePat tag $ VVar <$> args) $ Simple $ Pure $ VVar argv
                -- if a constructor just return it no need to write it out again
    update Eval (evalAlt ::)
    pure ()
compileANFDef (name, MkAForeign ccs argTy retTy) = do -- Todo: add ffi
    compileFFI name ccs argTy retTy
compileANFDef (name, MkAError exp) = compileANFDef (name, MkAFun [] exp)

main : GrinDef
main = MkDef
            (Grin "grinMain")
            []
            $ Simple $ App (Fixed $ UN "__mainExpression.0") []

compileANFProg : List (Name, ANFDef) -> Core GrinProg
compileANFProg defs = do
    grinDefsRef <- newRef GrinDefs []
    evalRef <- newRef Eval []
    appInfo <- newRef AppDefs $ MkAI [] [] []
    nextId <- newRef NextId 0
    primFnInfo <- newRef PFInfo $ MkPF [] []
    defs <- traverse compileANFDef defs

    evalAlts <- get Eval
    evalFn <- do
        argp <- nextVar
        argv <- nextVar
        pure $ MkDef
            (Grin "eval")
            [argp]
            $ Bind (VVar $ argv) (Fetch $ argp)
            $ Case (VVar $ argv) !(traverse ($ argv) evalAlts)

    appInfo <- get AppDefs
    appDefs <- sequence -- safe to assume appInfo._ is non-empty as there is always unsafePerformIO
        [ do
            f <- nextVar
            f' <- nextVar
            arg <- nextVar
            pure $ MkDef (Grin "appS")
                [f, arg]
                $ Bind (VVar f') (eval f)
                $ Case (VVar f')
                    !(traverse ($ arg) appInfo.appS)
        , do
            f <- nextVar
            f' <- nextVar
            arg <- nextVar
            pure $ MkDef (Grin "appL")
                [f, arg]
                $ Bind (VVar f') (eval f)
                $ Case (VVar f')
                    !(traverse ($ arg) appInfo.appL)
        , do
            f <- nextVar
            f' <- nextVar
            arg <- nextVar
            pure $ MkDef (Grin "appLInf")
                [f, arg]
                $ Bind (VVar f') (eval f)
                $ Case (VVar f')
                    !(traverse ($ arg) appInfo.appLInf)
        ]

    pfi <- get PFInfo

    defs <- pure $
        ([main, evalFn] ++ pfi.wrapper ++ appDefs)
        ++ !prims ++ !(get GrinDefs)

    let prog = MkProg pfi.externs defs
    pure prog

export
anfToGrin : TransInfo Core (List (Name, ANFDef)) GrinProg
anfToGrin = MkTI compileANFProg
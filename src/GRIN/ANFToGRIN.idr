module GRIN.ANFToGRIN

import Libraries.Data.IntMap
import Data.SortedMap
import Data.SortedSet
import Data.Nat
import Data.Vect

import Core.Context.Context
import Core.Core
import Core.Name
import Core.TT

import Compiler.ANF

import GRIN.AST
import GRIN.Data
import GRIN.PrimOps

%default total

fetchAVar :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    AVar ->
    Core (SExp GName)
fetchAVar (ALocal i) = do
    avs <- get AVars
    ptrs <- get Ptrs
    case lookup i avs of
        Nothing => throw $ InternalError "Undefined AVar."
        Just v => if contains v ptrs
            then pure $ Fetch Nothing v
            else pure $ Pure $ VVar v
fetchAVar ANull = pure $ Pure nullVal

storeAVar :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    AVar ->
    Core (SExp GName)
storeAVar (ALocal i) = do
    avs <- get AVars
    ptrs <- get Ptrs
    case lookup i avs of
        Nothing => throw $ InternalError "Undefined AVar."
        Just v => if contains v ptrs
            then pure $ Pure $ VVar v
            else pure $ Store $ VVar v
storeAVar ANull = pure $ Store nullVal

newAVar :
    Ref NextVar Var =>
    Ref AVars AVarMap =>
    AVar ->
    Core Var
newAVar (ALocal av) = do
    avs <- get AVars
    case lookup av avs of
        Nothing => do
            v <- newVar
            put AVars (insert av v avs)
            pure v
        Just _ => throw $ InternalError "Already defined AVar."
newAVar ANull = throw $ InternalError "Attempt to generate a new Var for ANull."

setVarPtr :
    Ref Ptrs PtrSet =>
    Var -> Core Var
setVarPtr v = do
    update Ptrs $ insert v
    pure v

storeAVars :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    List AVar ->
    (List Var -> Core (Exp GName)) ->
    Core (Exp GName)
storeAVars [] k = k []
storeAVars (av :: avs) k = do
    v <- newVar
    pure $ Bind (VVar v) !(storeAVar av) !(storeAVars avs (k . (v ::)))

storeAVarsVect :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    Vect k AVar ->
    (Vect k Var -> Core (Exp GName)) ->
    Core (Exp GName)
storeAVarsVect [] k = k []
storeAVarsVect (av :: avs) k = do
    v <- newVar
    pure $ Bind (VVar v) !(storeAVar av) !(storeAVarsVect avs (k . (v ::)))

fetchAVarsVect :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    Vect k AVar ->
    (Vect k Var -> Core (Exp GName)) ->
    Core (Exp GName)
fetchAVarsVect [] k = k []
fetchAVarsVect (av :: avs) k = do
    v <- newVar
    pure $ Bind (VVar v) !(fetchAVar av) !(fetchAVarsVect avs (k . (v ::)))

apply : Var -> Var -> SExp GName
apply clos arg = App (GrinName Apply) [clos, arg]

appU : Var -> Var -> SExp GName
appU clos arg = App (GrinName ApplyU) [clos, arg]

appNU : Var -> Var -> SExp GName
appNU clos arg = App (GrinName ApplyNU) [clos, arg]

appLazy : LazyReason -> Var -> Var -> SExp GName
appLazy LInf = appU
appLazy _ = appNU

mkLazyThunk : forall name . LazyReason -> name -> List SVal -> Val name
mkLazyThunk LInf = mkNUThunk
mkLazyThunk _ = mkUThunk

anfToExp :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    ANF ->
    Core (Exp GName)

anfConAlts :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    List AConAlt ->
    Maybe ANF ->
    Core (List (Alt GName))

anfConstAlts :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    List AConstAlt ->
    Maybe ANF ->
    Core (List (Alt GName))

anfToExp (AV _ v) = mkSimpleExp <$> fetchAVar v

anfToExp (AAppName _ Nothing fn args) =
    storeAVars args $ \vs => pure $ mkSimpleExp
        $ App (IdrName fn) vs
anfToExp (AAppName _ (Just LInf) fn args) =
    storeAVars args $ \vs => pure $ mkSimpleExp
        $ Pure $ mkNUThunk (IdrName fn) (SVar <$> vs)
anfToExp (AAppName _ (Just _) fn args) =
    storeAVars args $ \vs => pure $ mkSimpleExp
        $ Pure $ mkNUThunk (IdrName fn) (SVar <$> vs)

anfToExp (AUnderApp _ fn m args) =
    storeAVars args $ \vs => pure $ mkSimpleExp
        $ Pure $ mkPartial (IdrName fn) m (SVar <$> vs)

anfToExp (AApp _ Nothing fn arg) =
    storeAVarsVect [fn, arg] $ \[fnv, argv] => pure $ mkSimpleExp $ apply fnv argv
anfToExp (AApp _ (Just lazy) fn arg) =
    storeAVarsVect [fn, arg] $ \[fnv, argv] => pure $ mkSimpleExp $ appLazy lazy fnv argv

anfToExp (ALet _ av rhs rest) = do
    v <- newAVar (ALocal av)
    pure $ Bind (VVar v) (mkDo !(anfToExp rhs)) !(anfToExp rest)

anfToExp (ACon _ con _ _ args) =
    storeAVars args $ \vs => pure $ mkSimpleExp
        $ Pure $ mkCon (IdrName con) (SVar <$> vs)

anfToExp (AOp _ Nothing BelieveMe [from, to, arg]) = do
    v <- newVar
    storeAVarsVect [arg] $ \[var] => pure
        $ Bind (VVar v) (App (PrimName BelieveMe) [var])
        $ SimpleExp $ fetch v

anfToExp (AOp _ Nothing op args) =
    storeAVarsVect args $ \vs => pure $ mkSimpleExp
        $ App (PrimName op) (toList vs)
anfToExp (AOp _ (Just lazy) op args) =
    storeAVarsVect args $ \vs => pure $ mkSimpleExp
        $ Pure $ mkLazyThunk lazy (PrimName op) (SVar <$> toList vs)

anfToExp (AExtPrim fc lazy fn args) = throw $ InternalError "%extern not yet implemented"

anfToExp (AConCase _ av alts def) = do
    vp <- newVar
    v <- newVar
    pure $ Bind (VVar vp) !(storeAVar av)
         $ Bind (VVar v) (App (GrinName Eval) [vp])
         $ Case (VVar v) !(anfConAlts alts def)

anfToExp (AConstCase _ av alts@(MkAConstAlt c _ :: _) def) = do
    vp <- newVar
    v <- newVar
    pure $ Bind (VVar vp) !(storeAVar av)
         $ Bind (unwrapConstant v c) (App (GrinName Eval) [vp])
         $ Case (VVar v) !(anfConstAlts alts def)

anfToExp (AConstCase _ av alts def) = do
    vp <- newVar
    v <- newVar
    pure $ Bind (VVar vp) !(storeAVar av)
         $ Bind (VVar v) (App (GrinName Eval) [vp])
         $ Case (VVar v) !(anfConstAlts alts def)

anfToExp (APrimVal _ (BI x)) = do
    v <- newVar
    pure $ Bind (VVar v) (Pure $ VLit $ LString $ show x)
         $ SimpleExp (App (PrimFunc $ Cast StringType IntegerType) [v])
anfToExp (APrimVal _ c) = pure $ mkSimpleExp $ Pure $ anfConstant c

anfToExp (AErased _) = pure $ mkSimpleExp $ Pure nullVal

anfToExp (ACrash _ msg) = do
    v <- newVar
    pure $ Bind (VVar v) (Pure $ VLit $ LString msg)
         $ SimpleExp $ App (GrinName Crash) [v]

anfConAlt :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    AConAlt ->
    Core (Alt GName)
anfConAlt (MkAConAlt con _ _ avs exp) = do
    as <- traverse (newAVar . ALocal >=> setVarPtr) avs
    MkAlt (NodePat (MkTag Con $ IdrName con) as) <$> anfToExp exp

anfConAlts (alt :: alts) def = [| anfConAlt alt :: anfConAlts alts def |]
anfConAlts [] (Just exp) = pure . MkAlt DefaultPat <$> anfToExp exp
anfConAlts [] Nothing = pure []

anfConstAlt :
    Ref AVars AVarMap =>
    Ref Ptrs PtrSet =>
    Ref NextVar Var =>
    AConstAlt ->
    Core (Alt GName)
anfConstAlt (MkAConstAlt lit exp) =
    pure $ MkAlt (getConstantLitPat lit) !(anfToExp exp)

anfConstAlts (alt :: alts) def = [| anfConstAlt alt :: anfConstAlts alts def |]
anfConstAlts [] (Just exp) = pure . MkAlt DefaultPat <$> anfToExp exp
anfConstAlts [] Nothing = pure []

record BProg where
    constructor MkBProg
    eval : Var -> Core (List (Alt GName))
    apply : Var -> List (Alt GName)
    applyU : Var -> List (Alt GName)
    applyNU : Var -> List (Alt GName)
    defs : List (Def GName)
    externs : List (Extern GName)

initBProg : Ref NextVar Var => Core BProg
initBProg = pure $ MkBProg primCons go go go !primOps externs
  where
    go : _ -> List a
    go _ = []

addEvalAlt :
    Ref Build BProg =>
    (Var -> Core (Alt GName)) ->
    Core ()
addEvalAlt alt = update Build $ record { eval $= \ev, ptr => (::) <$> alt ptr `Core.(<*>)` ev ptr }

addEvalAlts :
    Ref Build BProg =>
    (Var -> Core (List (Alt GName))) ->
    Core ()
addEvalAlts alts = update Build $ record { eval $= \ev, ptr => (++) <$> alts ptr `Core.(<*>)` ev ptr }

addApplyAlt :
    Ref Build BProg =>
    ((arg : Var) -> Alt GName) ->
    Core ()
addApplyAlt alt = update Build $ record { apply $= \app, arg => alt arg :: app arg }

addApplyUAlt :
    Ref Build BProg =>
    ((arg : Var) -> Alt GName) ->
    Core ()
addApplyUAlt alt = update Build $ record { applyU $= \app, arg => alt arg :: app arg }

addApplyNUAlt :
    Ref Build BProg =>
    ((arg : Var) -> Alt GName) ->
    Core ()
addApplyNUAlt alt = update Build $ record { applyNU $= \app, arg => alt arg :: app arg }

addDef :
    Ref Build BProg =>
    Def GName ->
    Core ()
addDef def = update Build $ record { defs $= (def ::) }

addExtern :
    Ref Build BProg =>
    Extern GName ->
    Core ()
addExtern ext = update Build $ record { externs $= (ext ::) }

addFnEval :
    Ref NextVar Var =>
    Ref Build BProg =>
    GName -> Nat -> Core ()
addFnEval fn arity = do
    let uAlt = \ptr => do
            vs <- replicate arity newVar 
            res <- newVar
            pure $ MkAlt (NodePat (MkTag UThunk fn) vs)
                 $ Bind (VVar res) (App fn vs)
                 $ Bind VUnit (Update ptr (VVar res))
                 $ SimpleExp $ Pure (VVar res)
    addEvalAlt uAlt
    let nuAlt = \_ => do
            vs <- replicate arity newVar
            pure $ MkAlt (NodePat (MkTag NUThunk fn) vs)
                 $ SimpleExp $ App fn vs
    addEvalAlt nuAlt
    let S ar = arity
        | Z => pure ()
    let pAlts = \_ =>
            traverse addMissing [(ar + 1) .. 1]
    addEvalAlts pAlts
  where
    addMissing : Nat -> Core (Alt GName)
    addMissing missing = do
        vs <- replicate (arity `minus` missing) newVar
        let tag = MkTag (Partial missing) fn
        pure $ MkAlt (NodePat tag vs)
             $ SimpleExp $ Pure $ ConstTagNode tag (SVar <$> vs)

addFnApply :
    Ref NextVar Var =>
    Ref Build BProg =>
    GName -> Nat -> Nat -> Core ()
addFnApply fn _ 0 = pure ()
addFnApply fn ar 1 = do
    vs <- replicate (ar `minus` 1) newVar
    let alt = \arg =>
            MkAlt (NodePat (MkTag (Partial 1) fn) vs)
                $ SimpleExp $ App fn (vs ++ [arg])
    addApplyAlt alt
    vs <- replicate (ar `minus` 1) newVar
    let altU = \arg =>
            MkAlt (NodePat (MkTag (Partial 1) fn) vs)
                $ SimpleExp $ Pure
                    $ ConstTagNode (MkTag UThunk fn) (SVar <$> vs ++ [arg])
    addApplyUAlt altU
    vs <- replicate (ar `minus` 1) newVar
    let altNU = \arg =>
            MkAlt (NodePat (MkTag (Partial 1) fn) vs)
                $ SimpleExp $ Pure
                    $ ConstTagNode (MkTag NUThunk fn) (SVar <$> vs ++ [arg])
    addApplyNUAlt altNU

addFnApply fn ar mis = do
    vs <- replicate (ar `minus` mis) newVar
    let alt = \arg =>
            MkAlt (NodePat (MkTag (Partial mis) fn) vs)
                $ SimpleExp $ Pure
                    $ ConstTagNode (MkTag (Partial $ pred mis) fn) (SVar <$> vs ++ [arg])
    addApplyAlt alt
    vs <- replicate (ar `minus` mis) newVar
    let altU = \arg =>
            MkAlt (NodePat (MkTag (Partial mis) fn) vs)
                $ SimpleExp $ Pure
                    $ ConstTagNode (MkTag (Partial $ pred mis) fn) (SVar <$> vs ++ [arg])
    addApplyUAlt altU
    vs <- replicate (ar `minus` mis) newVar
    let altNU = \arg =>
            MkAlt (NodePat (MkTag (Partial mis) fn) vs)
                $ SimpleExp $ Pure
                    $ ConstTagNode (MkTag (Partial $ pred mis) fn) (SVar <$> vs ++ [arg])
    addApplyNUAlt altNU
    assert_total $ addFnApply fn ar (pred mis)

anfDef :
    Ref NextVar Var =>
    Ref Build BProg =>
    Name -> ANFDef ->
    Core ()

anfDef fn (MkAFun avs exp) = do
    avars <- newRef AVars empty
    ptrs <- newRef Ptrs empty
    vs <- traverse ((newAVar . ALocal) >=> setVarPtr) avs
    addFnEval (IdrName fn) (length avs)
    addFnApply (IdrName fn) (length avs) (length avs)
    addDef !(mkDef (IdrName fn) vs <$> anfToExp exp)

anfDef con (MkACon _ ar _) =
    addEvalAlt $ \_ => do
        vs <- replicate ar newVar
        let tag = (MkTag Con (IdrName con))
        pure $ MkAlt (NodePat tag vs) (mkSimpleExp $ Pure $ ConstTagNode tag (SVar <$> vs))

anfDef fn (MkAForeign ccs args ret) = do
    let Just (primFn, lib) = getCC ccs
        | Nothing => throw $ InternalError $ "No supported calling conventions."
    let Right type = getFFIType args ret
        | Left err => throw $ InternalError $ "Unsupported ffi type " ++ err ++ "."
    let prim = FFI
    let eff = isEff ret
    let libs = makeLibs lib
    addExtern $ MkExtern { extName = FFIName primFn, type, prim, eff, libs }
    wrap <- mkFFIWrapper (IdrName fn) args ret (FFIName primFn)
    addDef wrap
  where
    getSO : OS -> String
    getSO Darwin = "dylib"
    getSO FreeBSD = "so"
    getSO Linux = "so"
    getSO Android = "so"
    getSO MinGW = "dll"
    getSO Win = "dll"
    getSO NetBSD = "so"
    getSO OpenBSD = "so"

    makeLibs : Maybe String -> List (OS, String) -- TODO: check if portable directive is enabled
    makeLibs Nothing = []
    makeLibs (Just "libc") = [(Linux, "libc.so.6")] -- TODO: other OSs
    makeLibs (Just lib) = map (\os => (os, "\{lib}.\{getSO os}")) [Darwin, FreeBSD, Linux, Android, MinGW, Win, NetBSD, OpenBSD]

anfDef fn e@(MkAError exp) = anfDef fn (assert_smaller e $ MkAFun [] exp)

mkEvalFn :
    Ref NextVar Var =>
    (Var -> Core (List (Alt GName))) ->
    Core (Def GName)
mkEvalFn k = do
    ptr <- newVar
    val <- newVar
    alts <- k ptr
    pure $ mkDef (GrinName Eval) [ptr]
         $ Bind (VVar val) (fetch ptr)
         $ Case (VVar val) alts

mkApplyFn :
    Ref NextVar Var =>
    GrinFn ->
    ((arg : Var) -> List (Alt GName)) ->
    Core (Def GName)
mkApplyFn fn k = do
    fnPtr <- newVar
    fnVal <- newVar
    arg <- newVar
    let alts = k arg
    pure $ mkDef (GrinName fn) [fnPtr, arg]
         $ Bind (VVar fnVal) (App (GrinName Eval) [fnPtr])
         $ Case (VVar fnVal) alts

export
compileANF : List (Name, ANFDef) -> Core (Prog GName)
compileANF defs = do
    var <- newRef NextVar (MkVar 0)
    build <- newRef Build !initBProg
    traverse_ (uncurry anfDef) defs

    MkBProg eval apply applyU applyNU defs externs <- get Build

    evalFn <- mkEvalFn eval
    applyFn <- mkApplyFn Apply apply
    applyUFn <- mkApplyFn ApplyU applyU
    applyNUFn <- mkApplyFn ApplyNU applyNU
    
    let main =
        mkDef
            (GrinName Main)
            []
            $ mkSimpleExp
                $ App (IdrName $ MN "__mainExpression" 0) []

    pure $ mkProg externs (main :: evalFn :: applyFn :: applyUFn :: applyNUFn :: defs) (GrinName Main)

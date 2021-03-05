module GRIN.GRIN

import Data.Vect
import Data.SortedMap
import Data.SortedSet
import Data.Maybe

import Core.Core
import Core.TT

import Compiler.ANF
import Compiler.Common

import GRIN.Syntax

||| Next variable
data NextId : Type where

nextId : Ref NextId Int => Core Int
nextId = do
    i <- get NextId
    put NextId (i + 1)
    pure i

||| Whether each variable is a pointer or value.
data VarMap : Type where

||| Check if a variable is a pointer.
||| Defaults to is a pointer.
varIsPointer : Ref VarMap (SortedMap GrinVar Bool) => GrinVar -> Core Bool
varIsPointer var = pure $ fromMaybe False $ lookup var !(get VarMap)

||| Set if a variable is a pointer.
||| Overwriting is allowed.
setVarPointer :
    Ref VarMap (SortedMap GrinVar Bool) =>
    GrinVar -> (isPointer : Bool) -> Core ()
setVarPointer var isPointer = update VarMap $ insert var isPointer

primTag : String -> Tag
primTag = MkTag Con . UN

primTagNode : String -> GrinLit -> Val
primTagNode n val = VTagNode (MkTag Con $ UN n) [SLit val]

primTagVal : String -> Val
primTagVal = VTag . MkTag Con . UN

||| Convert constant to a GRIN value.
mkConstTag : Constant -> Val
mkConstTag = \case
    I i => primTagNode "Integer" $ LInt i
    BI i => primTagNode "Natural" $ LInt $ cast i
    B8 i => primTagNode "Bits8" $ LBits64 $ cast i
    B16 i => primTagNode "Bits16" $ LBits64 $ cast i
    B32 i => primTagNode "Bits32" $ LBits64 $ cast i
    B64 i => primTagNode "Bits64" $ LBits64 $ cast i
    Str s => primTagNode "String" $ LString s
    Ch c => primTagNode "Char" $ LChar c
    Db d => primTagNode "Double" $ LDouble d
    WorldVal => primTagVal "World"
    IntType => primTagVal "IntType"
    IntegerType => primTagVal "IntegerType"
    Bits8Type => primTagVal "Bits8Type"
    Bits16Type => primTagVal "Bits16Type"
    Bits32Type => primTagVal "Bits32Type"
    Bits64Type => primTagVal "Bits64Type"
    StringType => primTagVal "StringType"
    CharType => primTagVal "CharType"
    DoubleType => primTagVal "DoubleType"
    WorldType => primTagVal "WorldType"

||| Returns constructor for lazy version of a function.
getLazyTag : LazyReason -> Name -> Tag
getLazyTag LInf n = MkTag InfThunk n
getLazyTag _ n = MkTag Thunk n

||| Returns constructor for partial function application.
getPartialTag : (missing : Nat) -> Name -> Tag
getPartialTag = MkTag . Missing

||| Return app function with correct laziness.
getAppVar : Maybe LazyReason -> GrinVar
getAppVar Nothing = Grin "appS"
getAppVar (Just LInf) = Grin "appInf"
getAppVar (Just _) = Grin "appL"

||| Convert a `GrinExp` into something suitable as the rhs
||| of a `<-` binding.
mkBound : GrinExp -> SimpleExp
mkBound (Simple (Pure exp)) = Store exp
mkBound (Simple exp) = exp
mkBound exp = Do exp

erased : Tag
erased = MkTag Con $ UN "Erased"

eval : {auto 1 expTy : Either (exp = SimpleExp) (exp = GrinExp)} -> GrinVar -> exp
eval {expTy = Left prf} var = rewrite prf in App (Grin "eval") [var]
eval {expTy = Right prf} var = rewrite prf in Simple $ App (Grin "eval") [var]

fetchAndEval :
    Ref NextId Int =>
    Ref VarMap (SortedMap GrinVar Bool) =>
    AVar -> (k : GrinVar -> Core GrinExp) ->
    Core GrinExp
fetchAndEval ANull k = do
    i <- nextId
    pure $ Bind (VVar $ Var i) (Pure $ VTag erased)
         $ !(k $ Var i)
fetchAndEval (ALocal i) k = do
    i' <- nextId
    isPointer <- varIsPointer $ Anf i
    if isPointer
        then do
            i'' <- nextId
            pure $ Bind (VVar $ Var i') (Fetch $ Anf i)
                 $ Bind (VVar $ Var i'') (eval (Var i'))
                 !(k $ Var i')
        else pure $ Bind (VVar $ Var i') (eval (Anf i))
                  !(k $ Var i')

fetches : List AVar -> (List GrinVar -> Core exp) -> Core exp

unwrapLit : AConstAlt -> GrinVar -> Val
unwrapLit (MkAConstAlt c _) v = case c of
    I _ => VTagNode (primTag "Int") [SVar v]
    BI _ => VTagNode (primTag "Integer") [SVar v]
    B8 _ => VTagNode (primTag "Bits8") [SVar v]
    B16 _ => VTagNode (primTag "Bits16") [SVar v]
    B32 _ => VTagNode (primTag "Bits32") [SVar v]
    B64 _ => VTagNode (primTag "Bits64") [SVar v]
    Str _ => VTagNode (primTag "String") [SVar v]
    Ch _ => VTagNode (primTag "Char") [SVar v]
    Db _ => VTagNode (primTag "Double") [SVar v]
    WorldVal => VVar v
    IntType => VVar v
    IntegerType => VVar v
    Bits8Type => VVar v
    Bits16Type => VVar v
    Bits32Type => VVar v
    Bits64Type => VVar v
    StringType => VVar v
    CharType => VVar v
    DoubleType => VVar v
    WorldType => VVar v

compileAOp : Maybe LazyReason -> PrimFn arity -> Vect arity AVar -> Core GrinExp

compileExtPrim : Maybe LazyReason -> Name -> List AVar -> Core GrinExp

mkPointer : {auto p : Either (exp = SimpleExp) (exp = GrinExp)} -> (needPointer : Bool) -> Val -> exp
mkPointer {p = Left prf} False = rewrite prf in Pure
mkPointer {p = Left prf} True = rewrite prf in Store
mkPointer {p = Right prf} np = rewrite prf in Simple . mkPointer {p = Left Refl} np

fromToPointer : {auto p : Either (exp = SimpleExp) (exp = GrinExp)} -> (fromPointer : Bool) -> (needPointer : Bool) -> GrinVar -> exp
fromToPointer {p = Left prf} False False = rewrite prf in Pure . VVar
fromToPointer {p = Left prf} False True = rewrite prf in Store . VVar
fromToPointer {p = Left prf} True False = rewrite prf in Fetch
fromToPointer {p = Left prf} True True = rewrite prf in Pure . VVar
fromToPointer {p = Right prf} fp np = rewrite prf in Simple . fromToPointer {p = Left Refl} fp np

mutual
    ||| Compile an ANF expression.
    ||| Takes a list of variables that are function arguments
    compileANF :
        Ref NextId Int =>
        Ref VarMap (SortedMap GrinVar Bool) =>
        (needPointer : Bool) ->
        ANF -> (GrinVar -> Core GrinExp) -> Core GrinExp
    compileANF np (AV _ ANull) k = do
        i <- Var <$> nextId
        setVarPointer i np
        pure $ Bind (VVar i) (mkPointer np $ VTag erased)
             !(k i)
    compileANF np (AV _ (ALocal i)) k = do
        i' <- Var <$> nextId
        setVarPointer i' np
        iIsPointer <- varIsPointer $ Anf i
        pure $ Bind (VVar i') (fromToPointer iIsPointer np i')
             !(k i')
    compileANF np (AAppName _ Nothing n args) k = do
        i' <- Var <$> nextId
        i'' <- Var <$> nextId
        setVarPointer i' False -- functions should never return pointers I think
        setVarPointer i'' np
        fetches args \args' =>
            pure $ Bind (VVar i') (App (Fixed n) args')
                 $ Bind (VVar i'') (mkPointer np $ VVar i') -- GRIN will optimise this
                 !(k i'')


    compileAConAlt : Ref VarMap (SortedMap GrinVar Bool) => AConAlt -> Core GrinAlt

    compileAConstAlt : Ref VarMap (SortedMap GrinVar Bool) => AConstAlt -> Core GrinAlt
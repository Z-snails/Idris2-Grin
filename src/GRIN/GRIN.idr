module GRIN.GRIN

import Data.Vect
import Data.SortedSet
import Data.Maybe
import Data.List

import Libraries.Data.IntMap

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

nextVar : Ref NextId Int => Core GrinVar
nextVar = nextVar

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

erasedT : Tag
erasedT = MkTag Con $ UN "Erased"

eval : {auto 1 expTy : Either (exp = SimpleExp) (exp = GrinExp)} -> GrinVar -> exp
eval {expTy = Left prf} var = rewrite prf in App (Grin "eval") [var]
eval {expTy = Right prf} var = rewrite prf in Simple $ App (Grin "eval") [var]

fetchAndEval :
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    AVar -> (k : GrinVar -> Core GrinExp) ->
    Core GrinExp
fetchAndEval ANull k = do
    i <- nextId
    pure $ Bind (VVar $ Var i) (Pure $ VTag erasedT)
         $ !(k $ Var i)
fetchAndEval (ALocal ai) k = do
    i <- getAnfVar ai
    i' <- nextVar

    isPointer <- varIsPointer i'
    if isPointer
        then do
            i'' <- nextVar
            pure $ Bind (VVar i') (Fetch i)
                 $ Bind (VVar i'') (eval i')
                 !(k i'')
        else pure $ Bind (VVar i') (eval i)
                  !(k i')

||| Globally defined erased value.
-- is this faster than constantly storing and fetching?
-- or does it mean more cache invalidation because it is far away?
erasedV : GrinVar
erasedV = Grin "erasedV" -- `pure CErasedV`

||| Globally defined pointer to erased value.
erasedP : GrinVar
erasedP = Grin "erasedP" -- `fetch CErased`

fetches :
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    List AVar ->
    (List GrinVar -> Core GrinExp) ->
    Core GrinExp
fetches args k = k !(traverse go args)
  where
    go : AVar -> Core GrinVar
    go ANull = pure $ erasedP
    go (ALocal i) = getAnfVar i



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

compilePrimFn : 
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    (needPointer : Bool) -> -- whether a pointer is required
    (ret : Val) -> -- value to bind result to
    Maybe LazyReason ->
    PrimFn arity ->
    Vect arity AVar ->
    Core GrinExp -> -- rest of the grin expression
    Core GrinExp

compileExtPrim : 
    Ref NextId Int =>
    Ref VarMap (IntMap GrinVar) =>
    Ref PointerMap (SortedSet GrinVar) =>
    (needPointer : Bool) -> -- whether a pointer is required
    (ret : Val) -> -- value to bind result to
    Maybe LazyReason ->
    Name ->
    List AVar ->
    Core GrinExp -> -- rest of the grin expression
    Core GrinExp

||| Unwrap a literal
unwrapPrim :
    GrinVar ->
    AConstAlt ->
    Val

||| Wrap a literal
wrapPrim :
    Constant ->
    Val

mutual
    ||| Compile an ANF expression.
    ||| Takes a continuation of what to do with the result. 
    compileANF :
        Ref NextId Int =>
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        (ret : Val) -> -- value to bind result to
        ANF -> -- ANF expression to compile
        Core GrinExp -> -- rest of the grin expression
        Core GrinExp
    compileANF np ret (AV _ ANull) k = do
        pure $ Bind ret (if np then Pure $ VVar erasedP else Pure $ VVar erasedV) -- for now this is just a tag
             !k                                      -- but I'd like it to be removed entirely
    compileANF np ret (AV _ (ALocal ai)) k = do
        i <- getAnfVar ai -- get the GRIN variable
        pure $ Bind ret (fromToPointer !(varIsPointer i) np i)
             !k
    compileANF np ret (AAppName _ Nothing n args) k = do
        i <- nextVar -- result of function
        fetches args \args' =>
            pure $ Bind (VVar i) (App (Fixed n) args')
                 $ Bind ret (mkPointer np $ VVar i) -- GRIN will optimise this if pure
                 !k
    compileANF np ret (AAppName _ (Just lazy) n args) k = do
        fetches args \args' =>
            pure $ Bind ret (mkPointer np $ VTagNode (getLazyTag lazy n) (SVar <$> args'))
                 !k
    compileANF np ret (AUnderApp _ n missing args) k = do
        fetches args \args' =>
            pure $ Bind ret (mkPointer np $ VTagNode (getPartialTag missing n) (SVar <$> args'))
                 !k
    compileANF np ret (AApp _ lazy af aarg) k = do
        let ALocal af' = af
            | ANull => assert_total $ idris_crash "Internal Error: Erased argument can't be called as a function"
        f <- getAnfVar af'
        case aarg of
            ALocal iarg => do
                arg <- getAnfVar iarg
                pure $ Bind ret (App (getAppVar lazy) [f, arg])
                     !k
            ANull => do
                arg <- nextVar
                setVarPointer arg True -- function arguments are pointers
                pure $ Bind (VVar arg) (Pure $ VVar erasedP)
                     $ Bind ret (App (getAppVar lazy) [f, arg])
                     !k
    compileANF np ret (ALet _ anf rhs rest) k = do
        res <- getAnfVar anf
        compileANF False (VVar res) rhs
            $ compileANF np ret rest k
    compileANF np ret (ACon _ n _ []) k = -- Constructors are always fully applied
        pure $ Bind ret (mkPointer np $ VTag $ MkTag Con n)
             !k
    compileANF np ret (ACon _ n _ args) k =
        fetches args \args' =>
            pure $ Bind ret (mkPointer np $ VTagNode (MkTag Con n) $ SVar <$> args')
                 !k
    compileANF np ret (AOp _ lazy op args) k = compilePrimFn np ret lazy op args k
    compileANF np ret (AExtPrim _ lazy op args) k = compileExtPrim np ret lazy op args k
    compileANF _ _ (AConCase _ ANull _ _) _ = assert_total $ idris_crash "Internal Error: Attempt to match on erased in ANF"
    compileANF np ret (AConCase _ (ALocal var) alts def) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        evaled <- nextVar
        pure $ Bind (VVar fetched) (fromToPointer !(varIsPointer var') True var') -- make pointer before passing to eval
             $ Bind (VVar evaled) (eval fetched)
             $ Case (VVar evaled)
                !(case def of
                    Nothing => (traverse (\alt => compileAConAlt np ret alt k) alts)
                    Just exp =>
                        [| traverse (\alt => compileAConAlt np ret alt k) alts
                        ++ pure [MkAlt Default !(compileANF np ret exp k)] |]
                )
    compileANF _ _ (AConstCase _ ANull _ _) _ = assert_total $ idris_crash "Internal Error: Attempt to match on erased in ANF"
    compileANF np ret (AConstCase _ (ALocal var) alts@(alt :: _) def) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        evaledUnwrapped <- nextVar
        pure $ Bind (VVar fetched) (fromToPointer !(varIsPointer var') True var') -- make pointer before passing to eval
             $ Bind (unwrapPrim evaledUnwrapped alt) (eval fetched) -- unwrap primitive before passing to case
             $ Case (VVar evaledUnwrapped)
                !(case def of
                    Nothing => (traverse (\alt => compileAConstAlt np ret alt k) alts)
                    Just exp =>
                        [| traverse (\alt => compileAConstAlt np ret alt k) alts
                        ++ pure [MkAlt Default !(compileANF np ret exp k)] |]
                )
    compileANF np ret (AConstCase _ (ALocal var) [] (Just exp)) k = do
        var' <- getAnfVar var
        fetched <- nextVar
        pure $ Bind (VVar fetched) (fromToPointer !(varIsPointer var') True var') -- make pointer before passing to eval
             $ Bind VIgnore (eval fetched) -- evaluate to ensure correct laziness semantics (I think)
             !(compileANF np ret exp k)
    compileANF _ _ (AConstCase _ _ [] Nothing) _ = assert_total $ idris_crash "Internal Error: Empty case block"
    compileANF np ret (APrimVal _ val) k =
        pure $ Bind ret (mkPointer np $ wrapPrim val)
             !k
    compileANF np ret (AErased _) k =
        pure $ Bind ret (if np then Pure $ VVar erasedP else Pure $ VVar erasedV)
             !k
    compileANF np ret (ACrash _ msg) _ = do
        msg' <- nextVar
        pure $ Bind (VVar msg') (Pure $ VLit $ LString msg) -- don't bother wrapping in a string
             $ Simple $ App (Grin "_idris_crash") [msg']

    compileAConAlt :
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        (ret : Val) -> -- value to bind result to
        AConAlt ->
        Core GrinExp -> -- rest of the grin expression
        Core GrinAlt

    compileAConstAlt :
        Ref VarMap (IntMap GrinVar) =>
        Ref PointerMap (SortedSet GrinVar) =>
        (needPointer : Bool) -> -- whether a pointer is required
        (ret : Val) -> -- value to bind result to
        AConstAlt ->
        Core GrinExp -> -- rest of the grin expression
        Core GrinAlt
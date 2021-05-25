module GRIN.Var

import Control.Monad.State
import Data.SortedMap

import GRIN.GrinM
import GRIN.AST

public export
interface Monad m => MonadVar m where
    putVars : SortedMap Var Var -> m ()
    getVars : m (SortedMap Var Var)
    updateVar : Var -> m Var

export
resetVars : MonadVar m => m ()
resetVars = putVars empty

public export
record VarState where
    constructor MkVS
    varMap : SortedMap Var Var
    nextVar : Var

public export
VarM : Type -> Type
VarM = State VarState

export
MonadVar VarM where
    putVars vm = modify $ record { varMap = vm }
    getVars = gets varMap
    updateVar v = do
        vm <- gets varMap
        case lookup v vm of
            Just v' => pure v'
            Nothing => do
                v' <- gets nextVar
                modify $ record { varMap $= insert v v', nextVar $= incVar }
                pure v'

export
Monad m => MonadVar (GrinT name m) where
    putVars vm = modify $ record { varMap = vm }
    getVars = gets varMap
    updateVar v = do
        vm <- gets varMap
        case lookup v vm of
            Just v' => pure v'
            Nothing => do
                v' <- gets nextVar
                modify $ record { varMap $= insert v v', nextVar $= incVar }
                pure v'
      where
        newVar : GrinT name m Var
        newVar = do
            v <- gets nextVar
            modify $ record { nextVar $= incVar }
            pure v

||| Interface for types that contains `Var`s.
public export
interface HasVars a where
    updateVars : MonadVar m => a -> m a

export
HasVars Var where
    updateVars = updateVar

export
HasVars SVal where
    updateVars (SVar v) = SVar <$> updateVar v
    updateVars v = pure v

export
HasVars (Val name) where
    updateVars (SimpleVal v) = SimpleVal <$> updateVars v
    updateVars (ConstTagNode tag vs) = ConstTagNode tag <$> traverse updateVars vs
    updateVars (ConstTag tag) = pure $ ConstTag tag
    updateVars (VarTagNode v vs) = VarTagNode <$> updateVar v <*> traverse updateVars vs
    updateVars VUnit = pure VUnit

export
HasVars (CasePat name) where
    updateVars (NodePat tag vs) = NodePat tag <$> traverse updateVar vs
    updateVars (TagPat tag) = pure $ TagPat tag
    updateVars (LitPat l) = pure $ LitPat l
    updateVars DefaultPat = pure DefaultPat 

mutual
    export
    HasVars (SExp name) where
        updateVars (Do e) = mkDo <$> updateVars e
        updateVars (App fn vs) = App fn <$> traverse updateVars vs
        updateVars (Pure v) = Pure <$> updateVars v
        updateVars (Store v) = Store <$> updateVars v
        updateVars (Fetch i v) = Fetch i <$> updateVar v
        updateVars (FetchI i idx v) = FetchI i idx <$> updateVar v
        updateVars (Update var val) = Update <$> updateVar var <*> updateVars val

    export
    HasVars (Exp name) where
        updateVars (SimpleExp e) = mkSimpleExp <$> updateVars e
        updateVars (Bind val rhs rest) = Bind <$> updateVars val <*> updateVars rhs <*> updateVars rest
        updateVars (Case val alts) = Case <$> updateVars val <*> traverse updateVars alts
    
    export
    HasVars (Alt name) where
        updateVars (MkAlt pat e) = MkAlt <$> updateVars pat <*> updateVars e

export
HasVars (Def name) where
    updateVars (MkDef fn vs e ty) =
        MkDef
            fn
            <$> traverse updateVar vs
            <*> updateVars e
            <*> pure ty

export
HasVars (Prog name) where
    updateVars (MkProg es ds m) = MkProg es <$> traverse updateVars ds <*> pure m

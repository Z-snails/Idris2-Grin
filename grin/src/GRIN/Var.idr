module GRIN.Var

import Control.Monad.State
import Data.SortedMap

import GRIN.GrinM
import GRIN.AST

||| Generate a new variable.
export
newVar : Monad m => GrinT name m Var
newVar = do
    v <- gets nextVar
    modify $ record { nextVar $= incVar }
    pure v

||| Generate a new variable for an old variable.
export
updateVar : Monad m => Var -> GrinT name m Var
updateVar v = do
    vm <- gets varMap
    case lookup v vm of
        Just v' => pure v'
        Nothing => do
            v' <- gets nextVar
            modify $ record { varMap $= insert v v', nextVar $= incVar }
            pure v'

||| Interface for types that contains `Var`s.
interface HasVars a where
    updateVars : Monad m => a -> GrinT name m a

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
        updateVars (Do e) = updateVars e
        updateVars (App fn vs) = App fn <$> traverse updateVars vs
        updateVars (Pure v) = Pure <$> updateVars v

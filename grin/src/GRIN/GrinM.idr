module GRIN.GrinM

import Data.SortedMap
import Data.SortedSet

import public Control.Monad.State
import public Control.Monad.Identity

import GRIN.AST
import public GRIN.Analysis
import GRIN.Analysis.CallGraph

export
record GrinT name (m : Type -> Type) a where
    constructor MkGrinM
    unGrinM : StateT (Analysis name) m a

public export
GrinM : Type -> Type -> Type
GrinM name a = GrinT name Identity a

export
Functor m => Functor (GrinT name m) where
    map f = MkGrinM . map f . unGrinM

export
Monad m => Applicative (GrinT name m) where
    pure = MkGrinM . pure
    f <*> x = MkGrinM $ unGrinM f <*> unGrinM x

export
Monad m => Monad (GrinT name m) where
    x >>= f = MkGrinM $ unGrinM x >>= unGrinM . f

export
MonadTrans (GrinT name) where
    lift = MkGrinM . lift

export
Monad m => MonadState (Analysis name) (GrinT name m) where
    get = MkGrinM get
    put = MkGrinM . put
    state = MkGrinM . state

export
mapProg : Monad m => (Prog name -> Prog name) -> GrinT name m ()
mapProg f = modify $ record { prog $= f }

export
putProg : Monad m => Prog name -> GrinT name m ()
putProg p = modify $ record { prog = p }

export
invalidate : Monad m => AnalysisTag -> GrinT name m ()
invalidate t = modify $ case t of
    CallsGraph => record { calls = Nothing }
    CalledByGraph => record { calledBy = Nothing }
    CallGraphs => record { calls = Nothing, calledBy = Nothing }

export
getCalls : Monad m => Ord name => GrinT name m (CallGraph name)
getCalls = do
    Nothing <- gets calls
        | Just cg => pure cg
    p <- gets prog
    let cg = callsGraph p
    modify $ record { calls = Just cg }
    pure cg

export
getCalledBy : Monad m => Ord name => GrinT name m (CallGraph name)
getCalledBy = do
    Nothing <- gets calledBy
        | Just cg => pure cg
    calls <- getCalls
    let cg = calledByGraph calls
    modify $ record { calledBy = Just cg }
    pure cg

export
liftGrinM : (forall a. m1 a -> m2 a) -> GrinT name m1 a -> GrinT name m2 a
liftGrinM f (MkGrinM (ST m)) = MkGrinM $ ST \st => f $ m st

export
runGrinT' : GrinT name m a -> Analysis name -> m (Analysis name, a)
runGrinT' m a = runStateT a $ unGrinM m

export
runGrinT : Functor m => GrinT name m a -> Prog name -> m (Prog name, a)
runGrinT m p = mapFst prog <$> runGrinT' m (newAnalysis p)

export
runGrinM' : GrinM name a -> Analysis name -> (Analysis name, a)
runGrinM' m a = runIdentity $ runGrinT' m a

export
runGrinM : GrinM name a -> Prog name -> (Prog name, a)
runGrinM m p = runIdentity $ runGrinT m p

export
execGrinM : GrinM name a -> Prog name -> Prog name
execGrinM m p = fst $ runGrinM m p

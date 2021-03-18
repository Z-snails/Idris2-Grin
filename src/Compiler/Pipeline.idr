module Compiler.Pipeline

||| Information about a transformation step.
public export
record TransInfo (m : Type -> Type) (from : Type) (to : Type) where
    constructor MkTI
    transform : from -> m to

export
liftTI : (forall a. m0 a -> m1 a) -> TransInfo m0 from to -> TransInfo m1 from to
liftTI f ti = MkTI (f . ti.transform)

public export
data Pipeline : (m : Type -> Type) -> (from : Type) -> (to : Type) -> Type where
    Nil : Pipeline m ty ty
    (::) : TransInfo m from int -> Pipeline m int to -> Pipeline m from to

export
runPipeline : Monad m => Pipeline m from to -> from -> m to
runPipeline Nil x = pure x
runPipeline (ti :: tis) x = ti.transform x >>= runPipeline tis

export
pipeLineToTI : Monad m => Pipeline m from to -> TransInfo m from to
pipeLineToTI p = MkTI $ runPipeline p
module GRIN.Name

import Control.Monad.State
import Data.SortedMap

||| A name and resolved index.
public export
record Resolved a where
    constructor MkResolved
    res : Int
    orig : a

export
Eq (Resolved a) where
    (==) = (==) `on` res

export
Ord (Resolved a) where
    compare = compare `on` res

export
Show a => Show (Resolved a) where
    show = show . orig

||| State for resolving names.
record ResolveState name where
    constructor MkResState
    nextId : Int
    resolved : SortedMap name Int

||| Monad for resolving names.
export
record ResolveM name a where
    constructor MkResolveM
    unResolveM : State (ResolveState name) a

export
runResolveM : Ord name => ResolveM name a -> a
runResolveM = evalState (MkResState 0 empty) . unResolveM

export
Functor (ResolveM name) where
    map f = MkResolveM . map f . unResolveM

export
Applicative (ResolveM name) where
    pure = MkResolveM . pure
    f <*> x = MkResolveM $ unResolveM f <*> unResolveM x

export
Monad (ResolveM name) where
    x >>= f = MkResolveM $ unResolveM x >>= (unResolveM . f)

MonadState (ResolveState name) (ResolveM name) where
    get = MkResolveM get
    put = MkResolveM . put
    state = MkResolveM . state

export
resolve : name -> ResolveM name (Resolved name)
resolve orig = do
    st <- get
    case lookup orig st.resolved of
        Just res => pure $ MkResolved res orig
        Nothing => do
            let res = st.nextId
            put (record { nextId $= (+ 1), resolved $= insert orig res } st)
            pure $ MkResolved res orig

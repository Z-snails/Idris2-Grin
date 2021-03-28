module Core.Instances

import Core.Core

public export
Functor Core where
    map = Core.map

public export
Applicative Core where
    pure = Core.pure
    (<*>) = Core.(<*>)

public export
Monad Core where
    (>>=) = Core.(>>=)
    join mm = Core.(>>=) mm id
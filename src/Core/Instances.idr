module Core.Instances

import Core.Core

export
Functor Core where
    map = Core.map

export
Applicative Core where
    pure = Core.pure
    (<*>) = Core.(<*>)

export
Monad Core where
    (>>=) = Core.(>>=)
    join x = Core.(>>=) x id
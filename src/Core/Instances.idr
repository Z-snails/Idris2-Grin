module Core.Instances

import Core.Core
import Core.Name

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
    join mm = Core.(>>=) mm id

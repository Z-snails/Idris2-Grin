module Grin.Prims.Constructors

import Grin.Syntax

primNullCons : List GrinVar
primNullCons = Grin <$>
    [ "World"
    , "MkWorld"
    ]

primUnCons : List GrinVar
primUnCons = Grin <$>
    [ "Integer"
    , "Int"
    , "Bits8"
    , "Bits16"
    , "Bits32"
    , "Bits64"
    ]

||| All primitive constructors.
||| for example: `CInteger` (Grin "Integer", 1)
export
primCons : List (GrinVar, Nat)
primCons = map (, 0) primNullCons ++ map (, 1) primUnCons
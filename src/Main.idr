module Main

import Grin.GrinCG
import Idris.Driver
import Compiler.Common


main : IO ()
main = mainWithCodegens [("grin", grin)]
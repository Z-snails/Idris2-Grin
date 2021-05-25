module GRIN.GrinState

import Data.List
import Data.SortedMap
import Data.SortedSet as Set

import GRIN.AST
import GRIN.Error
import GRIN.Analysis.MaxVar

public export
0 CallGraph : Type -> Type
CallGraph name = SortedMap name (SortedSet name)

public export
record GrinState name where
    constructor MkGrinState
    prog : Prog name
    calls : Maybe (CallGraph name)
    calledBy : Maybe (CallGraph name)
    toInline : SortedMap name (Def name) -- should have all fetch ids removed
    errors : List Error
    varMap : SortedMap Var Var
    nextVar : Var

export
getErrors : GrinState name -> List Error
getErrors = reverse . errors

export
newGrinState : Ord name => Prog name -> GrinState name
newGrinState prog = MkGrinState
    { prog
    , calls = Nothing
    , calledBy = Nothing
    , toInline = empty
    , errors = []
    , varMap = empty
    , nextVar = incVar $ maxVar prog
    }

public export
data AnalysisTag
    = CallsGraph
    | CalledByGraph
    | CallGraphs

module GRIN.Analysis

import Data.SortedMap
import Data.SortedSet as Set

import GRIN.AST

public export
0 CallGraph : Type -> Type
CallGraph name = SortedMap name (SortedSet name)

public export
record Analysis name where
    constructor MkAnalysis
    prog : Prog name
    calls : Maybe (CallGraph name)
    calledBy : Maybe (CallGraph name)

export
newAnalysis : Prog name -> Analysis name
newAnalysis p = MkAnalysis p Nothing Nothing

public export
data AnalysisTag
    = CallsGraph
    | CalledByGraph
    | CallGraphs
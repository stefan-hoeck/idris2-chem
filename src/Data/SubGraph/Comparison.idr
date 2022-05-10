module Data.SubGraph.Comparison

%default total


-- Matcher


||| Type for definition of comparison / matching
||| functions for the detection of subgraph
||| isomorphisms
public export
Matcher : (a : Type) -> (b : Type) -> Type
Matcher a b = a -> b -> Bool

-- Matcher logic
public export
always : Matcher a b

public export
never : Matcher a b

public export
(&&) : Matcher a b -> Matcher a b -> Matcher a b

public export
(||) : Matcher a b -> Matcher a b -> Matcher a b

public export
not : Matcher a b -> Matcher a b

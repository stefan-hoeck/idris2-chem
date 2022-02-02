module Data.SubGraph.Comparison

%default total


-- Matcher 


||| Type for definition of comparison / matching
||| functions for the detection of subgraph
||| isomorphisms
public export
Matcher : (a : Type) -> Type
Matcher a = a -> a -> Bool

-- Matcher logic
public export
always : Matcher a

public export
never : Matcher a

public export
(&&) : Matcher a -> Matcher a -> Matcher a

public export
(||) : Matcher a -> Matcher a -> Matcher a

public export
not : Matcher a -> Matcher a

-- Algorithms for converting molecule with explicit hydrogens to ones
-- with implicit hydrogens and vice versa.

module Chem.Hydrogens

import Chem.Element
import Chem.Types
import Data.AssocList
import Data.BitMap
import Data.Graph
import Data.String
import Text.Smiles
import Data.List

%default total


--------------------------------------------------------------------------

--------------------------- Explicit to Implicit -------------------------

--------------------------------------------------------------------------


-- Record with bool defines whether node and bonds are merged into graph
record MergeResults m where
  constructor MkMR
  keepNeigh : Bool
  node      : m


-- Map over new node labels by applying f2 and deleting all nodes which
-- fullfill the deleting criterion
mapUtil :
     Maybe m
  -> (e -> n -> m -> MergeResults m)
  -> Graph e n
  -> (n, List (Node, e))
  -> Maybe (m, List (Node, e))
mapUtil mm f2 g (n, neigh) = map (\x => foldl acc (x,[]) neigh) mm
  where acc : (m, List (Node, e)) -> (Node, e) -> (m, List (Node, e))
        acc (ml, ps) (node, el) = case lab g node of
            Nothing => (ml, ps)
            Just x  => case f2 el x ml of
                    (MkMR False y) => (y, ps)
                    (MkMR True y)  => (y, (node, el) :: ps)


-- Generate an adjacency of a node by using mapUtil and change node label
-- with f1
mapAdj :
     (Adj e n -> Maybe m)
  -> (e -> n -> m -> MergeResults m)
  -> Graph e n
  -> Adj e n
  -> Maybe (Adj e m)
mapAdj f1 f2 g adj@(MkAdj label neighbours) = case mapUtil (f1 adj) f2 g (label, pairs neighbours) of
     Nothing       => Nothing
     Just (lbl,ns) => Just (MkAdj lbl (AssocList.fromList ns))


-- Collapse a graph by calling mapAdj and therefore mapUtil
-- f1 defines how to change the node label and f2 defines the criteria
-- of how to collapse the graph
public export
collapseGraph :
     Graph e n
  -> (Adj e n -> Maybe m)
  -> (e -> n -> m -> MergeResults m)
  -> Graph e m
collapseGraph g f1 f2 = MkGraph $ mapMaybe (mapAdj f1 f2 g) g.graph


-- MergeResults will show False if the neighbour is a hydrogen bound by a
-- single bond. The count will be increased by one and the node will be
-- deleted. In all other cases, MergeResults will show True and the node
-- will be kept.
public export
explH : Bond -> Elem -> (Elem, Nat) -> MergeResults (Elem, Nat)
explH _    H (H, n)    = MkMR True (H, n)
explH Sngl H (elem, n) = MkMR False (elem, n+1)
explH _    _ (elem, n) = MkMR True (elem, n)


-- The node label is changed to a pair of an element and a natural number
-- as an indicator of how many neighbouring nodes have been deleted
public export
initH : Graph Bond Elem -> Adj Bond Elem -> Maybe (Elem,Nat)
initH g (MkAdj H (MkAL [(k,Sngl)])) = case lab g k of
  Just H => Just (H,0)
  _      => Nothing
initH g (MkAdj x _) = Just (x,0)


-- Specific case to collapse graph and convert all explicit hydrogen atoms
-- into implicit ones
public export
noExplicitHs : Graph Bond Elem -> Graph Bond (Elem,Nat)
noExplicitHs g = collapseGraph g (initH g) explH




--------------------------------------------------------------------------

------------------------ Implicit to Explicit ----------------------------

--------------------------------------------------------------------------


-- Create new list of adjacencies from given graph
public export
foldNode : (m -> List (e, n)) -> Graph e m -> (List (Adj e n))
foldNode f1 g = foldlKV accList Lin g.graph <>> []
  where accList : SnocList (Adj e n) -> Node -> Adj e m -> SnocList (Adj e n)
        accList xs node x = xs <>< map (\(ve, vn) => MkAdj vn (fromList [(node,ve)])) (f1 x.label)


-- Starting value for new node
public export
startNode : Graph e m -> Node
startNode g = foldl max 0 (nodes g) + 1


-- Convert adjacency to context by using
-- MkContext, new node value and given adjacency
public export
newCtxt : Adj e n -> Bits32 -> Context e n
newCtxt (MkAdj label neighbours) node = MkContext node label neighbours


-- Convert list of adjacencies to a list of contexts by using newCtxt.
-- Every node gets a new Bits32 value
public export
newCtxts : List (Adj e n) -> Bits32 -> List (Context e n)
newCtxts Nil _ = Nil
newCtxts (x :: xs) node = newCtxt x node :: newCtxts xs (node+1)


-- Given a graph with implicit nodes and a function f1, getCtxts creates
-- a list of new contexts
public export
getCtxts : Graph e m -> (m -> List (e,n)) -> List (Context e n)
getCtxts g f1 = newCtxts (foldNode f1 g) (startNode g)


-- Merge new contexts and original graph
public export
expandGraph : Graph e m -> (m -> n) -> (m -> List (e,n)) -> Graph e n
expandGraph g f2 f1 = foldl addCtxt (map f2 g) (getCtxts g f1)
  where addCtxt : Graph e n -> Context e n -> Graph e n
        addCtxt g x = add x g


-- Create new pairs with bond label and hydrogen, amount of pairs depends
-- on Nat
public export
newHydrogen : (Elem, Nat) -> List (Bond, Elem)
newHydrogen (_, n) = replicate n (Sngl, H)


-- Specific case to expand graph and convert all implicit hydrogen atoms
-- into explicit ones
public export
noImplicitHs : Graph Bond (Elem, Nat) -> Graph Bond Elem
noImplicitHs g = expandGraph g fst newHydrogen




---------------------------------------------------------------------------

--------------- Main functions to test the above code ---------------------

---------------------------------------------------------------------------

-- Run from project's root directory with: `pack exec src/Chem/Hydrogens.idr`

toElem : Atom -> Elem
toElem (SubsetAtom elem arom) = elem
toElem (Bracket massNr elem isArom chirality hydrogens charge) = elem

------------------- test explicit to implicit -------------------------------

--showPair : (Elem,Nat) -> String
--showPair (e,n) = symbol e ++ "[" ++ show n ++ "]"

--covering
--main : IO ()
--main = do
--  putStr "please enter a SMILES code (q to quit): "
--  str <- trim <$> getLine
--  case str of
--    "q" => putStrLn "Goodbye!"
--    s   => case parse s of
--      Left (fc,e) =>  putStrLn (printParseError s fc e) >> main
--      Right mol   =>
--        let mol' := noExplicitHs (map toElem mol)
--         in putStrLn (pretty interpolate showPair mol') >> main

------------------- test explicit to implicit to explicit -------------------

--showPair : Elem -> String
--showPair e = symbol e


--covering
--main : IO ()
--main = do
--  putStr "please enter a SMILES code (q to quit): "
--  str <- trim <$> getLine
--  case str of
--    "q" => putStrLn "Goodbye!"
--    s   => case parse s of
--      Left (fc,e) =>  putStrLn (printParseError s fc e) >> main
--      Right mol   =>
--        let mol' := noImplicitHs (noExplicitHs (map toElem mol))
--         in putStrLn (pretty interpolate showPair mol') >> main

------------------- test implicit to explicit -------------------------------

showPair : Elem -> String
showPair e = symbol e

toPair : Atom Chirality -> (Elem,Nat)
toPair a = (a.elem, cast a.hydrogen)

covering
main : IO ()
main = do
  putStr "please enter a SMILES code (q to quit): "
  str <- trim <$> getLine
  case str of
    "q" => putStrLn "Goodbye!"
    s   => case graphWithH <$> parse s of
      Left (fc,e)      =>  putStrLn (printParseError s fc e) >> main
      Right Nothing    =>  putStrLn "Implicit H detection failed"
      Right (Just mol) =>
       let mol' := noImplicitHs (map toPair mol)
        in putStrLn (pretty interpolate showPair mol') >> main


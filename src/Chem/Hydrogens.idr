||| Algorithms for converting molecule with explicit hydrogens
||| to ones with implicit hydrogens and vice versa.
module Chem.Hydrogens

import Chem.Element
import Chem.Types
import Data.AssocList
import Data.BitMap
import Data.Graph
import Data.String
import Text.Smiles

%default total

---------------------------------- Notes ---------------------------------

------ Existing types

-- HCount (= Bits8; <10), Elem (= all elements),

-- Graph: Node, Edge, LNode, LEdge
-- Adj: with node label and AssocList e
-- Context: Node + node label + AssocList e
-- AssocList (= List of neighbours and labels of edges)

-- Atom is not imported yet!!
-- Atom a (in Atom.idr) (= record with Elem, arom (Bool), Maybe massNr -> Nothing = natürlicher mix, Just = Isotop,
--                       charge, label a, hydrogen (HCount)
-- No information should be lost like charge, isotope, single bond


------ Necessary types

---- With explicit hydrogen atoms:
-- Graph with edge labels and node labels
-- Elem as it is (with H) -> do we have a function that reads the nodes
-- and makes it type element?

---- for the transformation I need:
-- List of all nodes that are hydrogen atoms (only Nat, label not needed)
-- or is it needed for control?
-- List of all edges between all Hydrogens and another atom
-- (to know what to delete)
-- Number of neighbouring H atoms of a node (not an H)
-- Function that changes element into a new type (atom?) which has space
-- for a hydrogen count -> might need a test that it's not H to avoid
-- errors?
-- Then I can write element in new type with hydrogen count,
-- then delete H and edges between H and other atom




---- with implicit hydrogen atoms:
-- new Type like Elem, but shouldn't include H to avoid errors
-- is the type Atom needed here? Because we have the value hydrogen
--




-- notes:
-- gmap
-- alternative mit fold Graph traversieren, dabei sammeln, welche Knoten gelöscht werden müssen

-- dann überlegen, was kann man mit ufold und gmap machen. Wie löschen wir Nodes, brauchen wir noch mehr Infos
-- wie bauen wir Graph am Schluss auf?
-- note: c in ufold kann auch für einen Graph stehen



------------------------------ Task --------------------------------------

-- define function (in general) with nothing to do with hydrogens.
-- just how the edges and nodes are tested
-- In the form of merge: Graph e n -> ... -> Graph e n



||| Define record whether to merge results
record MergeResults m where
  constructor MkMR
  keepNeigh : Bool
  node      : m


-- testing function whether hydrogen needs to be deleted
testH : Edge -> Node -> Node -> MergeResults m

iterationList : (Node, e) -> e
iterationList (_, y) = y

-- 1. scrutinee label in m umwandeln
-- 2. iterieren über Liste List (Node, e) -> für jeden Node ein Label
-- 3. mit diesem Label 2. Funktion aufrufen (e -> ...) mit edge label, node label, akkumulierter Node = MergeResults m
-- bei Rekursion label m mitführen, List (Node, e), weil sie angepasst wird
mapUtil : (n -> m) -> (e -> n -> m -> MergeResults m) -> Graph e n -> (n, List (Node, e)) -> (m, List (Node, e))
mapUtil f1 f2 g (n, neigh) = foldl acc (f1 n,[]) neigh
  where acc : (m, List (Node, e)) -> (Node, e) -> (m, List (Node, e))
        acc (ml, ps) (node, el) = case lab g node of
            Nothing => (ml, ps)
            Just x  => case f2 el x ml of
                    (MkMR False y) => (y, ps)
                    (MkMR True y)  => (y, (node, el) :: ps)

-- TODO: Nicole
-- implement this by invoking `mapUtil`. Use `Data.AssocList.pairs` and `Data.AssocList.fromList`
-- to convert from `AssocList e` to `List (Node,e)` and back.
mapCtxt : (n -> m) -> (e -> n -> m -> MergeResults m) -> Graph e n -> Context e n -> Context e m
mapCtxt f1 f2 g (MkContext node label neighbours) =
  MkContext node (fst (mapUtil f1 f2 g (label, pairs neighbours))) (AssocList.fromList (snd (mapUtil f1 f2 g (label, pairs neighbours))))
-- wäre es sinnvoll, wenn Klammer mit mapUtil in eigener Funktion steht?


-- TODO: Nicole
-- use `gmap` and `mapCtxt` here
merge : Graph e n -> (n -> m) -> (e -> n -> m -> MergeResults m) -> Graph e m
merge g f1 f2 = gmap (mapCtxt f1 f2 g) g




-- MergeResults will show false if the neighbour is a hydrogen bound by a
-- single bond and the count will be increased by one. MergeResults will
-- show true if neighbour is any other element and count doesn't change
explH : Bond -> Elem -> (Elem, Nat) -> MergeResults (Elem, Nat)
explH Sngl H (elem, n) = MkMR False (elem, n+1)
explH _    _ (elem, n) = MkMR True (elem, n)

-- TODO: Nicole
-- Use `merge` and define the two function arguments accordingly (see notes on
-- paper)
-- n -> m as a lambda
noImplicitHs : Graph Bond Elem -> Graph Bond (Elem,Nat)
noImplicitHs g = merge g (\x => (x,0)) explH



toElem : Atom -> Elem
toElem (SubsetAtom elem arom) = elem
toElem (Bracket massNr elem isArom chirality hydrogens charge) = elem

showPair : (Elem,Nat) -> String
showPair (e,n) = symbol e ++ "[" ++ show n ++ "]"

-- run from project's root directory with: `pack exec src/Chem/Hydrogens.idr`
covering
main : IO ()
main = do
  putStr "please enter a SMILES code (q to quit): "
  str <- trim <$> getLine
  case str of
    "q" => putStrLn "Goodbye!"
    s   => case parse s of
      Left (fc,e) =>  putStrLn (printParseError s fc e) >> main
      Right mol   =>
        let mol' := noImplicitHs (map toElem mol)
         in putStrLn (pretty interpolate showPair mol') >> main





-- Types:
-- neighbours = List (Node, e)
-- node = Node
-- label = n


-- Was wir brauchen:
-- List (Node, (e, n)) -> mapMaybeK (Data.Assoclist)
-- 2 Funktionen: 1. n -> m (n = label scrutinee)
--               2. e -> n -> m -> MergeResults m (n = label neighbour, m = wird akkumuliert)





-- `delEdge` löscht ein Edge aus dem Graph (Edge -> Graph -> Graph)



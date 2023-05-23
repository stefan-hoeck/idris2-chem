||| Algorithms for converting molecule with explicit hydrogens
||| to ones with implicit hydrogens and vice versa.
module Chem.Hydrogens

import Chem.Element
import Chem.Types
import Data.AssocList
import Data.BitMap
import Data.Graph

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

-- was macht diese Funktion?
argumentgmap : (e -> n -> n -> MergeResults m) -> Graph e n -> Context e n -> Context e m
argumentgmap f x (MkContext node label neighbours) = ?argumentgmap_rhs_0


iterationList : (Node, e) -> e
iterationList (_, y) = y

-- 1. scrutinee label in m umwandeln
-- 2. iterieren über Liste List (Node, e) -> für jeden Node ein Label
-- 3. mit diesem Label 2. Funktion aufrufen (e -> ...) mit edge label, node label, akkumulierter Node = MergeResults m
-- bei Rekursion label m mitführen, List (Node, e), weil sie angepasst wird
argumentgmap2 : (n -> m) -> (e -> n -> m -> MergeResults m) -> Graph e n -> (n, List (Node, e)) -> (m, List (Node, e))
argumentgmap2 f1 f2 g (n, neigh) = foldl acc (f1 n,[]) neigh
  where acc : (m, List (Node, e)) -> (Node, e) -> (m, List (Node, e))
        acc (ml, ps) (node, el) = case lab g node of
            Nothing => (ml, ps)
            Just x  => case f2 el x ml of
                    (MkMR False y) => (y, ps)
                    (MkMR True y)  => (y, (node, el) :: ps)



  -- ?foo (map iterationList neigh) --(f2 ?e n (f1 n) )
--            MkMR True m  => (m, (?something :: ?somethingelse) ) -- aber m muss auch in Rekursion rein?
--            MkMR False m => ?Falsecase
-- second function
-- kann ich ?e mit map lösen? Und dann etwas ähnliches wie die Funktion fst, aber das 2. Element
-- n -> m : was wird hier geändert? Sind n und m nicht gleich?





-- Types:
-- neighbours = List (Node, e)
-- node = Node
-- label = n


-- Was wir brauchen:
-- List (Node, (e, n)) -> mapMaybeK (Data.Assoclist)
-- 2 Funktionen: 1. n -> m (n = label scrutinee)
--               2. e -> n -> m -> MergeResults m (n = label neighbour, m = wird akkumuliert)


-- delete edges, adapt node labels (green nodes), just not delete nodes yet
merge : Graph e n -> (e -> n -> n -> MergeResults m) -> Graph e m
merge x f = gmap (argumentgmap f x) x

test2 : Graph e n -> Graph e n


-- wie bei map kann ich hier die Funktion schreiben, die angewendet wird
-- z.B. wie (+1), aber wie bringe ich ein Graph in die Form Context e n?

-- function `contexts` macht eine Liste von Contexts aus einem Graph
-- (Graph -> List (Context e n))
-- `delEdge` löscht ein Edge aus dem Graph (Edge -> Graph -> Graph)



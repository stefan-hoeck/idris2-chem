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
import Data.List

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


--------------------------------------------------------------------------

--------------------------- Explicit to Implicit -------------------------

--------------------------------------------------------------------------

-- define function (in general) with nothing to do with hydrogens.
-- just how the edges and nodes are tested
-- In the form of merge: Graph e n -> ... -> Graph e n



-- Define record whether to merge results
record MergeResults m where
  constructor MkMR
  keepNeigh : Bool
  node      : m



-- 1. scrutinee label in m umwandeln
-- 2. iterieren über Liste List (Node, e) -> für jeden Node ein Label
-- 3. mit diesem Label 2. Funktion aufrufen (e -> ...) mit edge label, node label, akkumulierter Node = MergeResults m
-- bei Rekursion label m mitführen, List (Node, e), weil sie angepasst wird
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


-- TODO: Nicole
-- implement this by invoking `mapUtil`. Use `Data.AssocList.pairs` and `Data.AssocList.fromList`
-- to convert from `AssocList e` to `List (Node,e)` and back.
mapAdj :
     (Adj e n -> Maybe m)
  -> (e -> n -> m -> MergeResults m)
  -> Graph e n
  -> Adj e n
  -> Maybe (Adj e m)
mapAdj f1 f2 g adj@(MkAdj label neighbours) = case mapUtil (f1 adj) f2 g (label, pairs neighbours) of
     Nothing       => Nothing
     Just (lbl,ns) => Just (MkAdj lbl (AssocList.fromList ns))
--   let (lbl,ns) := mapUtil f1 f2 g (label, pairs neighbours)
--    in MkAdj lbl (AssocList.fromList ns)
-- wäre es sinnvoll, wenn Klammer mit mapUtil in eigener Funktion steht? Z.B. mit let (lbl, ns) := ...

-- TODO: Nicole
-- use `gmap` and `mapCtxt` here
public export
collapseGraph :
     Graph e n
  -> (Adj e n -> Maybe m)
  -> (e -> n -> m -> MergeResults m)
  -> Graph e m
collapseGraph g f1 f2 = MkGraph $ mapMaybe (mapAdj f1 f2 g) g.graph




-- MergeResults will show false if the neighbour is a hydrogen bound by a
-- single bond and the count will be increased by one. MergeResults will
-- show true if neighbour is any other element and count doesn't change
public export
explH : Bond -> Elem -> (Elem, Nat) -> MergeResults (Elem, Nat)
explH Sngl H (elem, n) = MkMR False (elem, n+1)
explH _    _ (elem, n) = MkMR True (elem, n)

public export
initH : Graph Bond Elem -> Adj Bond Elem -> Maybe (Elem,Nat)
initH g (MkAdj H (MkAL [(k,Sngl)])) = case lab g k of
  Just H => Just (H,0)
  _      => Nothing
initH g (MkAdj x _) = Just (x,0)

-- initH H = Nothing
-- initH x = Just (x,0)

-- hier wird nur ein Weg einer Bindung beachtet also z.B. von H nach C
-- dann ist im Pattern Match Sngl C -> True


-- TODO: Nicole
-- Use `merge` and define the two function arguments accordingly (see notes on
-- paper)
-- n -> m as a lambda
public export
noExplicitHs : Graph Bond Elem -> Graph Bond (Elem,Nat)
noExplicitHs g = collapseGraph g (initH g) explH








--------------------------------------------------------------------------

------------------------ Implicit to Explicit ----------------------------

--------------------------------------------------------------------------
-- create new list of adjacencies from given graph
public export
foldNode : (m -> List (e, n)) -> Graph e m -> (List (Adj e n))
foldNode f g = (foldlKV accList [] g.graph)
  -- TODO : Use `SnocList` for the first argument.
  -- At the REPL: Use `:doc SnocList` to see the available data constructors.
  -- Use `(<>>)` to convert a `SnocList` to a `List`.
  -- Use `(<><)` to append a `List` to a `SnocList`
  where accList : List (Adj e n) -> Node -> Adj e m -> List (Adj e n)
        accList xs node x = map (\(ve, vn) => MkAdj vn (fromList [(node,ve)])) (f x.label) ++ xs


-- starting value for Node
public export
startNode : Graph e m -> Node
startNode g = foldl max 0 (nodes g) + 1

-- transform Adj e n to Context e n by using
-- MkContext nodeValue and given Adjacency
public export
newCtxt : Adj e n -> Bits32 -> Context e n
newCtxt (MkAdj label neighbours) node = MkContext node label neighbours

public export
newCtxts : (Adj e n -> Bits32 -> Context e n) -> List (Adj e n) -> Bits32 -> List (Context e n)
newCtxts fun Nil _ = Nil
newCtxts fun (x :: xs) node = fun x node :: newCtxts fun xs (node+1)

public export
getCtxts : Graph e m -> (m -> List (e,n)) -> List (Context e n)
getCtxts g f1 = newCtxts newCtxt (foldNode f1 g) (startNode g)
-- f1 is here supposed to be newHydrogen



-- merge new contexts and original graph
--
-- TODO: * Abstract over edge and node label types
--       * Read idris2-hedgehog introduction and have a look
--         at the chem test suite. Try to come up with one or
--         more property tests for your algorithms.
--       * Think of another application/use case of the the
--         abstract versions of expandGraph and merge
--       -> stereochemistry? Für Keil-Strich-Formel expandieren
--          oder wenn es egal ist, dann collapse?
public export
expandGraph : Graph e m -> (m -> n) -> (m -> List (e,n)) -> Graph e n
expandGraph g f1 f2 = foldl addCtxt (map f1 g) (getCtxts g f2)
  where addCtxt : Graph e n -> Context e n -> Graph e n
        addCtxt g x = add x g



-- create new pairs with bond label and hydrogen, amount of pairs depends
-- on Nat
public export
newHydrogen : (Elem, Nat) -> List (Bond, Elem)
newHydrogen (_, n) = replicate n (Sngl, H)


public export
testExpand : Graph Bond (Elem, Nat) -> Graph Bond Elem
testExpand g = expandGraph g fst newHydrogen



-- Types:
-- neighbours = List (Node, e)
-- node = Node
-- label = n


-- Was wir brauchen:
-- List (Node, (e, n)) -> mapMaybeK (Data.Assoclist)
-- 2 Funktionen: 1. n -> m (n = label scrutinee)
--               2. e -> n -> m -> MergeResults m (n = label neighbour, m = wird akkumuliert)

toElem : Atom -> Elem
toElem (SubsetAtom elem arom) = elem
toElem (Bracket massNr elem isArom chirality hydrogens charge) = elem

------------------- test explicit to implicit -------------------------------
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
        let mol' := noExplicitHs (map toElem mol)
         in putStrLn (pretty interpolate showPair mol') >> main

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
--        let mol' := testExpand (noExplicitHs (map toElem mol))
--         in putStrLn (pretty interpolate showPair mol') >> main


------------------- test implicit to explicit -------------------------------
--showPair : Elem -> String
--showPair e = symbol e

--toPair : Atom Chirality -> (Elem,Nat)
--toPair a = (a.elem, cast a.hydrogen)

--covering
--main : IO ()
--main = do
--  putStr "please enter a SMILES code (q to quit): "
--  str <- trim <$> getLine
--  case str of
--    "q" => putStrLn "Goodbye!"
--    s   => case graphWithH <$> parse s of
--      Left (fc,e)      =>  putStrLn (printParseError s fc e) >> main
--      Right Nothing    =>  putStrLn "Implicit H detection failed"
--      Right (Just mol) =>
--       let mol' := testExpand (map toPair mol)
--        in putStrLn (pretty interpolate showPair mol') >> main


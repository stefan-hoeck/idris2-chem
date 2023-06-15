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


--------------------------------------------------------------------------

--------------------------- Explicit to Implicit -------------------------

--------------------------------------------------------------------------

-- define function (in general) with nothing to do with hydrogens.
-- just how the edges and nodes are tested
-- In the form of merge: Graph e n -> ... -> Graph e n



-- Define record whether to merge results into graph
record MergeResults m where
  constructor MkMR
  keepNeigh : Bool
  node      : m



-- map over new node labels by applying f2 and deleting all nodes which
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


-- Generate an Adjacency of a Node by using mapUtil and change node label
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


-- Specific case to collaps graph and convert all explicit hydrogen atoms
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
foldNode f g = (<>>) (foldlKV accList Lin g.graph) []
  -- TODO : Use `SnocList` for the first argument.
  -- At the REPL: Use `:doc SnocList` to see the available data constructors.
  -- Use `(<>>)` to convert a `SnocList` to a `List`.
  -- Use `(<><)` to append a `List` to a `SnocList`
  where accList : SnocList (Adj e n) -> Node -> Adj e m -> SnocList (Adj e n)
        accList xs node x = (<><) xs $ map (\(ve, vn) => MkAdj vn (fromList [(node,ve)])) (f x.label)


-- Starting value for new Node
public export
startNode : Graph e m -> Node
startNode g = foldl max 0 (nodes g) + 1

-- Convert Adjacency to Context by using
-- MkContext, new node value and given Adjacency
public export
newCtxt : Adj e n -> Bits32 -> Context e n
newCtxt (MkAdj label neighbours) node = MkContext node label neighbours

-- Convert List of Adjacencies to a List of Contexts by using newCtxt.
-- Every Node gets a new Bits32 value
public export
newCtxts : List (Adj e n) -> Bits32 -> List (Context e n)
newCtxts Nil _ = Nil
newCtxts (x :: xs) node = newCtxt x node :: newCtxts xs (node+1)

-- Given a Graph with implicit Nodes and a function f1, getCtxts creates
-- a List of new Contexts
public export
getCtxts : Graph e m -> (m -> List (e,n)) -> List (Context e n)
getCtxts g f1 = newCtxts (foldNode f1 g) (startNode g)



-- merge new contexts and original graph
--
-- TODO: * Think of another application/use case of the the
--         abstract versions of expandGraph and merge
--       -> stereochemistry? Für Keil-Strich-Formel expandieren
--          oder wenn es egal ist, dann collapse?

-- Expand Graph by creating new Contexts and adding them to the original
-- Graph
public export
expandGraph : Graph e m -> (m -> n) -> (m -> List (e,n)) -> Graph e n
expandGraph g f1 f2 = foldl addCtxt (map f1 g) (getCtxts g f2)
  where addCtxt : Graph e n -> Context e n -> Graph e n
        addCtxt g x = add x g


-- Create new pairs with bond label and hydrogen, amount of pairs depends
-- on Nat
public export
newHydrogen : (Elem, Nat) -> List (Bond, Elem)
newHydrogen (_, n) = replicate n (Sngl, H)


--
public export
noImplicitHs : Graph Bond (Elem, Nat) -> Graph Bond Elem
noImplicitHs g = expandGraph g fst newHydrogen



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
--        let mol' := noImplicitHs (noExplicitHs (map toElem mol))
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
--       let mol' := noImplicitHs (map toPair mol)
--        in putStrLn (pretty interpolate showPair mol') >> main


module Data.Graph.GraphAlgorithms

import Data.Bifoldable
import Data.IntMap
import Data.Graph.Types
import Data.Graph.Util
import Data.List
import Data.Nat

-- TODO: Disabled as discussed for the time being
%default total


-- General ---------------------------------------------------------------------

-- Multi-way tree
public export
data MWTree a = Br a (List (MWTree a))

||| Postorder traversal
||| Visits the nodes of all subtrees before the root
partial export
postorder : MWTree a -> List a
postorder (Br v ts) = reverse $ v :: concatMap postorder ts


-- A. Unlabeled Graphs ---------------------------------------------------------

||| Representation of a list of nodes
||| unlabeled
public export
Path : Type
Path = List Node

||| Root Path tree
||| Unlabeled
public export
RTree : Type
RTree = List Path


-- 1.1 dfs
||| Depth First search
|||
||| Requires a list of all nodes of the graph
||| to make sure that all nodes are visited.
|||
||| Output:
||| List of nodes in depth first order
partial export
dfs : List Node -> Graph e n -> List Node
dfs []        _ = []
dfs (v :: vs) g = if isEmpty g then [] else
  case match v g of
    Split c g' => v :: dfs ((keys $ neighbours c) ++ vs) g'
    Empty      => dfs vs g


-- 1.2 bfs
||| Breadth First Search
|||
||| Output:
||| List of nodes in breadth first order
partial export
bfs : List Node -> Graph e n -> List Node
bfs []        _ = []
bfs (v :: vs) g = if isEmpty g then [] else
  case match v g of
    Split c g' => v :: bfs (vs ++ (keys $ neighbours c)) g'
    Empty => bfs vs g


-- Spanning Trees --------------------------------------------------------------
partial
df : List Node -> Graph e n -> (List (MWTree Node), Graph e n)
df []        g = ([],g)
df (v :: vs) g = if isEmpty g then ([],empty) else 
    case match v g of
      Empty      => df vs g
      Split c g' => dfhelp v c g
        where
    partial
    dfhelp : Node -> Context e n -> Graph e n -> (List (MWTree Node), Graph e n)
    dfhelp v c g = let (f,g1)  = df (keys $ neighbours c) g
                       (f',g2) = df vs g1
                   in (Br v f :: f', g2)


||| Depth first spanning forest
partial export
dff : List Node -> Graph e n -> List (MWTree Node)
dff vs g = fst (df vs g)

-- TODO: Optimize topsort and scc

||| Topological sorting
partial export
topsort : Graph e n -> List Node
topsort g = reverse $ concatMap postorder $ dff (nodes g) g-- concatMap postorder . dff

||| Strongly connected components
partial export
scc : Graph e n -> List (MWTree Node)
scc g = dff (topsort g) (?grev g) 
-- grev see: fgl/Data/Graph/Inductive/Basic.hs


-- Root Path Tree --------------------------------------------------------------

||| breadth first algorithm for constructing the root-path tree
partial
bf : List Path -> Graph e n -> RTree
bf []                _  = []
bf (p@(v :: _) :: ps) g = if isEmpty g then [] else
  case match v g of
    Split c g' => p :: bf (ps ++ map (\x => x :: p) (keys $ neighbours c)) g'
    Empty      => bf ps g
bf (p :: ps)          g = bf ps g


||| Breadth first algorithm
||| Output
||| Root-path tree (list of lists actually)
partial export
bft : Node -> Graph e n -> RTree
bft v = bf [[v]] 

-- 3. esp

-- Helper functions
first : (a -> Bool) -> List a -> Maybe a
first p = head' . filter p

evalBool : Eq a => Maybe a -> a -> Bool
evalBool Nothing  _ = False
evalBool (Just v) w = v == w


||| Shortest Path
||| rooted at s
partial export
esp : Node -> Node -> Graph e n -> Maybe Path
esp s t = map reverse . first (\vs => evalBool (head' vs)  t) . bft s


-- 5. Node sets ----------------------------------------------------------------

listFromMaybe : Maybe (List a) -> List a
listFromMaybe Nothing  = []
listFromMaybe (Just l) = l

-- Returns the longer list
-- If none -> empty
compareMaybeLists : Maybe (List a) -> Maybe (List a) -> List a
compareMaybeLists la lb = let a = listFromMaybe la
                              b = listFromMaybe lb
                          in if length a `gt` length b then a else b


||| Finding the largest independent node sets
partial
indep : Graph e n -> List Node
indep empty = []
indep g     = let vs  = nodes g --if ?lend i1 > ?leng i2 then i1 else i2
                  m   = head' $ reverse $ sort $ map (deg g) vs --maximum
                  v   = first (\v => evalBool m (deg g v)) vs
                  mcg = case match <$> v <*> pure g of
                           (Just (Split c g')) => Just (c,g')
                           (Just Empty ) => Nothing
                           Nothing       => Nothing
                  i1 = map (indep . snd) mcg
                  i2 =  (::) <$> v <*> (map (\x => (indep $ delNodes (keys $ neighbours $ fst x) (snd x))) mcg)
              in compareMaybeLists i1 i2

module Test.Data.Isomorphism

import Data.Graph
import Data.SubGraph.InductiveSearch
import Data.SubGraph.Ullmann
import Data.So
import Data.Fin
import Data.Vect
import Data.List
import Test.Data.Graph
import Hedgehog

import Data.BitMap
import Data.AssocList

%default total

-- Percentage -----------------------------------------------------------------
record Ratio where
  constructor MkRatio
  val : Fin 101 -- [0,100]

valD : Ratio -> Nat
valD = finToNat . val

remD : Ratio -> Nat -- (53 % + 47 % = 100 %)
remD = minus 100 . valD

multD : Nat -> Ratio -> Nat
multD k d = (valD d * k) `div` 100

graphDensity : Gen Ratio
graphDensity = MkRatio <$> fin (linearFin 100)

-- Settings -------------------------------------------------------------------
graphSize : Hedgehog.Range Nat
graphSize = linear 0 100

graphDensity' : Hedgehog.Range Nat
graphDensity' = linear 0 100

-- Graph generators -----------------------------------------------------------

graph : Hedgehog.Range Nat -> (density : Hedgehog.Range Nat)
     -> Gen (Graph Char Char)
graph rNodes rDensity = let bond = element ['-','=','#']
                 in lgraph rNodes rDensity bond lower

-- SubGraph
boolRatio : Ratio -> Gen Bool
boolRatio d = frequency [(valD d,pure True),(remD d,pure False)]

listLenN : Nat -> Gen a -> Gen (List a)
listLenN 0     gb = (\x => x :: []) <$> gb
listLenN (S k) gb = (::) <$> gb <*> listLenN k gb

rndFilt : Ratio -> List a -> Gen (List a)
rndFilt d xs = let bl = listLenN (length xs) (boolRatio d)
                   nl = zip xs <$> bl
               in mapMaybe (\(v,b) => if b then Just v else Nothing) <$> nl

subGraph : Ratio -> (g : Graph e n) -> Gen (Graph e n)
subGraph d g = do
   ns <- rndFilt d $ nodes g
   g' <- pure $ delNodes ns g
   es <- rndFilt d $ edges g'
   pure $ delEdges es g'

-- Node renumbering -----------------------------------------------------------

-- Idea: Take values randomly from the list of keys to redistribute them
takeAtPos : Nat -> Vect (S k) a -> (a, Vect k a)
takeAtPos _ (x :: []) = (x, [])
takeAtPos Z (x :: xs) = (x, xs)
takeAtPos (S k) (x :: []) = (x, [])
takeAtPos (S k) (x :: xs@(y::ys)) = map ((::) x) $ takeAtPos k xs

-- Selection of a value and removal of it from the vector
extOne : Vect (S k) a -> Gen (a, Vect k a)
extOne vs = do
  nat <- nat (linear 0 (length vs))
  pure $ takeAtPos nat vs

-- Redistribute the existing keys
newKeys : Vect k Bits64 -> Gen (Vect k Bits64)
newKeys xs = go xs xs
  where go : Vect l Bits64 -> Vect l Bits64 -> Gen (Vect l Bits64)
        go []        []        = pure Nil
        go (x :: xs) (k :: ks) = do
                        (v, rys) <- extOne (k :: ks)
                        res <- go xs rys
                        pure $ Data.Vect.(::) v res

-- new key lookups
keyMapping : List Bits64 -> Gen (BitMap Bits64)
keyMapping xs = let nl = (zip xs . toList) <$> (newKeys (fromList xs))
                in foldl (\m,(cur,new) => insert cur new m) empty <$> nl

-- Key / Edge node replacement
nKeyRep : BitMap Bits64 -> LNode l -> Maybe (LNode l)
nKeyRep m (MkLNode n l) = let x = Data.BitMap.lookup n m in MkLNode <$> x <*> pure l

eKeyRep : BitMap Bits64 -> LEdge l -> Maybe (LEdge l)
eKeyRep m (MkLEdge (MkEdge n1 n2 _) l) =
  let Just n1n := Data.BitMap.lookup n1 m | Nothing => Nothing
      Just n2n := Data.BitMap.lookup n2 m | Nothing => Nothing
  in MkLEdge <$> mkEdge n1n n2n <*> pure l

replaceKeys : Graph e n -> Gen (Maybe (Graph e n))
replaceKeys g = do
    m <- keyMapping (nodes g)
    nlns <- pure $ traverse (nKeyRep m) $ labNodes g
    nens <- pure $ traverse (eKeyRep m) $ labEdges g
    pure $ insEdges <$> nens <*> (flip insNodes empty <$> nlns)

-- Renumbering test suite -----------------------------------------------------

-- Generates a vector of length k with increasing index (exxentially [0..n])
vectN : (k : Nat) -> Vect k Bits64
vectN k = go k 0
  where go : (n : Nat) -> Bits64 -> Vect n Bits64
        go Z     _ = []
        go (S n) s = s :: go n (s + 1)

||| Ensures that the extracted element is not present in the remaining vect
test_extOne : Property
test_extOne = property $ do
  v    <- pure $ vectN 5
  (elem,rem) <- forAll $ extOne v
  True === (isJust (Data.Vect.find ((==) elem) v)
           && isNothing (Data.Vect.find ((==) elem) rem))

||| Ensures, that all keys can be found
test_keyMapping : Property
test_keyMapping = property $ do
  g <- forAll $ graph (linear 1 50) graphDensity'
  m <- forAll $ keyMapping (nodes g)
  isJust (foldMap (\n => Data.BitMap.lookup n m) (nodes g)) === True

-- Properties -----------------------------------------------------------------

matchers : Matchers Char Char Char Char
matchers = MkMatchers (==) (==)

task : (qcs : List (Context Char Char)) -> Graph Char Char
    -> Task (length qcs) Char Char Char Char
task qcs t = MkTask (==) (==) (fromList qcs) t

partial
find_indSearch : Property
find_indSearch = property $ do
  t <- forAll $ graph graphSize graphDensity'
  q <- forAll $ graphDensity >>= flip subGraph t
  True === (isJust $ inductiveSearch matchers q t)

find_ullmann : Property
find_ullmann = property $ do
  t <- forAll $ graph graphSize graphDensity'
  q <- forAll $ graphDensity >>= flip subGraph t
  True === (isJust $ ullmann $ task (contexts q) t)

||| Ensures the successful generation of a renumbered graph
partial
test_graphRenum : Property
test_graphRenum = property $ do
  q <- forAll $ graph graphSize graphDensity'
  t <- forAll $ replaceKeys q
  True === isJust (t >>= inductiveSearch matchers q)

partial
test_renumSubGraph : Property
test_renumSubGraph = property $ do
  t <- forAll $ graph graphSize graphDensity'
  q <- forAll $ graphDensity >>= flip subGraph t >>= replaceKeys
  True === isJust (q >>= flip (inductiveSearch matchers) t)

-- Group ----------------------------------------------------------------------
partial export
props : Group
props = MkGroup "SubGraph Properties"
          [ ("extOne"             , test_extOne)
          , ("key mapping"        ,test_keyMapping)
          , ("inductive Search"   ,find_indSearch)
          , ("ullmann"            ,find_ullmann)
          , ("graph Renumbering"  ,test_graphRenum)
          , ("renumbered Subgraph",test_renumSubGraph)
          ]

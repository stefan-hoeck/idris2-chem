module Test.Data.Isomorphism

import Data.Graph
import Data.SubGraph.InductiveSearch
import Data.SubGraph.Ullmann
import Data.So
import Data.Fin
import Data.Vect
import Test.Data.Graph
import Hedgehog



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

-- Graph generation with specified size and density for
-- the calculation of some statistics (not a range)
-- Workaround: linear 53 53 (min and max the same)


-- SubGraph
boolRatio : Ratio -> Gen Bool
boolRatio d = frequency [(valD d,pure True),(remD d,pure False)]

-- TODO: How to get a random result? traverse?
rndFilt : Ratio -> List a -> Gen (List a)
rndFilt d xs = let prob = boolRatio d
               in pure $ filter (\_ => ?filterRandomValues prob) xs

subGraph : Ratio -> (g : Graph Char Char) -> Gen (Graph Char Char)
subGraph d g = do
   ns <- rndFilt d $ nodes g
   g' <- pure $ delNodes ns g
   es <- rndFilt d $ edges g'
   pure $ delEdges es g'


-- Properties -----------------------------------------------------------------

matchers : Matchers Char Char Char Char
matchers = MkMatchers (==) (==)

find_indSearch : Property
find_indSearch = property $ do
  t <- forAll $ graph graphSize graphDensity'
  q <- forAll $ graphDensity >>= flip subGraph t
  True === (isJust $ inductiveSearch matchers q t)


task : (qcs : List (Context Char Char)) -> Graph Char Char
    -> Task (length qcs) Char Char Char Char
task qcs t = MkTask (==) (==) (fromList qcs) t

find_ullmann : Property
find_ullmann = property $ do
  t <- forAll $ graph graphSize graphDensity'
  q <- forAll $ graphDensity >>= flip subGraph t
  True === (isJust $ ullmann $ task (contexts q) t)

-- Group
export
props : Group
props = MkGroup "SubGraph Properties"
          [ ("inductiveSearch",find_indSearch)
          , ("ullmann        ",find_ullmann)
          ]

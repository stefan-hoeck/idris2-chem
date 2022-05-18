module Test.Data.Isomorphism

import Data.Graph
import Data.SubGraph.InductiveSearch
import Data.So
import Data.Fin
import Data.Vect
import Test.Data.Graph
import Hedgehog


-- Generators -----------------------------------------------------------------

-- Graph size calculation
record Density where
  constructor MkDensity
  val : Fin 101 -- [0,100]

valD : Density -> Nat
valD = finToNat . val

remD : Density -> Nat
remD = minus 100 . valD

multD : Nat -> Density -> Nat
multD k d = (valD d * k) `div` 100



--
graphSize : Gen Nat
graphSize = nat $ linear 1 100

graphDensity : Gen Density
graphDensity = MkDensity <$> fin (linearFin 100)

-- For undirected Graphs
-- TODO: Proof of issuc?
graphStat : (n : Nat) -> Density
         -> (Hedgehog.Range Nat, Hedgehog.Range Nat)
graphStat Z _ = (linear 0 0, linear 0 0)
graphStat (S n) d = let nEmax = ((S n) * n) `div` 2
                        nE    = multD nEmax d
                    in (linear 1 (S n), linear 0 nE)


-- Graph generation
graph : (nNodes : Nat) -> Density
     -> Gen (Graph Char Char)
graph nNodes d = let bond = element ['-','=','#']
                     (rNodes, rEdges) = graphStat nNodes d
                 in lgraph rNodes rEdges bond lower


-- SubGraph generation

probD : Density -> Gen Bool
probD d = frequency [(valD d,pure True),(remD d,pure False)]

-- TODO: How to get a random result? traverse?
rndFilt : Density -> List a -> Gen (List a)
rndFilt d xs = let prob = probD d -- nKeep = multD (length xs) d
               in pure $ filter (\_ => ?filterRandomValues prob) xs

subGraph : Density -> (g : Graph Char Char) -> Gen (Graph Char Char)
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
  t <- forAll $ join $ graph <$> graphSize <*> graphDensity
  q <- forAll $ graphDensity >>= flip subGraph t
  True === (isJust $ inductiveSearch matchers q t)


-- Group
export
props : Group
props = MkGroup "SubGraph Properties"
          [ ("inductiveSearch",find_indSearch)
          ]

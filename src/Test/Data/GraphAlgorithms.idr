module Test.Data.GraphAlgorithms

import Data.Graph.Types
import Data.Graph.GraphAlgorithms

import Text.Smiles
import Hedgehog
import Data.Vect
import Data.List

%default total

--------------------------------------------------------------------------------
--      Generators
--------------------------------------------------------------------------------

Probability : Type
Probability = Nat

probabilities : Gen Probability
probabilities = nat (linear 0 100)
  
-- General Graph building
nodes : (nNodes : Hedgehog.Range Bits64) -> Gen (List Node)
nodes nNodes = map (\n => [1..n]) $ bits64 nNodes  



edges : (nodes: List Node) -> List Edge
edges []        = []
edges (v :: []) = []
edges (v :: vs) = (++) (edges vs) $ mapMaybe (mkEdge v) vs

||| Randomly removes edges from a list of edges
randomEdges : Probability -> List Edge -> Gen (List Edge)
randomEdges p es =
  let ves = Vect.fromList es
      bl  = vect (length es) $ frequency [
             (p          , pure True),
             (minus 100 p, pure False)]
   in map fst . filter snd . toList <$> [| zip (pure ves) bl |]

graph : Gen (Graph () ())
graph = let ns    = nodes (linear 1 20)
            es    = edges <$> ns
            rndEs = join $ randomEdges <$> probabilities <*> es
          in [| mkuGraph ns rndEs |]



-- TODO: Is that about how it could be done?
         -- Should I use generators from the first function?

-- Generation of test graphs using smiles strings
-- Should cover compound types:
--  linear
--  cyclic
--  aromatic
--  disconnected graphs
--  isomeric forms
-- Note: All the following Smiles strings were read successfully! :D
--smilesSelection : Vect 3 String
--smilesSelection = [
--    "CCOCC" -- Diethylether
   --,"C1CCCCC1" -- Cyclohexane
   --,"CC(=CCCC(=CCO)C)C" --Geraniol
--   ,"CC1(C2CCC1(C(=O)C2)C)C" --Camphor
   --,"C1COCCC1N2CCNCC2" -- 1-(Oxan-4-yl)piperazine
   --,"[NH4+].[NH4+].Cl[Cu-2](Cl)(Cl)Cl" --Ammonium cupric chloride
   --,"C1=CC=C2C(=C1)C(=CN2)CC(C(=O)O)N" -- Tryptohpane
--   ,"C1CN2CC3=CCOC4CC(=O)N5C6C4C3CC2C61C7=CC=CC=C75" --Strychnine
   --,"C1CN2CC3=CCO[C@H]4CC(=O)N5[C@H]6[C@H]4[C@H]3C[C@H]2[C@@]61C7=CC=CC=C75" -- Isomeric form
   --,"COc1ccc(CN2C(=O)c3ccc4c5ccc6C(=O)N(Cc7ccc(OC)cc7)C(=O)c8ccc(c9ccc(C2=O)c3c49)c5c68)cc1" --CAS 83524-75-8
--   ]

--graphs : Vect 3 (Graph Bond Atom) 
--graphs = map (escRes . parse) smilesSelection
  --where
  --  escRes : Result -> Graph Bond Atom
  --  escRes (End result) = result 
  --  escRes (Stuck _ _) = empty


--partial export
--showAlgoResults : IO ()
--showAlgoResults = do
--  putStrLn "Result visualization of Graph algorithms (wip)"
--  putStrLn "DFS"
--  putStrLn $ show $ map (\g => dfs (nodes g) g) graphs
--  putStrLn "BFS"
--  putStrLn $ show $ map (\g => bfs (nodes g) g) graphs


-- TODO: How to write a property test?
--prop_dfs : Property






-- Function to test wether the smiles reading failed somewhere
--export
--testSmilesReading : IO ()
--testSmilesReading = putStrLn $ show $ any isEmpty $ graphs 

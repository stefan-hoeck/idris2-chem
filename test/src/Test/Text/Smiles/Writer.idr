module Test.Text.Smiles.Writer

import Hedgehog

import Text.Smiles.Types
import Text.Smiles.Writer
import Text.Smiles.Parser
import Text.Molfile.Types
import Text.ParseError

import Data.String
import Data.Graph.Indexed.Query.Subgraph
import Data.Graph.Indexed.Util as GU

import Test.Data.Graph.Generators
import Test.Text.Smiles.Generators

import System.File

import Chem

%default total

smilesTests : List String
smilesTests =
  [ "CC"
  , "[Cu+2].[O-]S(=O)(=O)[O-]"
  , "C1C(C2C(C3C(C4C(C5C(C6C(C7C(C8C(C9C(C%10C(CC)C%10C)C9C)C8C)C7C)C6C)C5C)C4C)C3C)C2C)C1"
  , "C12CC1C2"
  ]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------
propSmilesRoundtrip : Property
propSmilesRoundtrip = property1 $
  traverse_ (\s => smilesRoundtrip s === s) smilesTests

propSmilesRoundtripNotEqual : Property
propSmilesRoundtripNotEqual = property1 $
  traverse_ (\s => smilesRoundtrip s /== "This should fail") smilesTests

covering
graphsRoundtripOk : String -> ChemRes [SmilesParseErr] Bool
graphsRoundtripOk s = do
  G o1 g1 <- readSmiles s
  G o2 g2 <- readSmiles (smilesRoundtrip s)
  pure $ isJust (query (==) (==) g1 g2)
                && (o1 == o2)
                && (GU.size g1 == GU.size g2)

covering
testNodes : List String -> Property
testNodes ls = property1 $
  traverse_ (\(n, s) =>
    case graphsRoundtripOk s of
         Left _      => do
           footnote "failed to read Smiles: {s}"
           failure
         Right True  => success
         Right False => do
           footnote "Line: \{show n}"
           footnote "SMILES:    \{s}"
           footnote "Roundtrip: \{smilesRoundtrip s}"
           failure
             ) (zip [1..(length ls)] ls)

covering
testNodesMini : Property
testNodesMini = testNodes smilesTests

covering
loadZinc : IO (List String)
loadZinc = do
  Right content <- readFile "resources/zinc.txt"
    | Left err => do
        printLn err
        pure []

  pure (map trim (lines content))

covering
testNodesZincIO : IO Property
testNodesZincIO = do
  zinc <- loadZinc
  pure (testNodes zinc)

genGraph : Gen (Graph SmilesBond SmilesAtom)
genGraph = lgraph (linear 1 50) (linear 0 80) bond atom

covering
testNodesGen : Property
testNodesGen = property $ do
  G _ g1 <- forAll genGraph
  let s = graphToSmiles g1
  case graphsRoundtripOk s of
    Left _      => do
                   footnote "failed to read Smiles: \{s}"
                   failure
    Right True  => success
    Right False => do
                   footnote "SMILES: \{s}"
                   failure

-- The code does not produce canonical smiles code which is why we get
-- errors like this one occasionaly from testNodesGen.

-- 1.
-- ━━━ Failed (- lhs) (+ rhs) ━━━
-- - "\"C=1CC=1=1CC=1.C\""
-- + "\"C1CC=11CC=1.C\""

-- Both have the same graph.
-- Text.Smiles.Writer> :exec printLn $ readSmiles' "C1CC=11CC=1.C"
-- Right (G 6 (mkGraph [SubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom
-- = False}, SubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom = False}, S
-- ubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom = False}] [E 0 1 Sngl,
--  E 0 2 Dbl, E 1 2 Sngl, E 2 3 Sngl, E 2 4 Dbl, E 3 4 Sngl]))

-- Text.Smiles.Writer> :exec printLn $ readSmiles' "C=1CC=1=1CC=1.C"
-- Right (G 6 (mkGraph [SubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom
-- = False}, SubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom = False}, S
-- ubsetAtom {elem = C, arom = False}, SubsetAtom {elem = C, arom = False}] [E 0 1 Sngl,
--  E 0 2 Dbl, E 1 2 Sngl, E 2 3 Sngl, E 2 4 Dbl, E 3 4 Sngl]))

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

covering
export
propsIO : IO Group
propsIO = do
  zincProp <- testNodesZincIO
  pure $ MkGroup "Text.Smiles.Writer"
    [ ("propSmilesRoundtrip", propSmilesRoundtrip)
    , ("propSmilesRoundtripNotEqual", propSmilesRoundtripNotEqual)
    , ("testNodesMini", testNodesMini)
    , ("testNodesZinc", zincProp)
    , ("testNodesGen", testNodesGen)
    ]


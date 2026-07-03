module Test.Text.Smiles.Writer

import Chem

import Data.String
import Data.Graph.Indexed.Util as GU
import Data.Graph.Indexed.Query.Subgraph

import Hedgehog

import System.File

import Test.Data.Graph.Generators
import Test.Text.Smiles.Generators

import Text.Molfile.Types
import Text.ParseError
import Text.Smiles.Parser
import Text.Smiles.Writer
import Text.Smiles.Types

%default total

--------------------------------------------------------------------------------
--          Test data
--------------------------------------------------------------------------------

||| A short list of (smiles) strings, that is useful for testing and debugging
smilesTests : List String
smilesTests =
  [ "CC"
  , "[Cu+2].[O-]S(=O)(=O)[O-]"
  , "C1C(C2C(C3C(C4C(C5C(C6C(C7C(C8C(C9C(C%10C(CC)C%10C)C9C)C8C)C7C)C6C)C5C)C4C)C3C)C2C)C1"
  , "C12CC1C2"
  ]

covering
loadZinc : IO (List String)
loadZinc = do
  Right content <- readFile "resources/zinc.txt"
    | Left err => do
        printLn err
        pure []

  pure (map trim (lines content))

genGraph : Gen (Graph SmilesBond SmilesAtom)
genGraph = lgraph (linear 1 50) (linear 0 80) bond atom

--------------------------------------------------------------------------------
--          Helpers
--------------------------------------------------------------------------------

||| Checks if converting a SMILES string into a graph yields an equivalent
||| graph as when converting to graph, then back to SMILES string
||| and then back to graph again.
covering
sameGraphAfterRoundtrip : String -> ChemRes [SmilesParseErr] Bool
sameGraphAfterRoundtrip s = do
  G o1 g1 <- readSmiles s
  G o2 g2 <- readSmiles (smilesRoundtrip s)
  pure $ isJust (query (==) (==) g1 g2)
                && (o1 == o2)
                && (GU.size g1 == GU.size g2)

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
testRoundtrips : List String -> Property
testRoundtrips ls = property1 $
  traverse_ (\(n, s) =>
    case sameGraphAfterRoundtrip s of
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
testRoundtripsMini : Property
testRoundtripsMini = testRoundtrips smilesTests

covering
testRoundtripsZincIO : IO Property
testRoundtripsZincIO = do
  zinc <- loadZinc
  pure (testRoundtrips zinc)

covering
testRoundtripsGen : Property
testRoundtripsGen = property $ do
  G _ g1 <- forAll genGraph
  let s = graphToSmiles g1
  case sameGraphAfterRoundtrip s of
    Left _      => do
                   footnote "failed to read Smiles: \{s}"
                   failure
    Right True  => success
    Right False => do
                   footnote "SMILES: \{s}"
                   failure

-- The function renderForest does not produce canonical SMILES. Consequently,
-- testRoundtripsGen may occasionally report different SMILES strings that
-- so far seem to represent the same graph.

-- Example:
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
  zincProp <- testRoundtripsZincIO
  pure $ MkGroup "Text.Smiles.Writer"
    [ ("propSmilesRoundtrip",         propSmilesRoundtrip)
    , ("propSmilesRoundtripNotEqual", propSmilesRoundtripNotEqual)
    , ("testRoundtripsMini",          testRoundtripsMini)
    , ("testRoundtripsZinc",          zincProp)
    , ("testRoundtripsGen",           testRoundtripsGen)
    ]


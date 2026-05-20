module Test.Text.Smiles.Writer

import Hedgehog

import Text.Smiles.Types
import Text.Smiles.Writer
import Text.Smiles.Parser
import Text.Molfile.Types
import Text.ParseError

import Data.Graph.Indexed.Query.Subgraph
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Util
import Data.Tree

import System.File

import Text.ILex
import Profile
import Chem
import Data.List.Quantifiers.Extra
import Data.String
import Text.Smiles


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

indexList : List a -> List (Nat, a)
indexList xs = go 1 xs
  where
    go : Nat -> List a -> List (Nat, a)
    go _ [] = []
    go n (x :: xs) = (n, x) :: go (n + 1) xs

covering
testNodes : List String -> Property
testNodes ls = property1 $
  traverse_ (\(n, s) =>
    let
        expected : ChemRes [SmilesParseErr] (Maybe (List Nat))
        expected = do
          G _ g0 <- readSmiles s
          pure $ Just $ map finToNat (nodes g0)

        actual : ChemRes [SmilesParseErr] (Maybe (List Nat))
        actual = do
          G _ g1 <- readSmiles s
          G _ g2 <- readSmiles (smilesRoundtrip s)
          pure $ toList . map finToNat <$> query (==) (==) g1 g2
    in do
      footnote "Line: \{show n}"
      footnote "SMILES:    \{s}"
      footnote "Roundtrip: \{smilesRoundtrip s}"
      actual === expected
  ) (indexList ls)

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
zincData : List String
zincData = unsafePerformIO loadZinc

-- Currently line 80 in zinc.txt gives an error
-- sadly i have not yet figured out how to show only the smiles string that
-- failed
-- Also, it crashes when too many entries are chosen..
covering
testNodesZinc : Property
testNodesZinc = testNodes $ take 81 zincData


--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

covering
export
props : Group
props =
  MkGroup "Text.Smiles.Writer"
    [ ("propSmilesRoundtrip", propSmilesRoundtrip)
    , ("testNodesMini", testNodesMini)
    , ("testNodesZinc", testNodesZinc)
    ]



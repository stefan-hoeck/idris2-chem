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
    in if actual == expected then
          success
       else do
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


-- After scrolling through the errors of the first 10'000 entries of zinc.txt
-- there seem to be 2 kinds of errors; although when converted to structures
-- they appear to be the same molecules:

-- 1.
-- Roundtrip: CC(=O)Nc1c2sscc2n(c1=O)C
-- SMILES:    CC(=O)Nc1c-2sscc2n(c1=O)C
-- Line: 80

-- caused by:
-- Text.Smiles.Writer> :exec printLn $ readSmiles' "CC(=O)Nc1c2sscc2n(c1=O)C"
-- E 5 9 Arom
-- VS
-- Text.Smiles.Writer> :exec printLn $ readSmiles' "CC(=O)Nc1c-2sscc2n(c1=O)C"
-- E 5 9 Sngl

-- 2.
-- Roundtrip: [H]/N=c1/n(c(c(s1)C(C)(C)C)C)C
-- SMILES:    [H]/N=c\1/n(c(c(s1)C(C)(C)C)C)C
-- Line: 1838

-- caused by?
-- Interestingly I can't get this to run in the repl, but in the test
-- this must have worked since we got the output above.
-- Text.Smiles.Writer> :exec printLn $ readSmiles' "[H]/N=c\1/n(c(c(s1)C(C)(C)C)C)C"
--                     :exec printLn $ readSmiles' "[H]/N=c\1/n(c(c(s1)C(C)(C)C)C)C"
-- Left "Error: Unexpected '\\SOH'\n\nvirtual: 1:8--1:9\n 1 | [H]/N=c\SOH/n(c(c(s1)C(C)(C)C)C)C\n            ^\n"

covering
testNodesZinc : Property
testNodesZinc = testNodes $ zincData


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



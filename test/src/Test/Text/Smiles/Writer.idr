module Test.Text.Smiles.Writer

import Text.Smiles.Types
import Text.Molfile.Types
import Text.Smiles.Writer
import Text.Smiles.Parser
import Hedgehog
import Data.Graph.Indexed.Query.Subgraph
import Data.Graph.Indexed.Query.DFS
import Data.Tree
import Data.Graph.Indexed.Util


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

covering
testQuery : Property
testQuery = property1 $
  traverse_ (\s =>
    case readSmiles' s of
      Left _ => success
      Right (G _ g1) =>
        let expected = Just $ (map finToNat (nodes g1))
            actual =
              case readSmiles' (smilesRoundtrip s) of
                Left _ => Nothing
                Right (G _ g2) =>
                  toList . map finToNat <$> query (==) (==) g1 g2
        in actual === expected
  ) smilesTests

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

covering
export
props : Group
props =
  MkGroup "Text.Smiles.Writer"
    [ ("propSmilesRoundtrip", propSmilesRoundtrip)
    , ("testQuery", testQuery)]


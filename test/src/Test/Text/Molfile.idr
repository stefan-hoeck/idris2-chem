module Test.Text.Molfile

import Text.Molfile
import Text.Molfile.SDF
import Text.Molfile.Reader.Util
import Test.Text.Molfile.Examples
import Test.Text.Molfile.Generators

%default total


--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

rw :  Eq a => Show a => Gen a -> Parser a -> (a -> String) -> Property
rw gen tok wt = property $ do
  v <- forAll gen
  let str : String
      str = wt v

  footnote ("Encoded: " ++ str)

  lineTok tok (0,str) === Right v

propRead : String -> Property
propRead s = property1 $ case readMol {es = [MolParseErr]} s of
  Right v         => pure ()
  Left (Here err) => failWith Nothing "\{err}"

prop_readRoundTrip : Property
prop_readRoundTrip = property $ do
  m <- forAll molFile
  let s := writeMolfile m

  footnote "Encoded:\n\{s}"

  Right m === readMol {es = [MolParseErr]} s

prop_sdfRoundTrip : Property
prop_sdfRoundTrip = property $ do
  sdfs <- forAll (list (linear 1 10) sdFile)
  let s := writeSDF sdfs

  footnote "Encoded:\n\{s}"

  Right sdfs === readSDF {es = [MolParseErr]} s

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_count", rw counts counts counts)
  , ("prop_atom",  rw simpleAtom atom atom)
  , ("prop_bond",  rw bondEdge bond bond)
  , ("prop_sg1",   propRead sg1)
  , ("prop_readRoundTrip", prop_readRoundTrip)
  , ("prop_sdfRoundTrip", prop_sdfRoundTrip)
  ]

module Test.Text.Molfile

import Text.Molfile
import Text.ParseError
import Test.Text.Molfile.Examples
import Test.Text.Molfile.Generators

%default total


--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

propRead : String -> Property
propRead s = property1 $ case readMol {es = [ParseError MolErr]} s of
  Right v         => pure ()
  Left (Here err) => failWith Nothing "\{err}"

prop_readRoundTrip : Property
prop_readRoundTrip = property $ do
  m <- forAll molFile
  let s := writeMolfile m

  footnote "Encoded:\n\{s}"

  Right m === readMol {es = [ParseError MolErr]} s

prop_sdfRoundTrip : Property
prop_sdfRoundTrip = property $ do
  sdfs <- forAll (list (linear 1 10) sdFile)
  let s := writeSDF sdfs

  footnote "Encoded:\n\{s}"

  Right sdfs === readSDF {es = [ParseError MolErr]} s

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_sg1",   propRead sg1)
  , ("prop_readRoundTrip", prop_readRoundTrip)
  , ("prop_sdfRoundTrip", prop_sdfRoundTrip)
  ]

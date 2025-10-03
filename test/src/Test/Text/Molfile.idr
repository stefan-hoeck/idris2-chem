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

  case readMol {es = [ParseError MolErr]} s of
    Left (Here x) => failWith Nothing "\{x}"
    Right res     => m === res

prop_readRoundTrip3000 : Property
prop_readRoundTrip3000 = property $ do
  m <- forAll (molFileGS [])
  let s := writeMolfile {version = V3000} m

  footnote "Encoded:\n\{s}"

  case readMol {es = [ParseError MolErr]} s of
    Left (Here x) => failWith Nothing "\{x}"
    Right res     => m === res

prop_sdfRoundTrip : Property
prop_sdfRoundTrip = property $ do
  sdfs <- forAll (list (linear 1 10) sdFile)
  let s := writeSDF sdfs

  footnote "Encoded:\n\{s}"

  case readSDF {es = [ParseError MolErr]} s of
    Left (Here x) => failWith Nothing "\{x}"
    Right res     => sdfs === res

prop_sdfRoundTrip3000 : Property
prop_sdfRoundTrip3000 = property $ do
  sdfs <- forAll (list (linear 1 10) (sdFileGS []))
  let s := writeSDF {version = V3000} sdfs

  footnote "Encoded:\n\{s}"

  case readSDF {es = [ParseError MolErr]} s of
    Left (Here x) => failWith Nothing "\{x}"
    Right res     => sdfs === res

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_sg1",   propRead sg1)
  , ("prop_readRoundTrip", prop_readRoundTrip)
  , ("prop_readRoundTrip3000", prop_readRoundTrip3000)
  , ("prop_sdfRoundTrip", prop_sdfRoundTrip)
  , ("prop_sdfRoundTrip3000", prop_sdfRoundTrip3000)
  ]

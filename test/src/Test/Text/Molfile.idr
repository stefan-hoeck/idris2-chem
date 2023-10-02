module Test.Text.Molfile

import Test.Text.Molfile.Examples
import Test.Text.Molfile.Generators
import Text.Parse.Manual

%default total


--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------
--
rw :  Eq a
   => Show a
   => Gen a
   -> (tok   : Tok b MolFileError a)
   -> (write : a -> String)
   -> Hedgehog.Property
rw gen tok wt = property $ do
  v <- forAll gen
  let str : String
      str = wt v

  footnote ("Encoded: " ++ str)

  lineTok 0 tok str === Right v

propRead : String -> Property
propRead s = property1 $ case readMol {es = [MolParseErr]} Virtual s of
  Right v         => pure ()
  Left (Here err) => failWith Nothing "\{err}"

propReadRoundTrip : Property
propReadRoundTrip = property $ do
  m <- forAll molFile
  Right m === readMol {es = [MolParseErr]} Virtual (writeMolfile m)

export
props : Group
props = MkGroup "Molfile Properties"
  [ ("prop_count", rw counts counts counts)
  , ("prop_atom",  rw atom atom atom)
  , ("prop_bond",  rw bondEdge bond bond)
  , ("prop_sg1",   propRead sg1)
  ]

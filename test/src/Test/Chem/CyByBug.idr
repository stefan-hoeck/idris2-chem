module Test.Chem.CyByBug

import Chem
import Chem.Aromaticity
import Chem.Query
import Text.Molfile
import Hedgehog

%default total

0 Grph : Type
Grph = Graph MolBond MolAtomAT

readGrph : String -> Either String Grph
readGrph s =
  case readMol {es = [MolParseErr]} s of
    Left (Here err) => Left "\{err}"
    Right g         => Right $ perceiveMolAtomTypes g.graph

qry, tgt : String

qgrph, tgrph : Either String Grph
qgrph = readGrph qry

tgrph = readGrph tgt

match : (q,t : Either String Grph) -> Either String (Maybe (List Nat))
match q t = do
  qg <- q
  tg <- t
  pure $ Query.substructure (molQuery qg) (molTarget tg)

prop_bug : Property
prop_bug = property1 $ match qgrph tgrph === Right Nothing

export
props : Group
props =
  MkGroup "CyByBug"
    [("prop_bug", prop_bug)]
--------------------------------------------------------------------------------
--  Molfiles
--------------------------------------------------------------------------------

qry =
  """

  Created by CyBy2

    6  6     0                      V2000
    -10.2774   10.3246    0.0000   C
     -9.1948   10.9495    0.0000   C
     -9.6524    9.2420    0.0000   N
     -8.5698    9.8670    0.0000   C
     -8.8712   12.1568    0.0000   C
     -9.9759    8.0346    0.0000   C
    1  2  1  0
    1  3  1  0
    2  4  1  0
    2  5  1  0
    3  4  1  0
    3  6  1  0
  M  END
  """

tgt =
  """

    CDK

   20 22  0  0  0  0  0  0  0  0999 V2000
      2.4577   -3.0809    0.0000 O   0  0  0  0  0  0  0  0  0  0  0  0
      1.4185   -1.9992    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -0.0379   -2.3584    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -0.4550   -3.7992    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -1.9114   -4.1584    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -2.3283   -5.6002    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -3.7846   -5.9594    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -4.8241   -4.8768    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -4.4072   -3.4350    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
     -2.9508   -3.0758    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      1.8356   -0.5584    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
      1.1116    0.7557    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      2.4256    1.4797    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      3.1496    0.1656    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      4.5905   -0.2515    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      5.6724    0.7887    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      7.1132    0.3716    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      7.4721   -1.0857    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      6.3902   -2.1259    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
      4.9494   -1.7088    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    1  2  2  0  0  0  0
    2  3  1  0  0  0  0
    3  4  1  0  0  0  0
    4  5  1  0  0  0  0
    5  6  2  0  0  0  0
    6  7  1  0  0  0  0
    7  8  2  0  0  0  0
    8  9  1  0  0  0  0
    9 10  2  0  0  0  0
    5 10  1  0  0  0  0
    2 11  1  0  0  0  0
   11 12  1  0  0  0  0
   12 13  1  0  0  0  0
   13 14  1  0  0  0  0
   11 14  1  0  0  0  0
   14 15  1  0  0  0  0
   15 16  2  0  0  0  0
   16 17  1  0  0  0  0
   17 18  2  0  0  0  0
   18 19  1  0  0  0  0
   19 20  2  0  0  0  0
   15 20  1  0  0  0  0
  M  END
  """

module Test.Chem.Aromaticity

import Chem
import Chem.Aromaticity
import Text.Smiles
import Text.Smiles.AtomType
import Hedgehog

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

toSB : AromBond SmilesBond -> SmilesBond
toSB ab = if ab.arom then Arom else if ab.type == Arom then Sngl else ab.type

readArom : String -> Either String (Graph SmilesBond SmilesAtomAT)
readArom =
  map (mapFst toSB . aromatize atomType . perceiveSmilesAtomTypes) . readSmiles'

triples : Graph e n -> List (Nat,Nat,e)
triples (G o g) = (\(E x y l) => (finToNat x, finToNat y, l)) <$> edges g 

testArom : String -> List (Nat,Nat,SmilesBond) -> Property
testArom s ts = property1 $ map triples (readArom s) === Right ts

--------------------------------------------------------------------------------
-- One-cycle aromatic systems
--------------------------------------------------------------------------------

prop_benzene : Property
prop_benzene =
  testArom "C1C=CC=CC=1"
    [(0,1,Arom),(0,5,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom),(4,5,Arom)]

-- cyclopropenyl cation
prop_cyprop : Property
prop_cyprop =
  testArom "[CH+]1C=C1"
    [(0,1,Arom),(0,2,Arom),(1,2,Arom)]

-- cyclopentadienyl anyion
prop_cypent : Property
prop_cypent =
  testArom "[CH-]1C=CC=C1"
    [(0,1,Arom),(0,4,Arom),(1,2,Arom), (2,3,Arom), (3,4,Arom)]

prop_pyridine : Property
prop_pyridine =
  testArom "C1C=NC=CC=1"
    [(0,1,Arom),(0,5,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom),(4,5,Arom)]

prop_pyrrole : Property
prop_pyrrole =
  testArom "[NH]1C=CC=C1"
    [(0,1,Arom),(0,4,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom)]

prop_imidazole : Property
prop_imidazole =
  testArom "[NH]1C=NC=C1"
    [(0,1,Arom),(0,4,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom)]

prop_furan : Property
prop_furan =
  testArom "O1C=CC=C1"
    [(0,1,Arom),(0,4,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom)]

prop_thiofuran : Property
prop_thiofuran =
  testArom "S1C=CC=C1"
    [(0,1,Arom),(0,4,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom)]

prop_cycloheptane : Property
prop_cycloheptane =
  testArom "[CH+]1C=CC=CC=C1"
    [(0,1,Arom),(0,6,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom),(4,5,Arom),(5,6,Arom)]

prop_borocycloheptane : Property
prop_borocycloheptane =
  testArom "B1C=CC=CC=C1"
    [(0,1,Arom),(0,6,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom),(4,5,Arom),(5,6,Arom)]

--------------------------------------------------------------------------------
-- Bi- and tricyclic aromats
--------------------------------------------------------------------------------

prop_naphthalene : Property
prop_naphthalene =
  testArom "C=1C=C2C=CC=CC2=CC=1"
    [ (0,1,Arom),(0,9,Arom),(1,2,Arom),(2,3,Arom),(2,7,Arom),(3,4,Arom)
    , (4,5,Arom),(5,6,Arom),(6,7,Arom),(7,8,Arom),(8,9,Arom)
    ]

prop_anthracene : Property
prop_anthracene =
  testArom "C=1C=C2C=C3C=CC=CC3=CC2=CC=1"
    [ (0,1,Arom),(0,13,Arom),(1,2,Arom),(2,3,Arom),(2,11,Arom),(3,4,Arom)
    , (4,5,Arom),(4,9,Arom), (5,6,Arom),(6,7,Arom),(7,8,Arom),(8,9,Arom)
    , (9,10,Arom), (10,11,Arom), (11,12,Arom), (12,13,Arom)
    ]

prop_indole : Property
prop_indole =
  testArom "C12C=CC=CC=1NC=C2"
    [ (0,1,Arom),(0,5,Arom),(0,8,Arom),(1,2,Arom),(2,3,Arom),(3,4,Arom)
    , (4,5,Arom),(5,6,Arom),(6,7,Arom),(7,8,Arom)
    ]

--------------------------------------------------------------------------------
-- Anti-aromats
--------------------------------------------------------------------------------

-- cyclopropenyl anion
prop_cyprop_min : Property
prop_cyprop_min =
  testArom "[CH-]1C=C1"
    [(0,1,Sngl),(0,2,Sngl),(1,2,Dbl)]

prop_cybutadien : Property
prop_cybutadien =
  testArom "C1C=CC=1"
    [(0,1,Sngl),(0,3,Dbl),(1,2,Dbl),(2,3,Sngl)]

prop_dioxa : Property
prop_dioxa =
  testArom "O1C=COC=C1"
    [(0,1,Sngl),(0,5,Sngl),(1,2,Dbl),(2,3,Sngl),(3,4,Sngl),(4,5,Dbl)]

prop_cyclooctatetraen : Property
prop_cyclooctatetraen =
  testArom "C1C=CC=CC=CC=1"
    [(0,1,Sngl),(0,7,Dbl),(1,2,Dbl),(2,3,Sngl),(3,4,Dbl),(4,5,Sngl),(5,6,Dbl),(6,7,Sngl)]

prop_cycloheptane_anion : Property
prop_cycloheptane_anion =
  testArom "[CH-]1C=CC=CC=C1"
    [(0,1,Sngl),(0,6,Sngl),(1,2,Dbl),(2,3,Sngl),(3,4,Dbl),(4,5,Sngl),(5,6,Dbl)]

--------------------------------------------------------------------------------
-- Not aromatic molecules
--------------------------------------------------------------------------------

prop_cyclohexane : Property
prop_cyclohexane =
  testArom "C1CCCCC1"
    [(0,1,Sngl),(0,5,Sngl),(1,2,Sngl),(2,3,Sngl),(3,4,Sngl),(4,5,Sngl)]

prop_piperidine : Property
prop_piperidine =
  testArom "C1CNCCC1"
    [(0,1,Sngl),(0,5,Sngl),(1,2,Sngl),(2,3,Sngl),(3,4,Sngl),(4,5,Sngl)]

--------------------------------------------------------------------------------
-- props
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "Aromaticity"
    [ ("prop_benzene", prop_benzene)
    , ("prop_cyprop", prop_cyprop)
    , ("prop_cypent", prop_cypent)
    , ("prop_pyridine", prop_pyridine)
    , ("prop_pyrrole", prop_pyrrole)
    , ("prop_furan", prop_furan)
    , ("prop_thiofuran", prop_thiofuran)
    , ("prop_imidazole", prop_imidazole)
    , ("prop_naphthalene", prop_naphthalene)
    , ("prop_anthracene", prop_anthracene)
    , ("prop_indole", prop_indole)
    , ("prop_borocycloheptane", prop_borocycloheptane)
    , ("prop_cycloheptane", prop_cycloheptane)

    , ("prop_cyprop_min", prop_cyprop_min)
    , ("prop_cybutadien", prop_cybutadien)
    , ("prop_dioxa", prop_dioxa)
    , ("prop_cyclooctatetraen", prop_cyclooctatetraen)
    , ("prop_cycloheptane_anion", prop_cycloheptane_anion)

    , ("prop_cyclohexane", prop_cyclohexane)
    , ("prop_piperidine", prop_piperidine)
    ]

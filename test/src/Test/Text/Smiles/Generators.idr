module Test.Text.Smiles.Generators

import public Chem
import public Data.Vect
import public Hedgehog
import public Test.Chem.Element
import public Test.Chem.Isotope
import public Test.Chem.Types
import public Text.Smiles

%default total

export
chirality : Gen Chirality
chirality = frequency
  [ (5, pure None)
  , (1, element [CW, CCW, TH1, TH2, AL1, AL2, SP1, SP2, SP3])
  , (1, maybe None TB . refineTBIx <$> bits8 (linear 1 20))
  , (1, maybe None OH . refineOHIx <$> bits8 (linear 1 20))
  ]

export
subset : Gen SmilesAtom
subset = element
  [ SubsetAtom C False
  , SubsetAtom B False
  , SubsetAtom N False
  , SubsetAtom O False
  , SubsetAtom P False
  , SubsetAtom S False
  , SubsetAtom F False
  , SubsetAtom Cl False
  , SubsetAtom Br False
  , SubsetAtom I False
  , SubsetAtom B True
  , SubsetAtom C True
  , SubsetAtom N True
  , SubsetAtom O True
  , SubsetAtom P True
  , SubsetAtom S True
  ]

export
hcount : Gen HCount
hcount = fromMaybe 0 . refineHCount <$> bits8 (linear 0 9)

export
atom : Gen SmilesAtom
atom = frequency
  [ (1, subset)
  , (5, Prelude.[| bracket aromIsotope chirality hcount charge |])
  ]

export
bond : Gen SmilesBond
bond = element [Sngl,Dbl,Trpl,Quad,Arom,FW,BW]

export
ringNr : Gen RingNr
ringNr = fromMaybe 0 . refineRingNr <$> bits8 (linear 0 99)

export
ring : Gen Ring
ring = [| R ringNr (maybe bond) |]

export
atomToken : Gen SmilesToken
atomToken = [| TA atom (([<] <><) <$> list (linear 0 3) ring) |]

export
token : Gen SmilesToken
token = frequency
  [ (5, atomToken)
  , (3, TB <$> bond)
  , (1, element [PO, PC, Dot])
  ]

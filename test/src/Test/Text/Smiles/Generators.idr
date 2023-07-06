module Test.Text.Smiles.Generators

import public Chem
import public Data.Vect
import public Hedgehog
import public Test.Chem.Element
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
subset : Gen Atom
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

ve : Atom -> ValidElem
ve (SubsetAtom elem arom)      = VE elem arom
ve (Bracket _ elem arom _ _ _) = VE elem arom

el : Elem -> ValidElem
el e = VE e False

export
validElem : Gen ValidElem
validElem = frequency
  [ (7, map el element)
  , (1, element [VE Se True, VE As True])
  , (3, map ve subset)
  ]

export
hcount : Gen HCount
hcount = fromMaybe 0 . refineHCount <$> bits8 (linear 0 9)

export
atom : Gen Atom
atom = frequency
  [ (1, subset)
  , (5, [| bracket (maybe massNr) validElem chirality hcount charge |])
  ]

export
bond : Gen Bond
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

module Test.Text.Smiles.Generators

import Chem.Element
import Chem.Types
import Data.Vect
import Test.Chem.Element
import Test.Chem.Types
import public Hedgehog
import public Text.Smiles.Lexer
import public Text.Smiles.Types

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
  [ SubsetAtom B False
  , SubsetAtom C False
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
  [ (5, [| bracket (maybe massNr) validElem chirality hcount charge |])
  , (1, subset)
  ]

export
bond : Gen Bond
bond = element [Sngl,Dbl,Trpl,Quad,Arom]

export
ringNr : Gen RingNr
ringNr = fromMaybe 0 . refineRingNr <$> bits8 (linear 0 99)

export
token : Gen SmilesToken
token = frequency
  [ (5, TAtom <$> atom)
  , (3, TBond <$> bond)
  , (1, TRing <$> ringNr)
  , (1, element [PO, PC, UB, DB, Dot])
  ]

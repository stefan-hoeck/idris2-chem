module Test.Chem.Generators

import public Chem
import public Hedgehog

import Data.Maybe
import Data.Vect

%default total

export
atomicNr : Gen AtomicNr
atomicNr = fromMaybe 1 . refineAtomicNr <$> bits8 (linear 1 118)

export
massNr : Gen MassNr
massNr = fromMaybe 1 . refineMassNr <$> bits16 (linear 1 511)

export
abundance : Gen Abundance
abundance =
  fromMaybe 1.0 . refineAbundance <$> double (linear MinAbundanceValue 1.0)

export
molecularMass : Gen MolecularMass
molecularMass =
  fromMaybe 1.0 . refineMolecularMass <$> double (linear 0 MaxMolecularMass)

export
molarMass : Gen MolarMass
molarMass =
  fromMaybe 1.0 . refineMolarMass <$> double (linear 0 MaxMolecularMass)

export
charge : Gen Charge
charge = fromMaybe 0 . refineCharge <$> int8 (linearFrom 0 (-15) 15)

export
radical : Gen Radical
radical = element [NoRadical, Singlet, Doublet, Triplet]

export
elem : Gen Elem
elem = fromAtomicNr <$> atomicNr

export
aromElem : Gen AromElem
aromElem =
  choice
    [ (\e => MkAE e False) <$> elem
    , element
        [ MkAE C True
        , MkAE B True
        , MkAE N True
        , MkAE O True
        , MkAE P True
        , MkAE S True
        , MkAE Se True
        , MkAE As True
        ]
    ]

export
formula : Gen Formula
formula =
  foldMap (uncurry singleton) <$>
  list (linear 0 20) [| MkPair elem (nat $ linear 0 20) |]

export
isotope : Gen Isotope
isotope = [| MkI elem (maybe massNr) |]

export
aromIsotope : Gen AromIsotope
aromIsotope = [| mkAI aromElem (maybe massNr) |]
  where
    mkAI : AromElem -> Maybe MassNr -> AromIsotope
    mkAI (MkAE e a) m = MkAI e m a

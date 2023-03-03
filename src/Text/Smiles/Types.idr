module Text.Smiles.Types

-- import Chem.Element
-- import Chem.Types
-- import Data.Refined
-- import Derive.Prelude
-- import Language.Reflection.Refined
-- import Text.RW
-- import public Data.Graph
--
-- --------------------------------------------------------------------------------
-- --          Pragmas
-- --------------------------------------------------------------------------------
--
-- %default total
--
-- %language ElabReflection
--
-- --------------------------------------------------------------------------------
-- --          Chirality
-- --------------------------------------------------------------------------------
--
-- public export
-- record TBIx where
--   constructor MkTBIx
--   value : Bits8
--   0 prf : So (1 <= value && value <= 20)
--
-- %runElab rwInt "TBIx" `(Bits8)
--
-- public export
-- record OHIx where
--   constructor MkOHIx
--   value : Bits8
--   0 prf : So (1 <= value && value <= 20)
--
-- %runElab rwInt "OHIx" `(Bits8)
--
-- public export
-- data Chirality =
--   None | CW | CCW | TH1 | TH2 | AL1 | AL2 | SP1 | SP2 | SP3 | TB TBIx | OH OHIx
--
-- %runElab derive "Chirality" [Ord,Eq,Show]
--
-- --------------------------------------------------------------------------------
-- --          Atoms
-- --------------------------------------------------------------------------------
-- public export
-- data ValidSubset : Elem -> Bool -> Type where
--   VB  : ValidSubset B b
--   VC  : ValidSubset C b
--   VN  : ValidSubset N b
--   VO  : ValidSubset O b
--   VF  : ValidSubset F False
--   VP  : ValidSubset P b
--   VS  : ValidSubset S b
--   VCl : ValidSubset Cl False
--   VBr : ValidSubset Br False
--   VI  : ValidSubset I False
--
-- public export
-- data Atom : Type where
--   SubsetAtom :  (elem : Elem)
--              -> (arom : Bool)
--              -> (0 prf : ValidSubset elem arom)
--              => Atom
--   Bracket    :  (massNr    : Maybe MassNr)
--              -> (elem      : Elem)
--              -> (isArom    : Bool)
--              -> (chirality : Chirality)
--              -> (hydrogens : HCount)
--              -> (charge    : Charge)
--              -> (0 prf     : ValidAromatic elem isArom)
--              => Atom
--
-- %runElab derive "Atom" [Show,Eq]
--
-- --------------------------------------------------------------------------------
-- --          Bonds
-- --------------------------------------------------------------------------------
--
-- public export
-- record RingNr where
--   constructor MkRingNr
--   value : Bits8
--   0 prf : So (value < 99)
--
-- %runElab rwInt "RingNr" `(Bits8)
--
-- public export
-- data Bond = Sngl | Arom | Dbl | Trpl | Quad
--
-- %runElab derive "Bond" [Show,Eq,Ord]
--
-- public export
-- SmilesMol : Type
-- SmilesMol = Graph Bond Atom
--
--
-- export %hint
-- toValidArom : ValidSubset e b => ValidAromatic e b
-- toValidArom @{VB}  = VAB
-- toValidArom @{VC}  = VAC
-- toValidArom @{VN}  = VAN
-- toValidArom @{VO}  = VAO
-- toValidArom @{VF}  = VARest
-- toValidArom @{VP}  = VAP
-- toValidArom @{VS}  = VAS
-- toValidArom @{VCl} = VARest
-- toValidArom @{VBr} = VARest
-- toValidArom @{VI}  = VARest

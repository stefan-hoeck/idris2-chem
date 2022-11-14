module Chem.ImplH

import Data.List
import Chem
import Text.Smiles
import Data.String
import Data.Graph
import Data.BitMap
import Data.AssocList
import Data.Either
import System.File

%default total

-- new datatypes
record AtomWithH where
  constructor AWH
  elem      : Elem
  aromatic  : Bool
  charge    : Charge
  hcount    : HCount

record Bonds where
  constructor BS
  single : Nat
  double : Nat
  triple : Nat

-- interfaces and help functions
Semigroup Bonds where
  (BS s1 d1 t1) <+> (BS s2 d2 t2) = BS (s1 + s2) (d1 + d2) (t1 + t2)

Monoid Bonds where
  neutral = BS 0 0 0

bondsToNat : Bonds -> Nat
bondsToNat (BS s d t) = s + d * 2 + t * 3

showBonds : Bonds -> String
showBonds (BS s d t) =
  "Sngl: " ++ show s ++ ", Dbl: "++ show d ++ ", Trpl: " ++ show t


Show AtomWithH where
  showPrec p (AWH e ar ch hc) =
    showCon p "AWH" $  showArg e
                    ++  showArg ar
                    ++  showArg ch
                    ++  showArg hc

showBond : List Bond -> String
showBond [] = ""
showBond (x :: xs) = show x ++ " " <+> showBond xs 

-- definition of errortypes
data ImplHError : Type where
  WrongBondCount  : (num : Nat   ) -> (value : Atom)  -> ImplHError
  WrongBonds      : (value : Atom) -> ImplHError

dispImplHError : ImplHError -> String
dispImplHError (WrongBondCount n v) = "Wrong number of Bonds for this Atom: " ++ show v ++ " Bonds: " ++ show n
dispImplHError (WrongBonds v)       = "Impossible assignment of bonds to this Atom: " ++ show v

data AtomTypeError : Type where
  WrongElementOrCharge: (elem : Elem) -> (charge : Charge) -> AtomTypeError
  WrongAmountBonds    : (elem : Elem) -> (charge : Charge) -> (bonds : Bonds) -> AtomTypeError
  AtomNotRecordedNow  : (elem : Elem) -> AtomTypeError

dispATError : AtomTypeError -> String
dispATError (WrongElementOrCharge elem c) = "Wrong Element and/or Charge for this function: " ++ show elem ++ show c
dispATError (WrongAmountBonds elem c b)   = "Wrong amount of bonds for this element. Element: " ++ show elem ++ " Charge: " ++ show c ++ " Bonds: " ++ showBonds b
dispATError (AtomNotRecordedNow elem)     = "Atom is not recorded now: " ++ show elem

-- transformation functions
fromSmilesElem : SmilesElem -> (Elem, Bool)
fromSmilesElem (El x)         = (x, False)
fromSmilesElem (A (SA BArom)) = (B, True)
fromSmilesElem (A (SA CArom)) = (C, True)
fromSmilesElem (A (SA NArom)) = (N, True)
fromSmilesElem (A (SA OArom)) = (O, True)
fromSmilesElem (A (SA SArom)) = (S, True)
fromSmilesElem (A (SA PArom)) = (P, True)
fromSmilesElem (A SeArom)     = (Se, True)
fromSmilesElem (A AsArom)     = (As, True)

fromOrgSubset : OrgSubset -> Elem
fromOrgSubset B          = B
fromOrgSubset C          = C
fromOrgSubset N          = N
fromOrgSubset O          = O
fromOrgSubset F          = F
fromOrgSubset P          = P
fromOrgSubset S          = S
fromOrgSubset Cl         = Cl
fromOrgSubset Br         = Br
fromOrgSubset I          = I
fromOrgSubset (OA BArom) = B
fromOrgSubset (OA CArom) = C
fromOrgSubset (OA NArom) = N
fromOrgSubset (OA OArom) = O
fromOrgSubset (OA SArom) = S
fromOrgSubset (OA PArom) = P


-- further help functions

--- Counts Arom Bonds as 1!
--- Can lead to wrong Bondcount!
bondTotal : List Bond -> Nat
bondTotal [] = 0
bondTotal (Sngl :: xs) = 1 + (bondTotal xs)
bondTotal (Arom :: xs) = 1 + (bondTotal xs)
bondTotal (Dbl :: xs)  = 2 + (bondTotal xs)
bondTotal (Trpl :: xs) = 3 + (bondTotal xs)
bondTotal (Quad :: xs) = 4 + (bondTotal xs)

orderBond' : Bond -> Nat
orderBond' Sngl  = 0
orderBond' Dbl   = 1
orderBond' Trpl  = 2
orderBond' Quad  = 3
orderBond' Arom  = 4

orderBond : Bond -> Bond -> Ordering
orderBond = compare `on` orderBond'

sortBond : (Bond -> Bond -> Ordering) -> List Bond -> List Bond
sortBond f xs = sortBy f xs

toBonds : List Bond -> Bonds
toBonds []           = BS 0 0 0
toBonds (Sngl :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (Dbl :: xs)  = BS 0 1 0 <+> toBonds xs
toBonds (Trpl :: xs) = BS 0 0 1 <+> toBonds xs
toBonds (Arom :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (x :: xs)    = BS 0 0 0 <+> toBonds xs

hCountToBonds : HCount -> Bonds
hCountToBonds (MkHCount value _) = BS (cast value) 0 0


fromOrg : Elem -> HCount -> Either ImplHError AtomWithH
fromOrg e h = Right $ AWH e False 0 h

fromOrgArom : Elem -> HCount -> Either ImplHError AtomWithH
fromOrgArom e h = Right $ AWH e True 0 h

-- determination of implicit hydrogens
--- non-aromatic atoms
toAtomWithHnonArom :  Atom
            -> (numberOfbonds : Nat)
            -> Either ImplHError AtomWithH
toAtomWithHnonArom (SubsetAtom B)  0  = fromOrg B 3
toAtomWithHnonArom (SubsetAtom B)  1  = fromOrg B 2
toAtomWithHnonArom (SubsetAtom B)  2  = fromOrg B 1
toAtomWithHnonArom (SubsetAtom B)  3  = fromOrg B 0
toAtomWithHnonArom (SubsetAtom C)  0  = fromOrg C 4
toAtomWithHnonArom (SubsetAtom C)  1  = fromOrg C 3
toAtomWithHnonArom (SubsetAtom C)  2  = fromOrg C 2
toAtomWithHnonArom (SubsetAtom C)  3  = fromOrg C 1
toAtomWithHnonArom (SubsetAtom C)  4  = fromOrg C 0
toAtomWithHnonArom (SubsetAtom N)  0  = fromOrg N 3
toAtomWithHnonArom (SubsetAtom N)  1  = fromOrg N 2
toAtomWithHnonArom (SubsetAtom N)  2  = fromOrg N 1
toAtomWithHnonArom (SubsetAtom N)  3  = fromOrg N 0
toAtomWithHnonArom (SubsetAtom N)  4  = fromOrg N 1
toAtomWithHnonArom (SubsetAtom N)  5  = fromOrg N 0
toAtomWithHnonArom (SubsetAtom O)  0  = fromOrg O 2
toAtomWithHnonArom (SubsetAtom O)  1  = fromOrg O 1
toAtomWithHnonArom (SubsetAtom O)  2  = fromOrg O 0
toAtomWithHnonArom (SubsetAtom F)  0  = fromOrg F 1
toAtomWithHnonArom (SubsetAtom F)  1  = fromOrg F 0
toAtomWithHnonArom (SubsetAtom P)  0  = fromOrg P 3
toAtomWithHnonArom (SubsetAtom P)  1  = fromOrg P 2
toAtomWithHnonArom (SubsetAtom P)  2  = fromOrg P 1
toAtomWithHnonArom (SubsetAtom P)  3  = fromOrg P 0
toAtomWithHnonArom (SubsetAtom P)  4  = fromOrg P 1
toAtomWithHnonArom (SubsetAtom P)  5  = fromOrg P 0
toAtomWithHnonArom (SubsetAtom S)  0  = fromOrg S 2
toAtomWithHnonArom (SubsetAtom S)  1  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S)  2  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom S)  3  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S)  4  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom S)  5  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S)  6  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom Cl)  0 = fromOrg Cl 1
toAtomWithHnonArom (SubsetAtom Cl)  1 = fromOrg Cl 0
toAtomWithHnonArom (SubsetAtom Br)  0 = fromOrg Br 1
toAtomWithHnonArom (SubsetAtom Br)  1 = fromOrg Br 0
toAtomWithHnonArom (SubsetAtom I)  0  = fromOrg I 1
toAtomWithHnonArom (SubsetAtom I)  1  = fromOrg I 0
toAtomWithHnonArom (MkAtom _ elem _ hydrogens charge)  _ =
  let (el,isArom) = fromSmilesElem elem
   in Right $ AWH el isArom charge hydrogens
toAtomWithHnonArom (SubsetAtom y) x = Left $ WrongBondCount x (SubsetAtom y)


--- aromatic atoms
toAtomWithHArom : Atom -> List Bond -> Either ImplHError AtomWithH
toAtomWithHArom (SubsetAtom (OA CArom)) [Dbl,Arom,Arom]  = fromOrgArom C 0
toAtomWithHArom (SubsetAtom (OA CArom)) [Sngl,Arom,Arom] = fromOrgArom C 0
toAtomWithHArom (SubsetAtom (OA CArom)) [Arom,Arom]      = fromOrgArom C 1
toAtomWithHArom (SubsetAtom (OA CArom)) [Arom,Arom,Arom] = fromOrgArom C 0
toAtomWithHArom (SubsetAtom (OA BArom)) [Arom,Arom]      = fromOrgArom B 0
toAtomWithHArom (SubsetAtom (OA BArom)) [Sngl,Arom,Arom] = fromOrgArom B 0
toAtomWithHArom (SubsetAtom (OA NArom)) [Arom,Arom]      = fromOrgArom N 0
toAtomWithHArom (SubsetAtom (OA NArom)) [Sngl,Arom,Arom] = fromOrgArom N 0
toAtomWithHArom (SubsetAtom (OA NArom)) [Arom,Arom,Arom] = fromOrgArom N 0
toAtomWithHArom (SubsetAtom (OA OArom)) [Arom,Arom]      = fromOrgArom O 0
toAtomWithHArom (SubsetAtom (OA SArom)) [Arom,Arom]      = fromOrgArom S 0
toAtomWithHArom (SubsetAtom (OA PArom)) [Arom,Arom]      = fromOrgArom P 0
toAtomWithHArom a _                                      = Left $ WrongBonds a


--- differentiation aromaticity
toAtomWithH : Atom -> List Bond -> Either ImplHError AtomWithH
toAtomWithH (SubsetAtom (OA a)) xs = toAtomWithHArom (SubsetAtom (OA a)) (sortBond orderBond xs)
toAtomWithH a xs                   = toAtomWithHnonArom a (bondTotal xs)

--- atom to AtomWithH
adjToAtomH : Adj Bond Atom -> Either ImplHError (Adj Bond AtomWithH)
adjToAtomH (MkAdj label ns) = map (`MkAdj` ns) (toAtomWithH label (values ns))

--- graph to AtomWithH
graphWithH : Graph Bond Atom -> Either ImplHError (Graph Bond AtomWithH)
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtomH graph)

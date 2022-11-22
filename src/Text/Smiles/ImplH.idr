module Text.Smiles.ImplH

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
toAtomWithHnonArom (SubsetAtom B _) 0  = fromOrg B 3
toAtomWithHnonArom (SubsetAtom B _) 1  = fromOrg B 2
toAtomWithHnonArom (SubsetAtom B _) 2  = fromOrg B 1
toAtomWithHnonArom (SubsetAtom B _) 3  = fromOrg B 0
toAtomWithHnonArom (SubsetAtom C _) 0  = fromOrg C 4
toAtomWithHnonArom (SubsetAtom C _) 1  = fromOrg C 3
toAtomWithHnonArom (SubsetAtom C _) 2  = fromOrg C 2
toAtomWithHnonArom (SubsetAtom C _) 3  = fromOrg C 1
toAtomWithHnonArom (SubsetAtom C _) 4  = fromOrg C 0
toAtomWithHnonArom (SubsetAtom N _) 0  = fromOrg N 3
toAtomWithHnonArom (SubsetAtom N _) 1  = fromOrg N 2
toAtomWithHnonArom (SubsetAtom N _) 2  = fromOrg N 1
toAtomWithHnonArom (SubsetAtom N _) 3  = fromOrg N 0
toAtomWithHnonArom (SubsetAtom N _) 4  = fromOrg N 1
toAtomWithHnonArom (SubsetAtom N _) 5  = fromOrg N 0
toAtomWithHnonArom (SubsetAtom O _) 0  = fromOrg O 2
toAtomWithHnonArom (SubsetAtom O _) 1  = fromOrg O 1
toAtomWithHnonArom (SubsetAtom O _) 2  = fromOrg O 0
toAtomWithHnonArom (SubsetAtom F _) 0  = fromOrg F 1
toAtomWithHnonArom (SubsetAtom F _) 1  = fromOrg F 0
toAtomWithHnonArom (SubsetAtom P _) 0  = fromOrg P 3
toAtomWithHnonArom (SubsetAtom P _) 1  = fromOrg P 2
toAtomWithHnonArom (SubsetAtom P _) 2  = fromOrg P 1
toAtomWithHnonArom (SubsetAtom P _) 3  = fromOrg P 0
toAtomWithHnonArom (SubsetAtom P _) 4  = fromOrg P 1
toAtomWithHnonArom (SubsetAtom P _) 5  = fromOrg P 0
toAtomWithHnonArom (SubsetAtom S _) 0  = fromOrg S 2
toAtomWithHnonArom (SubsetAtom S _) 1  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S _) 2  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom S _) 3  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S _) 4  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom S _) 5  = fromOrg S 1
toAtomWithHnonArom (SubsetAtom S _) 6  = fromOrg S 0
toAtomWithHnonArom (SubsetAtom Cl _) 0 = fromOrg Cl 1
toAtomWithHnonArom (SubsetAtom Cl _) 1 = fromOrg Cl 0
toAtomWithHnonArom (SubsetAtom Br _) 0 = fromOrg Br 1
toAtomWithHnonArom (SubsetAtom Br _) 1 = fromOrg Br 0
toAtomWithHnonArom (SubsetAtom I _) 0  = fromOrg I 1
toAtomWithHnonArom (SubsetAtom I _) 1  = fromOrg I 0
toAtomWithHnonArom (Bracket _ elem arom _ hydrogens charge)  _ =
   Right $ AWH elem arom charge hydrogens
toAtomWithHnonArom a@(SubsetAtom y _) x = Left $ WrongBondCount x a


--- aromatic atoms
toAtomWithHArom : Atom -> List Bond -> Either ImplHError AtomWithH
toAtomWithHArom (SubsetAtom C _) [Dbl,Arom,Arom]  = fromOrgArom C 0
toAtomWithHArom (SubsetAtom C _) [Sngl,Arom,Arom] = fromOrgArom C 0
toAtomWithHArom (SubsetAtom C _) [Arom,Arom]      = fromOrgArom C 1
toAtomWithHArom (SubsetAtom C _) [Arom,Arom,Arom] = fromOrgArom C 0
toAtomWithHArom (SubsetAtom B _) [Arom,Arom]      = fromOrgArom B 0
toAtomWithHArom (SubsetAtom B _) [Sngl,Arom,Arom] = fromOrgArom B 0
toAtomWithHArom (SubsetAtom N _) [Arom,Arom]      = fromOrgArom N 0
toAtomWithHArom (SubsetAtom N _) [Sngl,Arom,Arom] = fromOrgArom N 0
toAtomWithHArom (SubsetAtom N _) [Arom,Arom,Arom] = fromOrgArom N 0
toAtomWithHArom (SubsetAtom O _) [Arom,Arom]      = fromOrgArom O 0
toAtomWithHArom (SubsetAtom S _) [Arom,Arom]      = fromOrgArom S 0
toAtomWithHArom (SubsetAtom P _) [Arom,Arom]      = fromOrgArom P 0
toAtomWithHArom a _                                      = Left $ WrongBonds a


--- differentiation aromaticity
toAtomWithH : Atom -> List Bond -> Either ImplHError AtomWithH
toAtomWithH a@(SubsetAtom elem arom) xs = if arom == True
                then toAtomWithHArom a xs
                else toAtomWithHnonArom a $ bondTotal xs
toAtomWithH (Bracket _ elem isArom _ hydrogens charge) _ =
  Right $ AWH elem isArom charge hydrogens

--- atom to AtomWithH
adjToAtomH : Adj Bond Atom -> Either ImplHError (Adj Bond AtomWithH)
adjToAtomH (MkAdj label ns) = map (`MkAdj` ns) (toAtomWithH label (values ns))

--- graph to AtomWithH
graphWithH : Graph Bond Atom -> Either ImplHError (Graph Bond AtomWithH)
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtomH graph)


-------------------------------------------------------------------------------
-- Testing
-------------------------------------------------------------------------------

-- TODO : output not pretty
implHTest : IO ()
implHTest = do
  case parse "CCO" of
       Stuck x xs => putStrLn (show x ++ pack xs)
       End result => case graphWithH result of
                          Left y  => putStrLn (dispImplHError y)
                          Right y => putStrLn (pretty show show y)


{- TODO :
      - Type AWH -> Atom a
      - Pattern match nonArom -> algoritm (saveMinus)
      - List Bonds -> Maybe (Maybe Bond, Nat)
-}

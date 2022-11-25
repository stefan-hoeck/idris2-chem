module Text.Smiles.ImplH

import Data.List
import Chem
import Chem.Atom
import Text.Smiles
import Data.String
import Data.Graph
import Data.BitMap
import Data.AssocList
import Data.Either
import System.File

%default total

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

showBond : List Bond -> String
showBond [] = ""
showBond (x :: xs) = show x ++ " " <+> showBond xs 

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


-- generates a pair with a list of non aromatic bonds and a
-- aromatic bond counter 
toPairBondsNat : List Bond -> (List Bond, Nat)
toPairBondsNat = foldl fun ([],0)
  where fun : (List Bond, Nat) -> Bond -> (List Bond, Nat)
        fun (x, z) Arom = (x, S z)
        fun (x, z) b = (b :: x, z)


fromOrg : Elem -> HCount -> Maybe (Atom Chirality)
fromOrg e h = Just $ MkAtom e False Nothing 0 None h

fromOrgArom : (e : Elem)
           -> (0 prf : ValidAromatic e True)
           => HCount
           -> Maybe (Atom Chirality)
fromOrgArom e h = Just $ MkAtom e True Nothing 0 None h


-- implementation missing!!!
toImplH : (val : Nat) -> (bonds : Nat) -> Maybe HCount


-- determination of implicit hydrogens
--- non-aromatic atoms
toAtomExplicitH :  Atom
            -> (numberOfbonds : Nat)
            -> Maybe (Atom Chirality)
toAtomExplicitH (SubsetAtom B _) n =
  case toImplH 3 n of
    Just x => fromOrg B x
    Nothing => Nothing
toAtomExplicitH (SubsetAtom C _) n =
  case toImplH 4 n of
    Just x => fromOrg C x
    Nothing => Nothing
toAtomExplicitH (SubsetAtom N _) n =
  case (toImplH 3 n <|> toImplH 5 n) of
       Nothing => Nothing
       Just x  => fromOrg N x
toAtomExplicitH (SubsetAtom O _) n =
  case toImplH 2 n of
       Nothing => Nothing
       Just x  => fromOrg O x
toAtomExplicitH (SubsetAtom F _) n =
  case toImplH 1 n of
       Nothing => Nothing
       Just x  => fromOrg F x
toAtomExplicitH (SubsetAtom P _) n =
  case (toImplH 3 n <|> toImplH 5 n) of
       Nothing => Nothing
       Just x  => fromOrg P x
toAtomExplicitH (SubsetAtom S _) n =
  case (toImplH 2 n <|> toImplH 4 n <|> toImplH 6 n) of
       Nothing => Nothing
       Just x  => fromOrg S x
toAtomExplicitH (SubsetAtom Cl _) n =
  case toImplH 1 n of
       Nothing => Nothing
       Just x  => fromOrg Cl x
toAtomExplicitH (SubsetAtom Br _) n =
  case toImplH 1 n of
       Nothing => Nothing
       Just x  => fromOrg Br x
toAtomExplicitH (SubsetAtom I _) n =
  case toImplH 1 n of
       Nothing => Nothing
       Just x  => fromOrg I x
toAtomExplicitH (Bracket m e a chi h cha) n =
  Just $ MkAtom e a m cha chi h


--- aromatic atoms
toAtomExplicitHArom : Atom -> List Bond -> Maybe (Atom Chirality)
toAtomExplicitHArom (SubsetAtom C _) [Dbl,Arom,Arom]  = fromOrgArom C 0
toAtomExplicitHArom (SubsetAtom C _) [Sngl,Arom,Arom] = fromOrgArom C 0
toAtomExplicitHArom (SubsetAtom C _) [Arom,Arom]      = fromOrgArom C 1
toAtomExplicitHArom (SubsetAtom C _) [Arom,Arom,Arom] = fromOrgArom C 0
toAtomExplicitHArom (SubsetAtom B _) [Arom,Arom]      = fromOrgArom B 0
toAtomExplicitHArom (SubsetAtom B _) [Sngl,Arom,Arom] = fromOrgArom B 0
toAtomExplicitHArom (SubsetAtom N _) [Arom,Arom]      = fromOrgArom N 0
toAtomExplicitHArom (SubsetAtom N _) [Sngl,Arom,Arom] = fromOrgArom N 0
toAtomExplicitHArom (SubsetAtom N _) [Arom,Arom,Arom] = fromOrgArom N 0
toAtomExplicitHArom (SubsetAtom O _) [Arom,Arom]      = fromOrgArom O 0
toAtomExplicitHArom (SubsetAtom S _) [Arom,Arom]      = fromOrgArom S 0
toAtomExplicitHArom (SubsetAtom P _) [Arom,Arom]      = fromOrgArom P 0
toAtomExplicitHArom a _                               = Nothing


--- differentiation aromaticity
toAtomWithH : Atom -> List Bond -> Maybe (Atom Chirality)
toAtomWithH a@(SubsetAtom elem arom) xs = if arom == True
                then toAtomExplicitHArom a xs
                else toAtomExplicitH a $ bondTotal xs
toAtomWithH (Bracket _ elem isArom _ hydrogens charge) _ =
  Just $ MkAtom elem isArom Nothing charge None hydrogens

--- atom to AtomWithH
adjToAtomH : Adj Bond Atom -> Maybe (Adj Bond (Atom Chirality))
adjToAtomH (MkAdj label ns) = map (`MkAdj` ns) (toAtomWithH label (values ns))

--- graph to AtomWithH
graphWithH : Graph Bond Atom -> Maybe (Graph Bond (Atom Chirality))
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtomH graph)

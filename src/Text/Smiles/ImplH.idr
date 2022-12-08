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

public export
record Bonds where
  constructor BS
  single : Nat
  double : Nat
  triple : Nat

-- interfaces and help functions
public export
Semigroup Bonds where
  (BS s1 d1 t1) <+> (BS s2 d2 t2) = BS (s1 + s2) (d1 + d2) (t1 + t2)

public export
Monoid Bonds where
  neutral = BS 0 0 0


public export
bondsToNat : Bonds -> Nat
bondsToNat (BS s d t) = s + d * 2 + t * 3

public export
showBonds : Bonds -> String
showBonds (BS s d t) =
  "Sngl: " ++ show s ++ ", Dbl: "++ show d ++ ", Trpl: " ++ show t

public export
showBond : List Bond -> String
showBond [] = ""
showBond (x :: xs) = show x ++ " " <+> showBond xs 

-- further help functions

--- Counts Arom Bonds as 1!
--- Can lead to wrong Bondcount!
public export
bondTotal : List Bond -> Nat
bondTotal [] = 0
bondTotal (Sngl :: xs) = 1 + (bondTotal xs)
bondTotal (Arom :: xs) = 1 + (bondTotal xs)
bondTotal (Dbl :: xs)  = 2 + (bondTotal xs)
bondTotal (Trpl :: xs) = 3 + (bondTotal xs)
bondTotal (Quad :: xs) = 4 + (bondTotal xs)

public export
orderBond' : Bond -> Nat
orderBond' Sngl  = 0
orderBond' Dbl   = 1
orderBond' Trpl  = 2
orderBond' Quad  = 3
orderBond' Arom  = 4

public export
orderBond : Bond -> Bond -> Ordering
orderBond = compare `on` orderBond'

public export
sortBond : (Bond -> Bond -> Ordering) -> List Bond -> List Bond
sortBond f xs = sortBy f xs

public export
toBonds : List Bond -> Bonds
toBonds []           = BS 0 0 0
toBonds (Sngl :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (Dbl :: xs)  = BS 0 1 0 <+> toBonds xs
toBonds (Trpl :: xs) = BS 0 0 1 <+> toBonds xs
toBonds (Arom :: xs) = BS 1 0 0 <+> toBonds xs
toBonds (x :: xs)    = BS 0 0 0 <+> toBonds xs

public export
hCountToBonds : HCount -> Bonds
hCountToBonds (MkHCount value _) = BS (cast value) 0 0


-- generates a pair with a list of non aromatic bonds and a
-- aromatic bond counter 
public export
toPairBondsNat : List Bond -> (List Bond, Nat)
toPairBondsNat = foldl fun ([],0)
  where fun : (List Bond, Nat) -> Bond -> (List Bond, Nat)
        fun (x, z) Arom = (x, S z)
        fun (x, z) b = (b :: x, z)


public export
fromOrg : Elem -> HCount -> Maybe (Atom Chirality)
fromOrg e h = Just $ MkAtom e False Nothing 0 None h

public export
fromOrgArom : (e : Elem)
           -> (0 prf : ValidAromatic e True)
           => HCount
           -> Maybe (Atom Chirality)
fromOrgArom e h = Just $ MkAtom e True Nothing 0 None h


toImplH : (val : Nat) -> (bonds : Nat) -> Maybe HCount
toImplH val bonds = refine (cast val - cast bonds)


public export
explicitH : (e : Elem)
         -> {auto 0 prf : ValidSubset e False}
         -> Nat
         -> Maybe HCount
explicitH B n = toImplH 3 n
explicitH C n = toImplH 4 n
explicitH N n = toImplH 3 n <|> toImplH 5 n
explicitH O n = toImplH 2 n
explicitH F n = toImplH 1 n
explicitH P n = toImplH 3 n <|> toImplH 5 n
explicitH S n = toImplH 2 n <|> toImplH 4 n <|> toImplH 6 n
explicitH Cl n = toImplH 1 n
explicitH Br n = toImplH 1 n
explicitH I n = toImplH 1 n


public export
explicitAromH : (e : Elem)
             -> {auto 0 prf : ValidSubset e True}
             -> (List Bond, Nat)
             -> Maybe HCount
explicitAromH C ([], 2)      = Just $ 1
explicitAromH C ([], 3)      = Just $ 0
explicitAromH C ([Sngl], 2)  = Just $ 0
explicitAromH C ([Dbl], 2)   = Just $ 0
explicitAromH C (_, _)       = Nothing
explicitAromH B ([], 3)      = Just $ 0
explicitAromH B ([], 2)      = Just $ 0
explicitAromH B ([Sngl], 2)  = Just $ 0
explicitAromH B (_, _)       = Nothing
explicitAromH N ([], 3)      = Just $ 0
explicitAromH N ([], 2)      = Just $ 0
explicitAromH N ([Sngl], 2)  = Just 0
explicitAromH N (_, _)       = Nothing
explicitAromH O ([], 2)      = Just $ 0
explicitAromH O (_, _)       = Nothing
explicitAromH S ([], 2)      = Just $ 0
explicitAromH S (_, _)       = Nothing
explicitAromH P ([], 3)      = Just $ 0
explicitAromH P ([], 2)      = Just $ 0
explicitAromH P (_, _)       = Nothing


public export
toAtomWithH : Atom -> List Bond -> Maybe (Atom Chirality)
toAtomWithH (SubsetAtom elem False) xs = case explicitH elem (bondTotal xs) of
  Nothing => Nothing
  Just h => fromOrg elem h
toAtomWithH (SubsetAtom elem True) xs = case (explicitAromH elem (toPairBondsNat xs)) of
  Nothing => Nothing
  Just h => fromOrgArom elem h
toAtomWithH (Bracket _ elem isArom _ hydrogens charge) _ =
  Just $ MkAtom elem isArom Nothing charge None hydrogens

public export
adjToAtomH : Adj Bond Atom -> Maybe (Adj Bond (Atom Chirality))
adjToAtomH (MkAdj label ns) = map (`MkAdj` ns) (toAtomWithH label (values ns))

public export
graphWithH : Graph Bond Atom -> Maybe (Graph Bond (Atom Chirality))
graphWithH (MkGraph graph) = map MkGraph (traverse adjToAtomH graph)

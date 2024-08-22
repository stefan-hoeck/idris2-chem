||| Utilities for computing molecular descriptors
module Chem.QSAR.Util

import Chem
import Chem.Aromaticity
import Chem.AtomType

%default total

parameters {0 b,e,c,p,r,t,ch,l : Type}
           (g : IGraph k b (Atom e c p r h t ch l))

  ||| Returns the element at the given position
  export
  elemAt : Cast e Elem => Fin k -> Elem
  elemAt = cast . elem . lab g

  ||| True, if the given node is an atom of the given element
  export %inline
  isElem : Cast e Elem => Elem -> Fin k -> Bool
  isElem el = (el ==) . cast . elem . lab g
  
  ||| True, if the given list of neighbours points to at least one
  ||| element of the given type
  export %inline
  hasElem : Cast e Elem => Elem -> AssocList k b -> Bool
  hasElem el = any (isElem el) . keys

  ||| True, if the given list of neighbours points to at least one
  ||| element of the given type, bound via a bond of the given order
  export %inline
  hasNeighbour : 
       {auto ce : Cast e Elem}
    -> {auto cb : Cast b BondOrder}
    -> Elem
    -> BondOrder
    -> Fin k
    -> Bool
  hasNeighbour el o =
    any (\(x,v) => cast v == o && isElem el x) . neighboursAsPairs g

  ||| Counts the number of neighbours pointing to an element of the
  ||| given type.
  export %inline
  countElems : Cast e Elem => Elem -> AssocList k b -> Nat
  countElems el = count (isElem el) . keys

  ||| Counts the number of non-hydrogen neighbours
  export %inline
  countNonHs : Cast e Elem => AssocList k b -> Nat
  countNonHs = count (not . isElem H) . keys

  ||| Number of non-hydrogens bound to the given node
  export %inline
  heavyDegree : Cast e Elem => Fin k -> Nat
  heavyDegree = countNonHs . neighboursAsAL g

  ||| Maximum order of bonds connecting the given node
  export %inline
  maxBondOrder : Cast b BondOrder => Fin k -> BondOrder
  maxBondOrder =
    foldl (\o,(_,vb) => max o $ cast vb) Single . neighboursAsPairs g

  ||| True, if the bond connecting the two nodes `x` and `y` is an
  ||| amide bond. We assume, that it has already been verified that x and
  ||| are connected via a single bond.
  export
  isAmideBond : Cast e Elem => Cast b BondOrder => (x,y : Fin k) -> Bool
  isAmideBond x y =
    (isElem N x && hasNeighbour O Dbl y) ||
    (isElem N y && hasNeighbour O Dbl x)

parameters {auto cb : Cast b BondOrder}

  ||| Accumulates the total bond count from an atoms neighbours and the implicit
  ||| hydrogen count.
  export
  bonds : HCount -> AssocList k b -> Bonds
  bonds hc a = BS (cast hc.value) 0 0 <+> foldMap (toBonds . cast) a

  ||| Like `bonds` but counts only non-aromatic bonds.
  export
  nonAromaticBonds : HCount -> AssocList k (AromBond b) -> Bonds
  nonAromaticBonds hc a = BS (cast hc.value) 0 0 <+> foldMap conv a
    where
      conv : AromBond b -> Bonds
      conv ab = if ab.arom then neutral else toBonds (cast ab.type)

||| Total number of neighbours of an atom (including implicit hydrogens)
export
numNeighbours : Atom e c p r HCount t ch l -> AssocList k b -> Nat
numNeighbours a ns = cast a.hydrogen.value + length ns

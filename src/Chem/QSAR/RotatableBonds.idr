module Chem.QSAR.RotatableBonds

import Data.Graph.Indexed.Ring.Util
import Data.SortedSet
import Chem
import Chem.QSAR.Util

%default total

parameters {0 b,e,c,p,r,h,t,ch,l : Type}
           {auto ce          : Cast e Elem}
           {auto cb          : Cast b BondOrder}
           {k                : Nat}
           (ringBonds        : EdgeSet k)
           (includeTerminals : Bool)
           (excludeAmides    : Bool)
           (g                : IGraph k b (Atom e c p r h t ch l))

  ||| True if the given edge counts as a rotatable bond.
  |||
  ||| A single bond is rotatable, if
  |||  * it is not connected to a hydrogen atom
  |||  * it is not a ring bond
  |||  * the atoms it connects are not attached to triple bonds
  |||  * it does not connect a terminal non-H atom (unless `includeTerminals`
  |||    is set to `True`)
  |||  * it is an amide bond and `excludeAmides` is set to `True`
  export
  isRotatableBond : Edge k b -> Bool
  isRotatableBond (E x y l) =
       cast l == Single
    && not (isElem g H x || isElem g H y)
    && not (contains (E x y ()) ringBonds)
    && (maxBondOrder g x < Triple && maxBondOrder g y < Triple)
    && (includeTerminals || (heavyDegree g x > 1 && heavyDegree g y > 1))
    && (not $ excludeAmides && isAmideBond g x y)

  ||| Returns the number of rotatable bonds in a molecule.
  |||
  ||| See also `isRotatableBond` about what counts as a rotatable bond.
  export %inline
  rotatableBondCount : Nat
  rotatableBondCount = count isRotatableBond (edges g)

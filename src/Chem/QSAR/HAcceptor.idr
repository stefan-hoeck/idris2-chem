||| Functionality for counting the number of hydrogen bond acceptors
||| in a molecule.
|||
||| Like in the CDK, a H-acceptor is either
|||  * a non-positively charge oxygen that is not an aromatic ether
|||    nor adjacent to a nitrogen
|||  * a non-positively charge nitrogen that is not adjacent to an oxygen
module Chem.QSAR.HAcceptor

import Chem
import Chem.Aromaticity
import Chem.QSAR.Util

%default total

parameters {0 b,e,p,r,h,t,c,l : Type}
           {auto cst : Cast e Elem}
           {k        : Nat}
           (g        : IGraph k (AromBond b) (Atom e Charge p r h t c l))
  
  isAromEther : AssocList k (AromBond b) -> Bool
  isAromEther bs = countNonHs g bs > 1 && any (isAromatic g) (keys bs)

  ||| True, if the atom at the given node is a hydrogen bond acceptor.
  |||
  ||| Like in the CDK, an H-acceptor is either
  |||  * a non-positively charge oxygen that is not an aromatic ether
  |||    nor adjacent to a nitrogen
  |||  * a non-positively charge nitrogen that is not adjacent to an oxygen
  export
  isHAcceptor : Fin k -> Bool
  isHAcceptor n =
    let A atm ns := adj g n
     in case cast @{cst} (elem atm) of
          N => charge atm <= 0 && not (hasElem g O ns)
          O => charge atm <= 0 && not (hasElem g N ns || isAromEther ns)
          _ => False

  ||| Returns the number of H-acceptors counted in the graph.
  |||
  ||| See also `isHAcceptor` for the rules about what counts as an H-acceptor.
  export %inline
  hAcceptorCount : Nat
  hAcceptorCount = count isHAcceptor $ nodes g

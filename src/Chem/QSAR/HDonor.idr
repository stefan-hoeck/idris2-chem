||| Functionality for counting the number of hydrogen bond donors
||| in a molecule.
|||
||| Like in the CDK, a H-donor is either
|||  * a non-negatively charge oxygen bound to at least on hydrogen
|||  * a non-negatively charge nitrogen bound to at least on hydrogen
module Chem.QSAR.HDonor

import Chem
import Chem.Aromaticity
import Chem.QSAR.Util

%default total

parameters {0 b,e,p,r,t,c,l : Type}
           {auto cst : Cast e Elem}
           {k        : Nat}
           (g        : IGraph k (AromBond b) (Atom e Charge p r HCount t c l))

  ||| True, if the atom at the given node is a hydrogen bond donor.
  |||
  ||| Like in the CDK, a H-donor is either
  |||  * a non-negatively charge oxygen bound to at least on hydrogen
  |||  * a non-negatively charge nitrogen bound to at least on hydrogen
  export
  isHDonor : Fin k -> Bool
  isHDonor n =
    let A a ns := adj g n
     in case cast @{cst} (elem a) of
          N => charge a >= 0 && (hydrogen a > 0 || hasElem g H ns)
          O => charge a >= 0 && (hydrogen a > 0 || hasElem g H ns)
          _ => False

  ||| Returns the number of H-donors counted in the graph.
  |||
  ||| See also `isHDonor` for the rules about what counts as an H-donor.
  export %inline
  hDonorCount : Nat
  hDonorCount = count isHDonor $ nodes g

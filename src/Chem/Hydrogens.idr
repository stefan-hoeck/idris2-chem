||| Algorithms for converting molecule with explicit hydrogens
||| to ones with implicit hydrogens and vice versa.
module Chem.Hydrogens

import Chem.Element
import Chem.Types
import Data.AssocList
import Data.BitMap
import Data.Graph

%default total

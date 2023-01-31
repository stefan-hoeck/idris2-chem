module Test.Chem.AtomType

import Hedgehog

%default total

{-
  * parse SMILES string
  * convert to graph annotated with atom types
  * extract list of atom types from graph
  * return `[]` if any of the above steps fails

  Use `labNodes` to extract labeled nodes from the graph
  and sort them by key (using `Data.List.sortBy`) before
  extracting the labels, because they might be listed in arbitrary
  order.
-}
-- calcAtomTypes : String -> List AtomType

{-
  Uncomment the following without further modifications.
-}

-- prop : (String,List AtomType) -> (PropertyName,Property)
-- prop (s,ats) = MkPair (fromString "SMILES \{s}") $ withTests 1 $ property $
--   calcAtomTypes s === ats


{-
  Define list of pairs of SMILES strings and exptected list
  of atom types.
-}
-- -- Pairs of SMILES strings and expected list of atom types
-- pairs : List (String,List AtomType)

{-
  Uncomment the following without further modifications.
  Make sure to include these `props` in the main test runner
  in module `Main`.
-}
-- export
-- props : Group
-- props = MkGroup "AtomType Properties" $ map prop pairs

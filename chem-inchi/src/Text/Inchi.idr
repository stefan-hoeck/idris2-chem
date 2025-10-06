module Text.Inchi

import Data.String.Builder
import System.FFI
import Text.Molfile
import Text.Smiles

%default total

%foreign "C:idris_gen_inchi,idris2_inchi,libinchi"
prim__genInchi : String -> Ptr String -> Bits32 -> PrimIO Int

export
genInchi : String -> String
genInchi ""  = ""
genInchi mol =
  unsafePerformIO $ do
    pstr <- malloc 0xffff
    _    <- primIO $ prim__genInchi mol (prim__castPtr pstr) 0xffff
    res  <- pure (prim__getString (prim__castPtr pstr))
    free pstr
    pure res

export %inline
genInchiForMol : (n, i, ct : MolLine) -> MolGraph' h t c -> String
genInchiForMol n i c g = genInchi $ withBuilder $ putMol n i c g

toMolBond : SmilesBond -> MolBond
toMolBond Sngl = MkBond False Single NoBondStereo
toMolBond Arom = MkBond False Single NoBondStereo
toMolBond Dbl  = MkBond False Dbl NoBondStereo
toMolBond Trpl = MkBond False Triple NoBondStereo
toMolBond Quad = MkBond False Single NoBondStereo
toMolBond FW   = MkBond False Single NoBondStereo
toMolBond BW   = MkBond False Single NoBondStereo

toMolAtom : SmilesAtom -> MolAtom
toMolAtom (SubsetAtom elem arom) = cast elem
toMolAtom (Bracket (MkAtom elem ch _ _ _ _ _ _)) =
  MkAtom (cast elem) ch [0,0,0] NoRadical () () () Nothing

toMolGraph : SmilesGraph -> MolGraph
toMolGraph = bimap toMolBond toMolAtom

export %inline
genInchiForSmiles : String -> Either String String
genInchiForSmiles =
  map (genInchiForMol "" "idris2-chem" "" . toMolGraph) . readSmiles'

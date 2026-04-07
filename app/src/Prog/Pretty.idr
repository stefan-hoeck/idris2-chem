module Prog.Pretty

import Chem.Aromaticity
import Prog.Util

%default total

Interpolation SmilesAtomAT where
  interpolate a = a.type.name

act : Interpolation e => Interpolation n => List String -> Graph e n -> Prog ()
act [] (G _ g) = stdoutLn (pretty interpolate interpolate g)
act _ _        = invalid

kekulizeSmiles : SmilesGraph -> SmilesGraphAT
kekulizeSmiles =
  mapFst unarom . kekulize (const Dbl) . perceiveSmilesAtomTypes
  where
    unarom : SmilesBond -> SmilesBond
    unarom Arom = Sngl
    unarom b    = b

export
fromSmiles : String -> Prog SmilesGraph
fromSmiles = fromResult . readSmiles

export
prettySmiles : List String -> Prog ()
prettySmiles ("kekulize"::s::t) = fromSmiles s >>= act t . kekulizeSmiles
prettySmiles (s::t)             = fromSmiles s >>= act t
prettySmiles []                 = invalid

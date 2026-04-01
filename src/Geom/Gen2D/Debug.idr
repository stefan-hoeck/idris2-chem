module Geom.Gen2D.Debug

import Chem
import Data.String
import Geom
import Geom.Gen2D.Types
import Geom.Gen2D.Generate
import Text.Smiles
import Text.Molfile

%default total

toMolatomAT : (MolPoint, SmilesAtomAT) -> MolAtomAT
toMolatomAT (p,a) =
  { chirality := ()
  , radical   := NoRadical
  , label     := Nothing
  , position  := toCoords p [0,0,0]
  , elem      $= cast
  } a

toMolbond : SmilesBond -> MolBond
toMolbond Sngl = MkBond False Single NoBondStereo
toMolbond Arom = MkBond False Single NoBondStereo
toMolbond Dbl  = MkBond False Dbl    NoBondStereo
toMolbond Trpl = MkBond False Triple NoBondStereo
toMolbond Quad = MkBond False Single NoBondStereo
toMolbond FW   = MkBond False Dbl    NoBondStereo
toMolbond BW   = MkBond False Dbl    NoBondStereo

attachPoint : AttachPoint n -> String
attachPoint None         = ""
attachPoint (Attach a n) = " (\{show a} -> \{show n})"

export
showComponent : Component k e n -> String
showComponent (C a xs r _) =
 let pre := the String $ if r then "Ring" else "Chain"
  in "\{pre}: \{show xs}\{attachPoint a}"

export
printComponents : Graph e n -> IO ()
printComponents (G _ g) = traverse_ (putStrLn . showComponent) (components g)

export
test : String -> IO ()
test s =
  case readSmiles' s of
    Left x  => putStrLn "\{x}"
    Right x => printComponents x

export
coords : String -> IO ()
coords s =
  case perceiveSmilesAtomTypes <$> readSmiles' s of
    Left x  => putStrLn "\{x}"
    Right (G _ g) => putStrLn (pretty interpolate disp $ coordinates g)

  where
    disp : (MolPoint, SmilesAtomAT) -> String
    disp (p,a) = "\{a.elem.elem} : \{show p}"

export
mol : String -> IO ()
mol s =
  case perceiveSmilesAtomTypes <$> readSmiles' s of
    Left x  => putStrLn "\{x}"
    Right (G k g) =>
     let cg := coordinates g
         mg := bimap toMolbond toMolatomAT cg
         mf := MkMolfile "" "" "" (G k mg) []
      in putStrLn $ writeMolfile mf

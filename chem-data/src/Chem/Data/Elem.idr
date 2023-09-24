module Chem.Data.Elem

import Data.List
import Derive.Prelude

%default total
%language ElabReflection

-- data type similar to the real `ElemData` in `Chem.Data`, which is used
-- to accumulate the values found in the Blue Obelisk `.xml` file.
record ElemData where
  constructor ED
  mass              : Double
  exactMass         : Double
  radiusCovalent    : Double
  radiusVDW         : Maybe Double
  ionization        : Maybe Double
  electronAffinity  : Maybe Double
  electronegativity : Maybe Double
  boilingpoint      : Maybe Double
  meltingpoint      : Maybe Double

%runElab derive "ElemData" [Show]

init : ElemData
init = ED 0 0 0 Nothing Nothing Nothing Nothing Nothing Nothing

-- If the exact mass is still at zero, we set it to the same value as
-- the atomic mass. This is only the case for elements with an atomic
-- number above 115
adj : ElemData -> ElemData
adj x = if x.exactMass < 0.1 then {exactMass := x.mass} x else x

line :
     SnocList (Nat,ElemData)
  -> Nat
  -> ElemData
  -> List String
  -> List ElemData
line sx n x []         =
    map (adj. snd)
  . filter ((Z /=) . fst)
  . sortBy (comparing fst)
  $ sx <>> [(n,x)]
line sx n x ("" :: ss) = line sx n x ss
line sx n x (s  :: ss) = case forget $ split (' ' ==) s of
  ["atomicNumber", v]      => line (sx :< (n,x)) (cast v) init ss
  ["mass", v]              => line sx n ({mass := cast v} x) ss
  ["exactMass", v]         => line sx n ({exactMass := cast v} x) ss
  ["radiusCovalent", v]    => line sx n ({radiusCovalent := cast v} x) ss
  ["radiusVDW", v]         => line sx n ({radiusVDW := Just $ cast v} x) ss
  ["ionization", v]        => line sx n ({ionization := Just $ cast v} x) ss
  ["electronAffinity", v]  => line sx n ({electronAffinity := Just $ cast v} x) ss
  ["electronegativity", v] => line sx n ({electronegativity := Just $ cast v} x) ss
  ["boilingpoint", v]      => line sx n ({boilingpoint := Just $ cast v} x) ss
  ["meltingpoint", v]      => line sx n ({meltingpoint := Just $ cast v} x) ss
  _                        => line sx n x ss

dataLines : List String -> List ElemData
dataLines [] = []
dataLines ("" :: ss) = dataLines ss
dataLines (s  :: ss) = case forget $ split (' ' ==) s of
  ["atomicNumber",n] => line [<] (cast n) init ss
  _            => dataLines ss


generateLines : String -> String
generateLines s =
  let (h :: t) := dataLines $ lines s | [] => ""
      res      := "[ \{show h}" :: map (\x => ", \{show x}") t
   in """
      arrElemData =
        array
      \{unlines $ indent 4 <$> res}    ]
      """

genStr : String
genStr = "-- Generated Data"

||| Extracts data from the `dat` string, generates Idris code from it, and
||| attaches it to `src` after the `-- Generated Data` line.
export
adjustSource : (dat, src : String) -> String
adjustSource dat src =
  let gen         := generateLines dat
      (pre, _::t) := break (genStr ==) (lines src) | _ => src
   in unlines $ pre ++ [genStr, "", gen]

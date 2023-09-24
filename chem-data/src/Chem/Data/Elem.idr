module Chem.Data.Elem

import Data.List
import Derive.Prelude

%default total
%language ElabReflection

record ElemData where
  constructor ED
  symbol            : String
  atomicNumber      : Nat
  mass              : Double
  exactMass         : Double
  radiusCovalent    : Maybe Double
  radiusVDW         : Maybe Double
  ionization        : Maybe Double
  electronAffinity  : Maybe Double
  electronegativity : Maybe Double
  boilingpoint      : Maybe Double
  meltingpoint      : Maybe Double

%runElab derive "ElemData" [Show]

init : String -> ElemData
init s = ED s 0 0 0 Nothing Nothing Nothing Nothing Nothing Nothing Nothing

line : SnocList ElemData -> ElemData -> List String -> List ElemData
line sx x []         = sortBy (comparing atomicNumber) $ sx <>> [x]
line sx x ("" :: ss) = line sx x ss
line sx x (s  :: ss) = case forget $ split (' ' ==) s of
  ["symbol", v]            => line (sx :< x) (init v) ss
  ["atomicNumber", v]      => line sx ({atomicNumber := cast v} x) ss
  ["mass", v]              => line sx ({mass := cast v} x) ss
  ["exactMass", v]         => line sx ({exactMass := cast v} x) ss
  ["radiusCovalent", v]    => line sx ({radiusCovalent := Just $ cast v} x) ss
  ["radiusVDW", v]         => line sx ({radiusVDW := Just $ cast v} x) ss
  ["ionization", v]        => line sx ({ionization := Just $ cast v} x) ss
  ["electronAffinity", v]  => line sx ({electronAffinity := Just $ cast v} x) ss
  ["electronegativity", v] => line sx ({electronegativity := Just $ cast v} x) ss
  ["boilingpoint", v]      => line sx ({boilingpoint := Just $ cast v} x) ss
  ["meltingpoint", v]      => line sx ({meltingpoint := Just $ cast v} x) ss
  _ => line sx x ss

dataLines : List String -> List ElemData
dataLines [] = []
dataLines ("" :: ss) = dataLines ss
dataLines (s  :: ss) = case forget $ split (' ' ==) s of
  ["symbol",n] => line [<] (init n) ss
  _            => dataLines ss


generateLines : String -> String
generateLines s =
  let (h :: t) := dataLines $ lines s | [] => ""
      res      := "    [ \{show h}" :: map (\x => "    , \{show x}") t
   in """
      arrElemData =
        array
      unlines res
      """

genStr : String
genStr = "-- Generated Data"

||| Extracts data from the `dat` string, generates Idris code from it, and
||| attaches it to `src` after the `-- Generated Data` line.
export
adjustSource : (dat, src : String) -> String
adjustSource dat src =
  let gen         := generateLines dat
      (pre, _::t) := break (genStr ==) (lines dat) | _ => src
   in unlines $ pre ++ [genStr, "", gen]

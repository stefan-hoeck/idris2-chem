module Chem.Data.Isotope

import Chem.Elem
import Data.List
import Derive.Prelude
import Text.Lex.Elem

%default total
%language ElabReflection

-- data type similar to the real `IsotopeData` in `Chem.Data`, which is used
-- to accumulate the values found in the Blue Obelisk `.xml` file.
record IsotopeData where
  constructor ID
  massNr           : Nat
  exactMass        : Double
  naturalAbundance : Double

%runElab derive "IsotopeData" [Show]

init : Nat -> IsotopeData
init massNr = ID massNr 0 0

valid : IsotopeData -> Bool
valid d = d.exactMass > 0 && d.naturalAbundance > 0

-- we currently only keep data of naturally occuring isotopes
prependIso : IsotopeData -> List IsotopeData -> List IsotopeData
prependIso i = if valid i then (i::) else id

appendEmpty : List (List a) -> List (List a)
appendEmpty ss = ss ++ replicate (118 `minus` length ss) []

abundance : String -> Double
abundance s = case unpack s of
  d::'.'::t       => cast $ "0.0" ++ pack (d::t)
  c::d::'.'::t    => cast $ "0." ++ pack (c::d::t)
  b::c::d::'.'::t => cast $ pack (b::'.'::c::d::t)
  [d]             => cast $ "0.0" ++ pack [d]
  [c,d]           => cast $ "0." ++ pack [c,d]
  [b,c,d]         => cast $ pack [b,'.',c,d]
  _               => cast s

line :
     SnocList (Nat,List IsotopeData)
  -> Nat
  -> IsotopeData
  -> List IsotopeData
  -> List String
  -> List (List IsotopeData)
line sx n x xs []         =
    appendEmpty
  . map snd
  . sortBy (comparing fst)
  $ sx <>> [(n, prependIso x xs)]
line sx n x xs ("" :: ss) = line sx n x xs ss
line sx n x xs (s  :: ss) = case forget $ split (' ' ==) s of
  ["number",mn,"elementType",el] =>
    case cast {to = Nat} . value  . atomicNr <$> readElement el of
      Just k =>
        if k == n
           then line sx k (init $ cast mn) (prependIso x xs) ss
           else line (sx :< (n, prependIso x xs)) k (init $ cast mn) [] ss
      Nothing => line sx n x xs ss
  ["relativeAbundance", v] => line sx n ({naturalAbundance := abundance v} x) xs ss
  ["exactMass", v]         => line sx n ({exactMass := cast v} x) xs ss
  _                        => line sx n x xs ss

dataLines : List String -> List (List IsotopeData)
dataLines [] = []
dataLines ("" :: ss) = dataLines ss
dataLines (s  :: ss) = case forget $ split (' ' ==) s of
  ["number",mn,"elementType",el] =>
    case cast {to = Nat} . value  . atomicNr <$> readElement el of
      Just k  => line [<] k (init $ cast mn) [] ss
      Nothing => dataLines ss
  _ => dataLines ss


listLines : Show a => List a ->  String
listLines []        = "[]"
listLines [x]       = "[ \{show x} ]"
listLines (x :: xs) =
    unlines
  $ "[ \{show x}" :: (map (\x => indent 6 ", \{show x}") xs ++ [indent 6 "]"])

export
generateLines : String -> String
generateLines s =
  let (h :: t) := dataLines $ lines s | [] => ""
      res      := "[ \{listLines h}" :: map (\x => ", \{listLines x}") t
   in """
      arrIsotopeData =
        array
      \{unlines $ indent 4 <$> res}    ]
      """

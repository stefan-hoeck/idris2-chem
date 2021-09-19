module Test.Data.IntMap

import Data.List
import Data.SortedMap as SM
import Data.IntMapN as IM
import Hedgehog

pair : Gen (Key, Char)
pair = [| MkPair (bits64 (linear 0 0xffffffff)) alpha |]

pairs : Gen $ List (Key, Char)
pairs = list (linear 0 30) pair

intMap : Gen $ IntMap Char
intMap = fromList <$> pairs

singleton_lookup : Property
singleton_lookup = property $ do
  (k,v) <- forAll pair
  IM.lookup k (singleton k v) === Just v

insert_lookup : Property
insert_lookup = property $ do
  ((k,v),m) <- forAll [| MkPair pair intMap |]
  let m2 = insert k v m
  footnote #"After insert: \#{show m2}"#
  lookup k (insert k v m) === Just v

intmap_tolist : Property
intmap_tolist = property $ do
  ps <- forAll pairs
  SM.toList (fromList ps) === sortBy (comparing fst) (pairs (fromList ps))

export
props : Group
props = MkGroup "IntMap Properties"
          [ ("singleton_lookup", singleton_lookup)
          , ("insert_lookup", insert_lookup)
          , ("intmap_tolist", intmap_tolist)
          ]


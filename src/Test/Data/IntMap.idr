module Test.Data.IntMap

import Data.List
import Data.SortedMap as SM
import Data.IntMap as IM
import Hedgehog

pair : Gen (Bits32, Char)
pair = [| MkPair (bits32 (linear 0 0xffffffff)) alpha |]

pairs : Gen $ List (Bits32, Char)
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
  SM.toList (fromList ps) === (sortBy (comparing fst) $ IM.toList (fromList ps))

export
props : Group
props = MkGroup "IntMap Properties"
          [ ("singleton_lookup", singleton_lookup)
          , ("insert_lookup", insert_lookup)
          , ("intmap_tolist", intmap_tolist)
          ]


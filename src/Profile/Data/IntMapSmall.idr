module Profile.Data.IntMapSmall

import Data.DPair
import Data.IntMap as IM
import Data.AssocList as AL
import Data.SortedMap as SM
import Data.Nat
import Profile.Profiler

pairs : List (AL.Key,AL.Key)
pairs = map dup [0 .. 10]

nonEmptySM : SortedMap k v -> Bool
nonEmptySM m = not $ null m

testFromList : () -> Bool
testFromList () =
  Just 5 == lookup 5 (IM.fromList pairs)

testFromListAL : () -> Bool
testFromListAL () =
  Just 5 == lookup 5 (snd $ AL.fromList pairs)

testFromListSM : () -> Bool
testFromListSM () =
  Just 5 == lookup 5 (SM.fromList pairs)

testLookup : IntMap AL.Key -> () -> Bool
testLookup m = \_ => Just 2 == lookup 2 m

testLookupAL : AL m AL.Key -> () -> Bool
testLookupAL al = \_ => Just 2 == lookup 2 al

testLookupSM : SortedMap AL.Key AL.Key -> () -> Bool
testLookupSM m = \_ => Just 2 == lookup 2 m

testInsert : IntMap AL.Key -> () -> Bool
testInsert m = \_ => nonEmpty (insert 2000 2000 m)

testInsertAL : AL m AL.Key -> () -> Bool
testInsertAL m = \_ => nonEmpty (pairs $ insert 2000 2000 m)

testInsertSM : SortedMap AL.Key AL.Key -> () -> Bool
testInsertSM m = \_ => nonEmptySM (insert 2000 2000 m)

testDelete : IntMap AL.Key -> () -> Bool
testDelete m = \_ => nonEmpty (delete 2 m)

testDeleteAL : AL m AL.Key -> () -> Bool
testDeleteAL m = \_ => nonEmpty (pairs $ delete 2 m)

testDeleteSM : SortedMap AL.Key AL.Key -> () -> Bool
testDeleteSM m = \_ => nonEmptySM (delete 2 m)

export
profile : IO ()
profile =
  let im = IM.fromList (map dup [0 .. 3])
      sm = SM.fromList (map dup [0 .. 3])
      al = AL.fromList (map dup [0 .. 3])
   in do
     profileAndReport $
       MkTask "fromList" testFromList 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListAL" testFromListAL 1000 ItIsSucc
     profileAndReport $
       MkTask "fromListSM" testFromListSM 1000 ItIsSucc
     profileAndReport $
       MkTask "lookup" (testLookup im) 1000000 ItIsSucc
     profileAndReport $
       MkTask "lookupAL" (testLookupAL (snd al)) 1000000 ItIsSucc
     profileAndReport $
       MkTask "lookupSM" (testLookupSM sm) 1000000 ItIsSucc
     profileAndReport $
       MkTask "insert" (testInsert im) 1000000 ItIsSucc
     profileAndReport $
       MkTask "insertAL" (testInsertAL (snd al)) 1000000 ItIsSucc
     profileAndReport $
       MkTask "insertSM" (testInsertSM sm) 1000000 ItIsSucc
     profileAndReport $
       MkTask "delete" (testDelete im) 1000000 ItIsSucc
     profileAndReport $
       MkTask "deleteAL" (testDeleteAL (snd al)) 1000000 ItIsSucc
     profileAndReport $
       MkTask "deleteSM" (testDeleteSM sm) 1000000 ItIsSucc

module Test.Data.IntMap.Array

import Data.Refined
import Data.IntMap.Array
import Data.SOP
import Data.Vect
import Hedgehog

ix : Gen Ix
ix = fromMaybe 0 . refine <$> bits8 (linear 0 7)

vect8 : Gen (Vect 8 Char)
vect8 = vect 8 alpha

array : Gen (Arr Char)
array = map fromVect vect8

fromToVect : Property
fromToVect = property $ do
  cs <- forAll vect8
  cs === toVect (fromVect cs)

toFromVect : Property
toFromVect = property $ do
  cs <- forAll array
  cs === fromVect (toVect cs)

mapId : Property
mapId = property $ do
  cs <- forAll array
  cs === map id cs

appId : Property
appId = property $ do
  cs <- forAll array
  cs === (pure id <*> cs)

readSet : Property
readSet = property $ do
  [i,v,arr] <- forAll (np [ix,alpha,array])
  v === read i (set i arr v)

readMod : Property
readMod = property $ do
  [i,arr] <- forAll (np [ix,array])
  toUpper (read i arr) === read i (mod i arr toUpper)

export
props : Group
props = MkGroup "Array Properties"
          [ ("fromToVect", fromToVect)
          , ("toFromVect", toFromVect)
          , ("mapId", mapId)
          , ("appId", appId)
          , ("readSet", readSet)
          , ("readMod", readMod)
          ]

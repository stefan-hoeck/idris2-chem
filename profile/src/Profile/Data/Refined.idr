module Profile.Data.Refined

import Data.Nat
import Data.Refined
import Data.String
import Profile.Profiler

--------------------------------------------------------------------------------
--          Refinements for Strings
--------------------------------------------------------------------------------

-- This was the original version. It is slightly slower
-- than the version we use now.
allStrM : (Char -> Bool) -> String -> Bool
allStrM f x = case strM x of
  StrNil         => True
  (StrCons y xs) => case f y of
    True  => all f (assert_smaller x xs)
    False => False

-- The short convenience version using
-- the `Foldable` version of `all`.
-- It performs pretty well.
-- The tail-call optimized and specialized version
-- from `Data.Refined` is twice as fast.
allUnpack : (Char -> Bool) -> String -> Bool
allUnpack f = all f . unpack

testAllUnpack : () -> Bool
testAllUnpack () =
  let str = "The quick brown fox and all that bullshit"
   in allUnpack isPrintableLatin str

testAllUnpackTR : () -> Bool
testAllUnpackTR () =
  let str = "The quick brown fox and all that bullshit"
   in all isPrintableLatin str

testAllStrM : () -> Bool
testAllStrM () =
  let str = "The quick brown fox and all that bullshit"
   in allStrM isPrintableLatin str

--------------------------------------------------------------------------------
--          Parsing Natural Numbers
--------------------------------------------------------------------------------

readNatStrM : Num a => String -> Maybe a
readNatStrM = go 0
  where go : Integer -> String -> Maybe a
        go res s = case strM s of
          StrNil       => Just $ fromInteger res
          StrCons c cs =>
            if isDigit c
               then go (cast (ord c - 48) + res * 10)
                    (assert_smaller s cs)
               else Nothing

readNatCast : Eq a => Num a => Cast String a => String -> Maybe a
readNatCast s   =
  let res = cast {to = a} s
   in if res == 0 && any ('0' /=) s then Nothing else Just res

readNatUnpackTR : Num a => String -> Maybe a
readNatUnpackTR = go 0 . unpack
  where go : Integer -> List Char -> Maybe a
        go res []       = Just $ fromInteger res
        go res (h :: t) =
          if isDigit h
             then go (cast (ord h - 48) + res * 10) t
             else Nothing

testBits32StrM : () -> Bool
testBits32StrM () =
  let str = "288776654"
   in isJust $ readNatStrM {a = Bits32} str

testBits32Cast : () -> Bool
testBits32Cast () =
  let str = "288776654"
   in isJust $ readNatCast {a = Bits32} str

testBits32UnpackTR : () -> Bool
testBits32UnpackTR () =
  let str = "288776654"
   in isJust $ readNatUnpackTR {a = Bits32} str


export
profile : IO ()
profile = do
  profileAndReport $
    MkTask "allUnpack" testAllUnpack 1000000 ItIsSucc
  profileAndReport $
    MkTask "allUnpackTR" testAllUnpackTR 1000000 ItIsSucc
  profileAndReport $
    MkTask "allStrM" testAllStrM 1000000 ItIsSucc
  profileAndReport $
    MkTask "readBits32StrM" testBits32StrM 1000000 ItIsSucc
  profileAndReport $
    MkTask "readBits32Cast" testBits32Cast 1000000 ItIsSucc
  profileAndReport $
    MkTask "readBitsUnpackTR" testBits32UnpackTR 1000000 ItIsSucc

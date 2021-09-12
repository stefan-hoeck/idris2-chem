||| Utilities for working with refined primitives
module Data.Refined

import public Data.DPair
import public Language.Reflection.Refined.Util

import Data.String

--------------------------------------------------------------------------------
--          Parsing and Printing
--------------------------------------------------------------------------------

public export
readNat : Num a => String -> Maybe a
readNat = go 0
  where go : a -> String -> Maybe a
        go res s = case strM s of
          StrNil       => Just res
          StrCons c cs =>
            if isDigit c
               then go (fromInteger (cast (ord c - 48)) + res * 10)
                    (assert_smaller s cs)
               else Nothing

public export
readInt : Num a => Neg a => String -> Maybe a
readInt s = case strM s of
  StrCons '-' t => negate <$> readNat t
  _             => readNat s

public export
readRefinedNat :  {f : a -> Bool}
               -> Num a
               => String
               -> Maybe (Subset a $ So . f)
readRefinedNat s =
  readNat s >>= \n =>
    case choose (f n) of
      Left oh => Just $ Element n oh
      Right _ => Nothing

public export
readRefinedInt :  {f : a -> Bool}
               -> Num a
               => Neg a
               => String
               -> Maybe (Subset a $ So . f)
readRefinedInt s =
  readInt s >>= \n =>
    case choose (f n) of
      Left oh => Just $ Element n oh
      Right _ => Nothing

namespace Int8
  public export %inline
  read : {f : Int8 -> Bool} -> String -> Maybe (Subset Int8 $ So . f)
  read = readRefinedInt

  public export %inline
  write : Subset Int8 p -> String
  write = show . fst

namespace Int16
  public export %inline
  read : {f : Int16 -> Bool} -> String -> Maybe (Subset Int16 $ So . f)
  read = readRefinedInt

  public export %inline
  write : Subset Int16 p -> String
  write = show . fst

namespace Int32
  public export %inline
  read : {f : Int32 -> Bool} -> String -> Maybe (Subset Int32 $ So . f)
  read = readRefinedInt

  public export %inline
  write : Subset Int32 p -> String
  write = show . fst

namespace Int64
  public export %inline
  read : {f : Int64 -> Bool} -> String -> Maybe (Subset Int64 $ So . f)
  read = readRefinedInt

  public export %inline
  write : Subset Int64 p -> String
  write = show . fst

namespace Bits8
  public export %inline
  read : {f : Bits8 -> Bool} -> String -> Maybe (Subset Bits8 $ So . f)
  read = readRefinedNat

  public export %inline
  write : Subset Bits8 p -> String
  write = show . fst

namespace Bits16
  public export %inline
  read : {f : Bits16 -> Bool} -> String -> Maybe (Subset Bits16 $ So . f)
  read = readRefinedNat

  public export %inline
  write : Subset Bits16 p -> String
  write = show . fst

namespace Bits32
  public export %inline
  read : {f : Bits32 -> Bool} -> String -> Maybe (Subset Bits32 $ So . f)
  read = readRefinedNat

  public export %inline
  write : Subset Bits32 p -> String
  write = show . fst

namespace Bits64
  public export %inline
  read : {f : Bits64 -> Bool} -> String -> Maybe (Subset Bits64 $ So . f)
  read = readRefinedNat

  public export %inline
  write : Subset Bits64 p -> String
  write = show . fst

--------------------------------------------------------------------------------
--          Fixed-width naturals
--------------------------------------------------------------------------------

public export
Digits : Bits32 -> Type
Digits maxVal = Subset Bits32 (So . (<= maxVal))

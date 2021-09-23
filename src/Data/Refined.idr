||| Utilities for working with refined primitives
|||
||| TODO: Eventually, we should clean up this stuff and put it in its
|||       own Idris2 package
module Data.Refined

import public Language.Reflection.Refined.Util
import Language.Reflection.Refined

import Data.String

%default total

--------------------------------------------------------------------------------
--          Refined Strings
--------------------------------------------------------------------------------

public export
all : (Char -> Bool) -> String -> Bool
all f = go . unpack
  where go : List Char -> Bool
        go []       = True
        go (h :: t) = if f h then go t else False

public export
any : (Char -> Bool) -> String -> Bool
any f = go . unpack
  where go : List Char -> Bool
        go []       = False
        go (h :: t) = if f h then True else go t

public export
isPrintableAscii : Char -> Bool
isPrintableAscii c = '\32' <= c && c <= '\127'

public export
isPrintableLatin : Char -> Bool
isPrintableLatin c = isPrintableAscii c || ('\160' <= c && c <= '\255')

--------------------------------------------------------------------------------
--          Parsing and Printing
--------------------------------------------------------------------------------

||| Reads a natural number consisting *only* of digits.
||| Note: * The number may be prefixed with an arbitrary
|||         number of zeros
|||       * Any non-digit character will make the function
|||         return `Nothing`
|||       * Bounds are not checked, so this might lead to
|||         truncation due to integer overflows in case of
|||         large digit sequences
public export
readInt : Eq a => Num a => Cast String a => String -> Maybe a
readInt s   =
  let res = cast {to = a} s
   in if res == 0 && (any ('0' /=) s || s == "") then Nothing else Just res

||| Like `readInt`, but the number can be prefixed
||| with a single optional '+'.
public export
readIntPlus : Eq a => Num a => Cast String a => String -> Maybe a
readIntPlus s = case strM s of
  StrCons '+' t => readInt t
  _             => readInt s

--------------------------------------------------------------------------------
--          Elab Scripts
--------------------------------------------------------------------------------

||| This creates boiler-plate code for refined primitive integral values.
|||
||| A refined value must be of the following structure:
||| It must be a record with a constructor equal to the
||| type's name prefixed by "Mk", a single accessor called `value`
||| and an erased proof of validity of type `So`. See below for
||| an example
|||
||| The generated code consists of the following (in the section
||| below, `prim` means the primitive data type (`Bits16` in the
||| example below), `dt` means the refined data type (`MassNr` in
||| in the example below)):
|||
|||  * implementations of `Eq`, `Ord`, and `Show`
|||  * a namespace named after the data type, exporting
|||    the following functions:
|||
|||    * function `refine` of type `prim -> Maybe dt`
|||    * function `fromInteger` of type
|||      `(n : Integer) -> {0 auto _ : IsJust (refine n)} -> dt`
|||    * function `read` of type `String -> Maybe dt`
|||    * function `write` of type `dt -> String`
||| 
||| @dataType Name of the data type (for instance "MassNr")
||| @reader   quoted function used for reading the unrefined
|||           integral from a string (for instance `(readInt))
||| @writer   quoted function used for writing the refined
|||           type to a string (for instance `(show . value))
||| @type     quoted name of the wrapped data type (for instance
|||           `(Bits16)).
|||
||| ```idris example
||| %language ElabReflection
|||
||| record MassNr where
|||   constructor MkMassNr
|||   value : Bits16
|||   0 prf : So (1 <= value && value <= 511)
|||
||| %runElab rwIntegral MassNr `(readInt) `(show . value) `(Bits16)
||| ```
export
rwIntegral :  (dataType : String)
           -> (reader   : TTImp)
           -> (writer   : TTImp)
           -> (tpe      : TTImp)
           -> Elab ()
rwIntegral dt reader writer tpe =
  let ns        = MkNS [dt]
      t         = varStr dt
      nameStr   = primVal $ Str dt

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in `read`
      refineNS  = var $ NS ns (UN $ Basic "refine")
   in refinedIntegralDflt dt tpe >>
      declare
        [ INamespace EmptyFC ns
          `[ public export
             read : String -> Maybe ~(t)
             read s = ~(reader) s >>= ~(refineNS)

             public export
             readE : (String -> err) -> String -> Either err ~(t)
             readE f s = maybe (Left $ f s) Right $ read s

             public export
             readMsg : String -> Either String ~(t)
             readMsg = mkReadE read ~(nameStr)

             public export
             write : ~(t) -> String
             write = ~(writer)
           ]
        ]

||| Alias for `rwIntegral dt `(readInt) `(show . value)`
export
rwInt : (dataType : String) -> (tpe : TTImp) -> Elab ()
rwInt dt = rwIntegral dt `(readInt) `(show . value)

||| Alias for `rwIntegral dt `(readIntPlus) `(show . value)`
export
rwIntPlus : (dataType : String) -> (tpe : TTImp) -> Elab ()
rwIntPlus dt = rwIntegral dt `(readIntPlus) `(show . value)

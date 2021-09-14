||| Fixed-width floating point numbers in
||| Mol-Files
module Text.Molfile.Float

import Data.List1
import Data.Refined
import Data.String
import Text.RW

public export
pow10 : Nat -> Bits32
pow10 0     = 1
pow10 (S k) = 10 * pow10 k

||| Fixed-width floating point numbers
|||
||| FIXME: This actually needs also a signum!
public export
record Float (minPre,maxPre : Int32) (wpost : Nat) where
  constructor MkFloat
  pre       : Int32
  post      : Bits32
  0 prePrf  : So (minPre  <= pre  && pre  <= maxPre)
  0 postPrf : So (post < pow10 wpost)

public export
Eq (Float a b c) where
  (==) = (==) `on` (\v => (v.pre,v.post))

public export
Ord (Float a b c) where
  compare = compare `on` (\v => (v.pre,v.post))

public export
refine :  {minPre, maxPre : _}
       -> {wpost : _}
       -> Int32
       -> Bits32
       -> Maybe (Float minPre maxPre wpost)
refine pre post = do
  prfPre  <- maybeSo (minPre <= pre && pre <= maxPre)
  prfPost <- maybeSo (post < pow10 wpost)
  pure $ MkFloat pre post prfPre prfPost

rd :  {minPre,maxPre : _}
   -> {wpost : _}
   -> String
   -> Maybe (Float minPre maxPre wpost)
rd s = case split ('.' ==) s of
  (h ::: [t]) =>
    if length t == wpost
       then do
         pre     <- case h of
           "-0" => Just 0
           _    => readIntPlus h
         post    <- readInt t
         refine pre post
       else Nothing
  _           => Nothing

export %hint %inline
readImpl : {minPre,maxPre : _} -> {wpost : _} -> Read (Float minPre maxPre wpost)
readImpl = mkRead rd "Float"


wt : {wpost : _} -> Float minPre maxPre wpost -> String
wt f = show f.pre ++ "." ++ padLeft wpost '0' (show f.post)

export %hint %inline
writeImpl : {wpost : _} -> Write (Float minPre maxPre wpost)
writeImpl = MkWrite wt
public export %inline
{wpost : _} -> Show (Float a b wpost) where
  show = write

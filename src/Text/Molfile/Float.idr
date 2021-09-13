||| Fixed-width floating point numbers in
||| Mol-Files
module Text.Molfile.Float

import Data.List1
import Data.Refined
import Data.String

public export
pow10 : Nat -> Bits32
pow10 0     = 1
pow10 (S k) = 10 * pow10 k

||| Fixed-width floating point numbers
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

namespace Float
  public export
  read :  {minPre,maxPre : _}
       -> {wpost : _}
       -> String
       -> Maybe (Float minPre maxPre wpost)
  read s = case split ('.' ==) s of
    (h ::: [t]) =>
      if length t == wpost
         then do
           pre     <- readIntPlus {a = Int32} h 
           post    <- readNat {a = Bits32} t
           prfPre  <- maybeSo (minPre <= pre && pre <= maxPre)
           prfPost <- maybeSo (post < pow10 wpost)
           pure $ MkFloat pre post prfPre prfPost
         else Nothing
    _           => Nothing

  export
  write : {wpost : _} -> Float minPre maxPre wpost -> String
  write f = show f.pre ++ "." ++ padLeft wpost '0' (show f.post)

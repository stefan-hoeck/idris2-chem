||| Fixed-width floating point numbers in
||| Mol-Files
module Text.Molfile.Float

import Data.List1
import Data.Refined
import Data.String
import Decidable.HDec.Bits32
import Decidable.HDec.Int32
import Derive.Prelude
import Text.RW

%default total
%language ElabReflection

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
  {auto 0 prePrf  : FromTo minPre maxPre pre}
  {auto 0 postPrf : post < pow10 wpost}

%runElab deriveIndexed "Float" [Show,Eq,Ord]

public export
refineFloat :
     {minPre, maxPre : _}
  -> {wpost : _}
  -> Int32
  -> Bits32
  -> Maybe (Float minPre maxPre wpost)
refineFloat pre post =
  let Just0 p1 := hdec0 {p = FromTo minPre maxPre} pre | Nothing0 => Nothing
      Just0 p2 := hdec0 {p = (< pow10 wpost)} post     | Nothing0 => Nothing
   in Just $ MkFloat pre post

-- public export
-- read :  {minPre,maxPre : _}
--      -> {wpost : _}
--      -> String
--      -> Maybe (Float minPre maxPre wpost)
-- read s = case split ('.' ==) s of
--   (h ::: [t]) =>
--     if length t == wpost
--        then do
--          pre     <- case h of
--            "-0" => Just 0
--            _    => readIntPlus h
--          post    <- readInt t
--          refine pre post
--        else Nothing
--   _           => Nothing
--
-- public export
-- readMsg :  {minPre,maxPre : _}
--         -> {wpost : _}
--         -> String
--         -> Either String (Float minPre maxPre wpost)
-- readMsg = mkReadE read "Float"
--
--
public export
write : {wpost : _} -> Float minPre maxPre wpost -> String
write f = show f.pre ++ "." ++ padLeft wpost '0' (show f.post)

public export %inline
{wpost : _} -> Interpolation (Float a b wpost) where
  interpolate = write

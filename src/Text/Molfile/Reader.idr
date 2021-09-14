module Text.Molfile.Reader

import Data.List
import Data.String
import Data.Vect
import Text.RW
import public Text.Molfile.Float
import public Text.Molfile.Types

%default total

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

-- this is significantly faster than `Data.String.trim`. Since
-- we use this a lot, it had quite an impact on parsing performance.
trimOr0 : String -> String
trimOr0 "" = "0"
trimOr0 s  = go Nil $ unpack s
  where go : (res : List Char) -> (rem : List Char) -> String
        go res [] = pack $ reverse res
        go res (x :: xs) = if isSpace x then go res xs else go (x :: res) xs

||| Tries to split a `String` into a vector of
||| chunks of exactly the given lengths.
||| Fails if the length of the string does not exactly match
||| the length of concatenated chunks.
export
trimmedChunks : Vect n Int -> String -> Either String (Vect n String)
trimmedChunks ns s = go 0 ns
  where go : (pos : Int) -> Vect k Int -> Either String (Vect k String)
        go pos [] = if pos >= cast (length s)
                       then Right []
                       else Left $ #"String is too long: \#{s} (max : \#{show pos})"#
        go pos (x :: xs) = (trimOr0 (strSubstr pos x s) ::) <$> go (pos + x) xs

||| Chunks of the counts line. See `counts` for a description
||| of the format and types of chunks.
public export
countChunks : Vect 12 Int
countChunks = [3,3,3,3,3,3,3,3,3,3,3,6]

||| General format:
|||   aaabbblllfffcccsssxxxrrrpppiiimmmvvvvvv
|||
|||   aaa    : number of atoms
|||   bbb    : number of bonds
|||   ccc    : chiral flag
|||   vvvvvv : version
|||
||| The other fields are obsolete or no longer supported
||| and are being ignored by the parser.
export
counts : String -> Either String Counts
counts s = do
  [a,b,_,_,c,_,_,_,_,_,_,v] <- trimmedChunks countChunks s
  [| MkCounts (readE a) (readE b) (readE c) (readE v) |]

||| Chunks of an atom line. See `atom` for a description
||| of the format and types of chunks.
public export
atomChunks : Vect 16 Int
atomChunks = [10,10,10,4,2,3,3,3,3,3,3,3,3,3,3,3]

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
|||
|||   x,y,z : coordinates
|||   aaa   : atom symbol
|||   dd    : mass difference (superseded by M ISO line)
|||   ccc   : charge (superseded by M RAD and M CHG lines)
|||   sss   : atom stereo parity
|||   hhh   : hydrogen count + 1
|||   bbb   : stereo care box
|||   vvv   : valence
|||   HHH   : H0 designator
|||
|||   r and i are not used and ignored
export
atom : String -> Either String Atom
atom s = do
  [x,y,z,a,d,c,s,h,b,v,h0,_,_,m,n,e] <- trimmedChunks atomChunks s
  [| MkAtom (readE x) (readE y) (readE z) (readE a) (readE d) (readE c)
            (readE s) (readE h) (readE b) (readE v) (readE h0)
            (readE m) (readE n) (readE e) |]

||| Chunks of a bond line. See `bond` for a description
||| of the format and types of chunks.
export
bondChunks : Vect 7 Int
bondChunks = [3,3,3,3,3,3,3]

||| General format:
|||   111222tttsssxxxrrrccc
|||
|||   111 and 222 : atom references
|||   ttt         : bond type
|||   sss         : bond stereo
|||   rrr         : bond topology
|||   ccc         : reacting center status
|||
|||   xxx is not used and ignored
export
bond : String -> Either String Bond
bond s = do
  [r1,r2,t,ss,r,_,c] <- trimmedChunks bondChunks s
  [| MkBond (readE r1) (readE r2) (readE t) (readE ss) (readE r) (readE c) |]

readN :  {n : _}
      -> (String -> Either String a)
      -> List String
      -> Either String (Vect n a, List String)
readN read = go n
  where go : (k : Nat) -> List String -> Either String (Vect k a, List String)
        go Z ss           = Right ([], ss)
        go (S k) []       = Left "Unexpected end of input"
        go (S k) (h :: t) = do
          va        <- read h
          (vt,rest) <- go k t
          pure (va :: vt, rest)

readProps : List String -> Either String (List Property)
readProps []         = Left "Unexpected end of mol file"
readProps ["M  END"] = Right []
readProps (x :: xs)  = do
  p1 <- readE x
  t  <- readProps xs
  pure $ p1 :: t


molLines : List String -> Either String MolFile
molLines (n :: i :: c :: cnt :: t) = do
  name    <- readE n
  info    <- readE i
  comm    <- readE c
  cnts    <- counts cnt
  (as,t1) <- readN atom t
  (bs,t2) <- readN bond t1
  ps      <- readProps t2
  pure (MkMolFile name info comm cnts as bs ps)
molLines _ = Left "Unexpected end of input"

export
mol : String -> Either String MolFile
mol = molLines . lines

--------------------------------------------------------------------------------
--          Writing
--------------------------------------------------------------------------------

export
writeChunks : Vect n Int -> Vect n String -> String
writeChunks = go ""
  where go : String -> Vect k Int -> Vect k String -> String
        go res [] []               = res
        go res (x :: xs) (y :: ys) =
          go (res ++ padLeft (cast x) ' ' y) xs ys

export
writeCounts : Counts -> String
writeCounts (MkCounts a b c v) =
  writeChunks countChunks
    [write a,write b,"0","0",write c,"0","0","0","0","0","0", write v]

export
writeAtom : Atom -> String
writeAtom (MkAtom x y z a d c s h b v h0 m n e) =
  writeChunks atomChunks
    [ write x, write y, write z, write a, write d, write c
    , write s, write h, write b, write v, write h0, "0", "0", write m, write n
    , write e]

export
writeBond : Bond -> String
writeBond (MkBond r1 r2 t ss r c) =
  writeChunks bondChunks
    [write r1, write r2, write t, write ss, write r, "0", write c]

export
writeMol : MolFile -> String
writeMol (MkMolFile n i c cnts as bs ps) =
  fastUnlines $  [value n, value i, value c, writeCounts cnts]
              ++ toList (map writeAtom as)
              ++ toList (map writeBond bs)
              ++ map write ps
              ++ ["M  END"]

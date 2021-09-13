module Text.Molfile.Reader

import Data.String
import Data.Vect
import public Text.Molfile.Float
import public Text.Molfile.Types

%default total

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

||| Tries to split a `String` into a vector of
||| chunks of exactly the given lengths.
||| Fails if the length of the string does not exactly match
||| the length of concatenated chunks.
public export
chunks : Vect n Int -> String -> Maybe (Vect n String)
chunks ns s = go 0 ns
  where go : (pos : Int) -> Vect k Int -> Maybe (Vect k String)
        go pos [] = if pos >= cast (length s) then Just [] else Nothing
        go pos (x :: xs) = (strSubstr pos x s ::) <$> go (pos + x) xs

public export
trimmedChunks : Vect n Int -> String -> Maybe (Vect n String)
trimmedChunks ns s = map trim <$> chunks ns s

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
counts : String -> Maybe Counts
counts s = do
  [a,b,_,_,c,_,_,_,_,_,_,v] <- trimmedChunks countChunks s
  [| MkCounts (read a) (read b) (read c) (read v) |]

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
atom : String -> Maybe Atom
atom s = do
  [x,y,z,a,d,c,s,h,b,v,h0,_,_,m,n,e] <- trimmedChunks atomChunks s
  [| MkAtom (read x) (read y) (read z) (read a) (read d) (read c)
            (read s) (read h) (read b) (read v) (read h0)
            (read m) (read n) (read e) |]

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
bond : String -> Maybe Bond
bond s = do
  [r1,r2,t,ss,r,_,c] <- trimmedChunks bondChunks s
  [| MkBond (read r1) (read r2) (read t) (read ss) (read r) (read c) |]

readN :  {n : _}
      -> (String -> Maybe a)
      -> List String
      -> Maybe (Vect n a, List String)
readN read = go n
  where go : (k : Nat) -> List String -> Maybe (Vect k a, List String)
        go Z ss           = Just ([], ss)
        go (S k) []       = Nothing
        go (S k) (h :: t) = do
          va        <- read h
          (vt,rest) <- go k t
          pure (va :: vt, rest)

readProps : List String -> Maybe (List Property)
readProps []         = Nothing
readProps ["M  END"] = Just []
readProps (x :: xs)  = do
  p1 <- read x
  t  <- readProps xs
  pure $ p1 :: t


molLines : List String -> Maybe MolFile
molLines (n :: i :: c :: cnt :: t) = do
  name    <- MolLine.refine n
  info    <- MolLine.refine i
  comm    <- MolLine.refine c
  cnts    <- counts cnt
  (as,t1) <- readN atom t
  (bs,t2) <- readN bond t1
  ps      <- readProps t2
  pure (MkMolFile name info comm cnts as bs ps)
molLines _ = Nothing

export
mol : String -> Maybe MolFile
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

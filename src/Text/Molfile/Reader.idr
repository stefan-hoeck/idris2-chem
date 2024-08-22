module Text.Molfile.Reader

import Chem.Util
import Data.Array.Mutable
import Data.List.Quantifiers.Extra
import Data.Linear.Traverse1
import Data.Nat
import Data.SortedMap
import Data.String
import Data.Vect
import Text.Lex.Manual.Syntax
import Text.Molfile.Reader.Types
import Text.Molfile.Reader.Util
import public Text.Molfile.Types

import Syntax.T1

%default total

--------------------------------------------------------------------------------
--          Linear Utilities
--------------------------------------------------------------------------------

public export
record Result where
  constructor R
  lines : List (Nat,String)
  mol   : Molfile

%inline
right : a -> (r : MArray k (Adj k x y)) -> T1 [r] -@ R1 [] (Either e (a, IGraph k x y))
right sg r t = let (u # t) := freeze r t in Right (sg, IG u) # t

-- Fails with an error and discards the allocated linear array at the
-- same time.
failAndDiscard : e -> (r : MArray k a) -> (1 t : T1 [r]) -> R1 [] (Either e b)
failAndDiscard err r t = let _ # t := release r t in Left err # t

export
lineTok : Parser a -> (Nat,String) -> Either MolParseErr a
lineTok f (l,s) = case f (unpack s) of
  Right ([], val) => Right val
  Right (cs, val) => Left (MPE l . EInvalid $ pack cs)
  Left err        => Left (MPE l err)

0 GroupMap : Type
GroupMap = SortedMap Nat String

0 MParser : Nat -> Type
MParser k =
     List (Nat,String)
  -> GroupMap
  -> FromMArray
       k
       (Adj k MolBond MolAtom)
       (Either MolParseErr ((List (Nat,String),GroupMap), IGraph k MolBond MolAtom))

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

0 Prop : Nat -> Type
Prop k = (Fin k, MolAtom -> MolAtom)

0 GroupsMod : Type
GroupsMod = GroupMap -> GroupMap

0 STMod : Nat -> Type
STMod k = Either GroupsMod (List $ Prop k)

charge : {k : _} -> Parser (Prop k)
charge = Util.do
  n <- node {k} 4
  c <- int 4 (refineCharge . cast)
  pure $ (n, {charge := c})

%inline
setMass : MassNr -> Isotope -> Isotope
setMass v = {mass := Just v}

iso : {k : _} -> Parser (Prop k)
iso = Util.do
  n <- node {k} 4
  v <- nat 4 (refineMassNr . cast)
  pure $ (n, {elem $= setMass v})

rad : {k : _} -> Parser (Prop k)
rad = Util.do
  n <- node {k} 4
  v <- radical
  pure $ (n, {radical := v})

atomGroup : {k : _} -> Nat -> Parser (Prop k)
atomGroup v = Util.do
  n <- node {k} 4
  pure $ (n, {label := Just $ G v ""})

typ : Parser (Nat, SGroupType)
typ = Util.do
  n <- nat 4 Just
  v <- trim 4 sgroupType
  pure $ (n, v)

nx : (x : Nat) -> Parser a -> Parser (List a)
nx x f = Util.do
  n <- nat 3 (\n => if 1 <= n && n <= x then Just n else Nothing)
  repeat n f [<] 

lbl : Parser (Nat, String)
lbl = Util.[| MkPair (nat 5 Just) (packChars) |]

applyProps : List (Prop k) -> (r : MArray k (Adj k MolBond MolAtom)) -> F1' [r]
applyProps xs r = traverse1_ (\(n,f) => modify r n (map f)) xs

addGroups : List (Nat,SGroupType) -> GroupsMod
addGroups ps m = foldl acc m ps
  where
    acc : GroupMap -> (Nat,SGroupType) -> GroupMap
    acc m (x,SUP) = insert x "" m
    acc m _       = m

atomList : {k : _} -> Parser (List $ Prop k)
atomList = Util.do
  n <- nat 4 Just
  nx 15 (atomGroup n)

setLbl : (Nat, String) -> GroupMap -> GroupMap
setLbl (n,nm) m =
  case lookup n m of
    Just _  => insert n nm m
    Nothing => m

--------------------------------------------------------------------------------
--          Reading
--------------------------------------------------------------------------------

||| General format:
|||   aaabbblllfffcccsssxxxrrrpppiiimmmvvvvvv
|||     3  3  3  3  3  3  3  3  3  3  3     6
|||     3  3     6
|||
|||   aaa    : number of atoms
|||   bbb    : number of bonds
|||   ccc    : chiral flag
|||   vvvvvv : version
|||
||| The other fields are obsolete or no longer supported
||| and are being ignored by the parser.
export
counts : Parser Counts
counts = Util.do
  ac <- count
  bc <- count
  dropN 3
  cf <- trim 3 chiralFlag
  dropN 21
  v  <- trim 6 version
  pure $ MkCounts ac bc cf v

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
atom : Parser MolAtom
atom = Util.do
  pos   <- coords
  i     <- trim 4 isotope
  dropN 2
  c     <- nat 3 charge
  dropN 30
  pure $ MkAtom i c pos NoRadical () () () Nothing

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
bond : {k : _} -> Parser (Edge k MolBond)
bond = Util.do
  x  <- node {k} 3
  y  <- node {k} 3
  t  <- trim 3 bondOrder
  s  <- trim 3 bondStereo
  dropN 9
  edge x y $ MkBond (x < y) t s

prop : {k : _} -> Parser (STMod k)
prop ('M'::' '::' '::'C'::'H'::'G'::t) = map Right <$> nx 8 charge t
prop ('M'::' '::' '::'I'::'S'::'O'::t) = map Right <$> nx 8 iso t
prop ('M'::' '::' '::'R'::'A'::'D'::t) = map Right <$> nx 8 rad t 
prop ('M'::' '::' '::'S'::'T'::'Y'::t) = map (Left . addGroups) <$> nx 8 typ t
prop ('M'::' '::' '::'S'::'A'::'L'::t) = map Right <$> atomList t
prop ('M'::' '::' '::'S'::'M'::'T'::t) = map (Left . setLbl) <$> lbl t
prop _                                 = Right ([], Left id)

properties : {k : _} -> MParser k
properties []                   sg r t = right ([],sg) r t
properties ((_,"M  END") :: ss) sg r t = right (ss,sg) r t
properties (s            :: ss) sg r t =
  case lineTok (prop {k}) s of
    Right (Left f)   => properties ss (f sg) r t
    Right (Right ps) => let _ # t := applyProps ps r t in properties ss sg r t
    Left err         => failAndDiscard err r t

bonds : {k : _} -> (n : Nat) -> MParser k
bonds 0     ss      gs r = properties ss gs r
bonds (S k) (s::ss) gs r =
  case lineTok bond s of
    Right (E x y b) => T1.do
      modify r x {neighbours $= insert y b}
      modify r y {neighbours $= insert x b}
      bonds k ss gs r
    Left err        => failAndDiscard err r
bonds (S k) [] gs r = failAndDiscard (MPE 0 EOI) r

atoms :
     {k : _}
  -> (n, nbonds : Nat)
  -> {auto ix : Ix n k}
  -> MParser k
atoms 0     bs ss      gs r t = bonds bs ss gs r t
atoms (S v) bs (s::ss) gs r t =
  case lineTok atom s of
    Right a  =>
     let _ # t := modifyIx r v {label := a} t
      in atoms v bs ss gs r t
    Left err => failAndDiscard err r t
atoms (S v) bs [] gs r t = failAndDiscard (MPE 0 EOI) r t

adjIni : Adj k MolBond MolAtom
adjIni = A (cast Elem.C) empty

adjLbl : GroupMap -> MolAtom -> MolAtom
adjLbl m = {label $= (>>= \(G n _) => G n <$> lookup n m)}

export
readMolFrom : (ls : List (Nat,String)) -> Either MolParseErr Result
readMolFrom (h1::h2::h3::c::t) = Prelude.do
  name               <- lineTok molLine h1
  info               <- lineTok molLine h2
  comment            <- lineTok molLine h3
  MkCounts as bs _ _ <- lineTok counts c
  ((ls,m),g) <- create as adjIni (atoms as bs t empty)
  pure $ R ls $ MkMolfile name info comment (G as $ map (adjLbl m) g)
readMolFrom ls = Left (MPE 0 EHeader)

export
readMol : Has MolParseErr es => String -> ChemRes es Molfile
readMol "" = Right (MkMolfile "" "" "" (G 0 empty))
readMol s  = bimap inject mol . readMolFrom . zipWithIndex $ lines s

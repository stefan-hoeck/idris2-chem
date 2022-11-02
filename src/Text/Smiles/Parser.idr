module Text.Smiles.Parser

import Chem.Element
import Chem.Types
import Data.BitMap
import Data.Maybe
import Data.String
import Generics.Derive
import Text.Parser.Util
import Text.Smiles.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data DotOrBond = B Bond | Dot | NoDOB

public export
data Err : Type where
  EndOfInput             : Err
  ExpectedAtom           : Err
  ExpectedClosingBracket : Err
  ExpectedElement        : Err
  InvalidCharge          : String -> Err
  InvalidChirality       : String -> Err
  InvalidElement         : String -> Err
  InvalidHCount          : String -> Err
  InvalidMassNr          : String -> Err
  InvalidRingNr          : String -> Err
  UnexpectedCP           : Err
  UnexpectedOP           : Err

%runElab derive "Err" [Generic,Meta,Eq,Show]

||| An atom paired with its node index
public export
record BAtom where
  constructor MkBAtom
  node : Node
  atom : Atom

||| An atom with a ring bond
public export
record RAtom where
  constructor MkRAtom
  atom : BAtom
  bond : Maybe Bond

public export
record ST where
  constructor MkST
  node  : Node
  atom  : BAtom
  stack : List BAtom
  rings : BitMap RAtom
  mol   : SmilesMol

public export
data Result : Type where
  End   : (result : Graph Bond Atom) -> Result
  Stuck : Err -> List Char -> Result

--%runElab derive "Result" [Generic,Meta,Eq,Show]
--------------------------------------------------------------------------------
--          Updating State
--------------------------------------------------------------------------------

isAromatic : Atom -> Bool
isAromatic (SubsetAtom _ arom) = arom
isAromatic (Bracket _ _ isArom _ _ _) = isArom

-- TODO : We should be able to proof that the second
--        `Node` is strictly larger than the first
addBond' : Bond -> Node -> Node -> SmilesMol -> SmilesMol
addBond' b n1 n2 mol = case mkEdge n1 n2 of
  Just e  => insEdge (MkLEdge e b) mol
  Nothing => mol

addBond : Maybe Bond -> BAtom -> BAtom -> SmilesMol -> SmilesMol
addBond m (MkBAtom n1 a1) (MkBAtom n2 a2) mol =
  let b = fromMaybe (if isAromatic a1 && isAromatic a2 then Arom else Sngl) m
   in addBond' b n1 n2 mol

addRing : Maybe Bond -> RingNr -> ST -> ST
addRing b1 r (MkST n a1 s rs g) =
  let k = cast {to = Key} r.value
   in case lookup k rs of
        Nothing              => MkST n a1 s (insert k (MkRAtom a1 b1) rs) g
        Just (MkRAtom a2 b2) =>
          MkST n a1 s (delete k rs) $ addBond (b1 <|> b2) a1 a2 g

--------------------------------------------------------------------------------
--          Atoms
--------------------------------------------------------------------------------

digs : (cs : List Char) -> ResI cs Err $ String
digs cs = mapResI pack $ takeWhile isDigit cs

massNr : (cs : List Char) -> ResM cs Err $ Maybe MassNr
massNr cs = case digs cs of
  Y "" _ _ => y cs Nothing
  Y ds t p => maybe (N $ InvalidMassNr ds) (y t . Just) $ read ds

vl : Elem -> ValidElem
vl x = VE x False %search

elem : (cs : List Char) -> ResS cs Err ValidElem
elem ('c'     ::t) = y t (VE C True %search)
elem ('b'     ::t) = y t (VE B True %search)
elem ('n'     ::t) = y t (VE N True %search)
elem ('o'     ::t) = y t (VE O True %search)
elem ('p'     ::t) = y t (VE P True %search)
elem ('s'::'e'::t) = y t (VE Se True %search)
elem ('s'     ::t) = y t (VE S True %search)
elem ('a'::'s'::t) = y t (VE As True %search)
elem (c1::c2::t)   =
  if isLower c2
     then either N (y t       . vl) $ readE (pack [c1,c2]) InvalidElement
     else either N (y (c2::t) . vl) $ readE (singleton c1) InvalidElement
elem cs        = N ExpectedElement

chirality : (cs : List Char) -> ResM cs Err Chirality
chirality ('@'::cs) = case cs of
  '@'          ::t => y t CW
  'T'::'H'::'1'::t => y t TH1
  'T'::'H'::'2'::t => y t TH2
  'A'::'L'::'1'::t => y t AL1
  'A'::'L'::'2'::t => y t AL2
  'S'::'P'::'1'::t => y t SP1
  'S'::'P'::'2'::t => y t SP2
  'S'::'P'::'3'::t => y t SP3
  'T'::'B'::     t =>
    let Y ds t' p = digs t
     in maybe (N $ InvalidChirality ("TB" ++ ds)) (y t' . TB) $ read ds
  'O'::'H'::     t =>
    let Y ds t' p = digs t
     in maybe (N $ InvalidChirality ("OH" ++ ds)) (y t' . OH) $ read ds
  t                => y t CCW
chirality cs = y cs None

hcount : (cs : List Char) -> ResM cs Err HCount
hcount ('H'::'H'::t) = y t 2
hcount ('H'::     t) = case digs t of
  Y "" _ _  => y t 1
  Y ds t' p => maybe (N $ InvalidHCount ds) (y t') $ read ds
hcount cs            = y cs 0

charge : (cs : List Char) -> ResM cs Err Charge
charge ('+'::'+'::t) = y t 2
charge ('-'::'-'::t) = y t (-2)
charge ('+'::     t) = case digs t of
  Y "" _ _  => y t 1
  Y ds t' p => maybe (N $ InvalidCharge ds) (y t') $ read ds
charge ('-'::     t) = case digs t of
  Y "" _ _  => y t (-1)
  Y ds t' p => maybe (N $ InvalidCharge ds) (y t') $ read ("-" ++ ds)
charge cs            = y cs 0

bracket : (cs : List Char) -> ResS cs Err Atom
bracket ('['::cs1) =
  let Y mn  cs2      p2 = massNr cs1       | N err => N err
      Y a   cs3      p3 = Parser.elem cs2  | N err => N err
      Y chi cs4      p4 = chirality cs3    | N err => N err
      Y h   cs5      p5 = hcount cs4       | N err => N err
      Y chg (']'::t) p6 = charge cs5       | N err => N err
                                           | _     => N ExpectedClosingBracket
      VE el ar prf = a
   in Y (Bracket mn a.elem a.arom chi h chg) t $
        slConsLeft p6 ~> p5 ~> p4 ~> p3 ~> p2 ~> cons1
bracket cs = N ExpectedAtom

atom : (cs : List Char) -> ResS cs Err Atom
atom ('C'::'l'::t) = y t (SubsetAtom Cl False)
atom ('C'     ::t) = y t (SubsetAtom C False)
atom ('c'     ::t) = y t (SubsetAtom C True)
atom ('N'     ::t) = y t (SubsetAtom N False)
atom ('n'     ::t) = y t (SubsetAtom N True)
atom ('O'     ::t) = y t (SubsetAtom O False)
atom ('o'     ::t) = y t (SubsetAtom O True)
atom ('F'     ::t) = y t (SubsetAtom F False)
atom ('B'::'r'::t) = y t (SubsetAtom Br False)
atom ('S'     ::t) = y t (SubsetAtom S False)
atom ('s'     ::t) = y t (SubsetAtom S True)
atom ('P'     ::t) = y t (SubsetAtom P False)
atom ('p'     ::t) = y t (SubsetAtom P True)
atom ('I'     ::t) = y t (SubsetAtom I False)
atom ('B'     ::t) = y t (SubsetAtom B False)
atom ('b'     ::t) = y t (SubsetAtom B True)
atom cs            = bracket cs
--------------------------------------------------------------------------------
--          Rings and Bonds
--------------------------------------------------------------------------------

bnd : (cs : List Char) -> ResI cs Err (Maybe Bond)
bnd ('='  :: t) = y t (Just Dbl)
bnd ('-'  :: t) = y t (Just Sngl)
bnd (':'  :: t) = y t (Just Arom)
bnd ('#'  :: t) = y t (Just Trpl)
bnd ('$'  :: t) = y t (Just Quad)
bnd ('/'  :: t) = y t Nothing
bnd ('\\' :: t) = y t Nothing
bnd cs         = y cs Nothing

dob : (cs : List Char) -> ResI cs Err DotOrBond
dob ('.' :: t) = y t Dot
dob cs         = mapResI (maybe NoDOB B) $ bnd cs

ringNr : (cs : List Char) -> ResS cs Err RingNr
ringNr ('%'::d1::d2::t) =
  let ds = pack [d1,d2]
   in maybe (N $ InvalidRingNr ("%" ++ ds)) (y t) $ read ds
ringNr (d          ::t) =
  let ds = singleton d
   in maybe (N $ InvalidRingNr ds) (y t) $ read ds
ringNr []               = N $ InvalidRingNr ""

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

headAlpha : List Char -> Bool
headAlpha (c :: _) = isAlpha c || c == '['
headAlpha _        = False

rngs : (cs : List Char) -> (0 _ : SuffixAcc cs) -> ST -> ResI cs Err ST
rngs cs1 (Access rec) st =
  if headAlpha cs1 then y cs1 st
  else
    let Y b   cs2 p2 = bnd cs1
        Y r   cs3 p3 = ringNr cs2 | N _ => y cs1 st
        Y res cs4 p4 = rngs cs3 (rec cs3 $ p3 ~> p2) (addRing b r st)
     in Y res cs4 $ weaken $ p4 ~> p3 ~> p2

atm' : (cs : List Char) -> DotOrBond -> Atom -> ST -> ResI cs Err ST
atm' cs dob a (MkST n a1 s rs g) =
  let a2 = MkBAtom n a
      g2 = insNode n a g
      g3 = case dob of
             NoDOB => addBond Nothing  a1 a2 g2
             B b   => addBond (Just b) a1 a2 g2
             Dot   => g2
   in rngs cs (ssAcc cs) (MkST (n+1) a2 s rs g3)

atm : (cs : List Char) -> ST -> ResS cs Err ST
atm cs1 st =
  if headAlpha cs1
     then
       let Y a   cs2 p2 = atom cs1 | N err => N err
           Y st2 cs3 p3 = atm' cs2 NoDOB a st
        in Y st2 cs3 $ p3 ~> p2
     else
       let Y b   cs2 p2 = dob cs1
           Y a   cs3 p3 = atom cs2 | N err => N err
           Y st2 cs4 p4 = atm' cs3 b a st
        in Y st2 cs4 $ p4 ~> p3 ~> p2

prs : (cs : List Char) -> (0 _ : SuffixAcc cs) -> (st : ST) -> Result
prs cs (Access rec) st =
  case atm cs st of
    Y st2 cs2 p2 => prs cs2 (rec cs2 p2) st2
    N err => case cs of
      '(' :: t => case atm t $ {stack $= (st.atom ::)} st of
         Y st2 cs2 p2 => prs cs2 (rec cs2 $ Cons p2) st2
         N err2       => Stuck err2 t

      ')' :: t => case st.stack of
        a :: as => prs t (rec t cons1) ({stack := as, atom := a} st)
        Nil     => Stuck UnexpectedCP (')' :: t)

      []       =>
        if null (st.rings) && null (st.stack) then End st.mol
        else Stuck EndOfInput []
      _        => Stuck err cs


export
parse : String -> Result
parse "" = End empty
parse s  = case atom (unpack s) of
  N err    => Stuck err (unpack s)
  Y a cs _ =>
    let Y st cs2 _ = rngs cs (ssAcc cs) (MkST 1 (MkBAtom 0 a) Nil empty (insNode 0 a empty))
     in prs cs2 (ssAcc cs2) st

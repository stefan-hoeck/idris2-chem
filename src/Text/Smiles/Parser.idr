module Text.Smiles.Parser

import Data.Graph
import Data.Prim.Bits32
import Data.SortedMap
import Derive.Prelude
import Text.Parse.Manual
import Text.Smiles.Lexer

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data SmilesErr : Type where
  ExpectedAtom       : SmilesErr
  ExpectedAtomOrRing : SmilesErr
  ExpectedAtomOrBond : SmilesErr
  EmptyParen         : SmilesErr
  RingBondMismatch   : SmilesErr
  UnclosedRing       : SmilesErr

export
Interpolation SmilesErr where
  interpolate ExpectedAtom = "Expected an atom"
  interpolate ExpectedAtomOrRing = "Expected an atom or ring bond"
  interpolate ExpectedAtomOrBond = "Expected an atom or a bond"
  interpolate EmptyParen = "Empty parens"
  interpolate RingBondMismatch = "Ring bonds do not match"
  interpolate UnclosedRing = "Unclosed ring"

public export
0 Err : Type
Err = ParseError SmilesToken SmilesErr

%runElab derive "SmilesErr" [Eq,Show]

record RingInfo where
  constructor R
  orig   : Node
  atom   : Atom
  bond   : Maybe Bond
  column : Nat

record AtomInfo where
  constructor A
  orig   : Node
  atom   : Atom
  column : Nat

0 Rings : Type
Rings = SortedMap RingNr RingInfo

public export
0 Mol : Type
Mol = Graph Bond Atom

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

-- hopefully, we know what we are doing...
%inline
unsafeEdge : Node -> Node -> Edge
unsafeEdge x y = MkEdge x y (mkLT $ believe_me (Builtin.Refl {x = True}))

bond : Atom -> Atom -> Bond
bond x y = if isArom x && isArom y then Arom else Sngl

ringBond : Maybe Bond -> Maybe Bond -> Atom -> Atom -> Maybe Bond
ringBond Nothing Nothing   x y = Just $ bond x y
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

bondError : (column : Nat) -> RingNr -> Either (Bounded Err) a
bondError c x = custom (bounds (TR x) c) RingBondMismatch

ring :
     (col : Nat)
  -> RingNr
  -> Maybe Bond
  -> Node
  -> Atom
  -> Rings
  -> Mol
  -> Either (Bounded Err) (Rings,Mol)
ring col2 r mb2 n2 a2 rs m = case lookup r rs of
  Nothing => Right (insert r (R n2 a2 mb2 col2) rs, m)
  Just (R n a mb c) =>
    let Just b := ringBond mb mb2 a a2 | Nothing => bondError col2 r
        rs2    := delete r rs
        edge   := MkLEdge (unsafeEdge n n2) b
     in Right (rs2, insEdge edge m)

-- TODO: We should validate if atoms are aromatic in case of
--       an aromatic bond. But perhaps it is better to do that
--       in the main parser?
%inline
bondTo : Bond -> Node -> Node -> Atom -> Mol -> Mol
bondTo b n1 n2 a2 =
  let le := MkLEdge (unsafeEdge n1 n2) b
   in insEdge le . insNode n2 a2

finalize : List AtomInfo -> Rings -> Mol -> Either (Bounded Err) Mol
finalize (A _ _ c :: xs) _ _ = unclosed (oneChar (P 0 c)) PO
finalize [] rs m = case SortedMap.toList rs of
  []                 => Right m
  (r,R _ _ _ c) :: _ => custom (bounds (TR r) c) UnclosedRing

-- We just got a fresh atom. Now come the optional ring bonds and branches.
-- branched_atom ::= atom ringbond* branch*
chain :
     (orig : Node)          -- the node we bind to
  -> (a    : Atom)          -- the atom we bind to
  -> (s    : List AtomInfo) -- stack of open branches
  -> (r    : Rings)         -- list of opened ring bonds
  -> (m    : Mol)           -- accumulated molecule
  -> (n    : Node)          -- current node
  -> (ts   : List (SmilesToken,Nat))
  -> Either (Bounded Err) Mol
chain o a s r m n [] = finalize s r m
chain o a s r m n ((x,c)::xs) = case x of
  TA a2 => chain n a2 s r (bondTo (bond a a2) o n a2 m) (n+1) xs
  TB b  => case xs of
    (TA a2,_) :: t => chain n a2 s r (bondTo b o n a2 m) (n+1) t
    (TR ri,c) :: t => case ring c ri (Just b) o a r m of
      Right (r2,m2) => chain o a s r2 m2 n t
      Left err      => Left err
    _ => custom (bounds x c) ExpectedAtomOrRing

  PO => case xs of
    (TB b, _) :: (TA a2,_) :: t =>
      chain n a2 (A o a c :: s) r (bondTo b o n a2 m) (n+1) t
    (TA a2,_) :: t =>
      chain n a2 (A o a c :: s) r (bondTo (bond a a2) o n a2 m) (n+1) t
    _ => custom (bounds x c) ExpectedAtomOrBond

  PC => case s of
    A o2 a2 _ :: t => chain o2 a2 t r m n xs
    []             => unexpected (B PC $ bounds PC c)

  TR ri => case ring c ri Nothing o a r m of
      Right (r2,m2) => chain o a s r2 m2 n xs
      Left err      => Left err

  Dot => case xs of
    (TA a2,_) :: t => chain n a2 s r (insNode n a2 m) (n+1) t
    ((t,c)::_)     => custom (bounds t c) ExpectedAtom
    []             => eoi

start : List (SmilesToken,Nat) -> Either (Bounded Err) Mol
start ((TA a,_) :: xs) = chain 0 a [] empty (insNode 0 a empty) 1 xs
start []               = Right empty
start ((t,c) :: _)     = custom (bounds t c) ExpectedAtom

export
parseFrom : Origin -> String -> Either (FileContext,Err) Mol
parseFrom o s =
  let Right ts := lexSmiles s | Left e => Left $ fromBounded o (Reason <$> e)
      Right m  := start ts    | Left e => Left $ fromBounded o e
   in Right m

export %inline
parse : String -> Either (FileContext,Err) Mol
parse = parseFrom Virtual

-- ||| An atom paired with its node index
-- public export
-- record BAtom where
--   constructor MkBAtom
--   node : Node
--   atom : Atom
--
-- ||| An atom with a ring bond
-- public export
-- record RAtom where
--   constructor MkRAtom
--   atom : BAtom
--   bond : Maybe Bond
--
-- public export
-- record ST where
--   constructor MkST
--   node  : Node
--   atom  : BAtom
--   stack : List BAtom
--   rings : BitMap RAtom
--   mol   : SmilesMol
--
-- public export
-- data Result : Type where
--   End   : (result : Graph Bond Atom) -> Result
--   Stuck : Err -> List Char -> Result
--
-- %runElab derive "Result" [Eq,Show]
--
-- --------------------------------------------------------------------------------
-- --          Updating State
-- --------------------------------------------------------------------------------
--
-- isAromatic : Atom -> Bool
-- isAromatic (SubsetAtom _ arom) = arom
-- isAromatic (Bracket _ _ isArom _ _ _) = isArom
--
-- -- TODO : We should be able to proof that the second
-- --        `Node` is strictly larger than the first
-- addBond' : Bond -> Node -> Node -> SmilesMol -> SmilesMol
-- addBond' b n1 n2 mol = case mkEdge n1 n2 of
--   Just e  => insEdge (MkLEdge e b) mol
--   Nothing => mol
--
-- addBond : Maybe Bond -> BAtom -> BAtom -> SmilesMol -> SmilesMol
-- addBond m (MkBAtom n1 a1) (MkBAtom n2 a2) mol =
--   let b = fromMaybe (if isAromatic a1 && isAromatic a2 then Arom else Sngl) m
--    in addBond' b n1 n2 mol
--
-- addRing : Maybe Bond -> RingNr -> ST -> ST
-- addRing b1 r (MkST n a1 s rs g) =
--   let k = cast {to = Key} r.value
--    in case lookup k rs of
--         Nothing              => MkST n a1 s (insert k (MkRAtom a1 b1) rs) g
--         Just (MkRAtom a2 b2) =>
--           MkST n a1 s (delete k rs) $ addBond (b1 <|> b2) a1 a2 g
--
-- --------------------------------------------------------------------------------
-- --          Atoms
-- --------------------------------------------------------------------------------
--
-- digs : (cs : List Char) -> ResI cs Err $ String
-- digs cs = mapResI pack $ takeWhile isDigit cs
--
-- massNr : (cs : List Char) -> ResM cs Err $ Maybe MassNr
-- massNr cs = case digs cs of
--   Y "" _ _ => y cs Nothing
--   Y ds t p => maybe (N $ InvalidMassNr ds) (y t . Just) $ read ds
--
-- vl : Elem -> ValidElem
-- vl x = VE x False
--
-- elem : (cs : List Char) -> ResS cs Err ValidElem
-- elem ('c'     ::t) = y t (VE C True)
-- elem ('b'     ::t) = y t (VE B True)
-- elem ('n'     ::t) = y t (VE N True)
-- elem ('o'     ::t) = y t (VE O True)
-- elem ('p'     ::t) = y t (VE P True)
-- elem ('s'::'e'::t) = y t (VE Se True)
-- elem ('s'     ::t) = y t (VE S True)
-- elem ('a'::'s'::t) = y t (VE As True)
-- elem (c1::c2::t)   =
--   if isLower c2
--      then either N (y t       . vl) $ readE (pack [c1,c2]) InvalidElement
--      else either N (y (c2::t) . vl) $ readE (singleton c1) InvalidElement
-- elem cs        = N ExpectedElement
--
-- chirality : (cs : List Char) -> ResM cs Err Chirality
-- chirality ('@'::cs) = case cs of
--   '@'          ::t => y t CW
--   'T'::'H'::'1'::t => y t TH1
--   'T'::'H'::'2'::t => y t TH2
--   'A'::'L'::'1'::t => y t AL1
--   'A'::'L'::'2'::t => y t AL2
--   'S'::'P'::'1'::t => y t SP1
--   'S'::'P'::'2'::t => y t SP2
--   'S'::'P'::'3'::t => y t SP3
--   'T'::'B'::     t =>
--     let Y ds t' p = digs t
--      in maybe (N $ InvalidChirality ("TB" ++ ds)) (y t' . TB) $ read ds
--   'O'::'H'::     t =>
--     let Y ds t' p = digs t
--      in maybe (N $ InvalidChirality ("OH" ++ ds)) (y t' . OH) $ read ds
--   t                => y t CCW
-- chirality cs = y cs None
--
-- hcount : (cs : List Char) -> ResM cs Err HCount
-- hcount ('H'::'H'::t) = y t 2
-- hcount ('H'::     t) = case digs t of
--   Y "" _ _  => y t 1
--   Y ds t' p => maybe (N $ InvalidHCount ds) (y t') $ read ds
-- hcount cs            = y cs 0
--
-- charge : (cs : List Char) -> ResM cs Err Charge
-- charge ('+'::'+'::t) = y t 2
-- charge ('-'::'-'::t) = y t (-2)
-- charge ('+'::     t) = case digs t of
--   Y "" _ _  => y t 1
--   Y ds t' p => maybe (N $ InvalidCharge ds) (y t') $ read ds
-- charge ('-'::     t) = case digs t of
--   Y "" _ _  => y t (-1)
--   Y ds t' p => maybe (N $ InvalidCharge ds) (y t') $ read ("-" ++ ds)
-- charge cs            = y cs 0
--
-- bracket : (cs : List Char) -> ResS cs Err Atom
-- bracket ('['::cs1) =
--   let Y mn  cs2      p2 = massNr cs1       | N err => N err
--       Y a   cs3      p3 = Parser.elem cs2  | N err => N err
--       Y chi cs4      p4 = chirality cs3    | N err => N err
--       Y h   cs5      p5 = hcount cs4       | N err => N err
--       Y chg (']'::t) p6 = charge cs5       | N err => N err
--                                            | _     => N ExpectedClosingBracket
--       VE el ar = a
--    in Y (Bracket mn a.elem a.arom chi h chg) t $
--         slConsLeft p6 ~> p5 ~> p4 ~> p3 ~> p2 ~> cons1
-- bracket cs = N ExpectedAtom
--
-- atom : (cs : List Char) -> ResS cs Err Atom
-- atom ('C'::'l'::t) = y t (SubsetAtom Cl False)
-- atom ('C'     ::t) = y t (SubsetAtom C False)
-- atom ('c'     ::t) = y t (SubsetAtom C True)
-- atom ('N'     ::t) = y t (SubsetAtom N False)
-- atom ('n'     ::t) = y t (SubsetAtom N True)
-- atom ('O'     ::t) = y t (SubsetAtom O False)
-- atom ('o'     ::t) = y t (SubsetAtom O True)
-- atom ('F'     ::t) = y t (SubsetAtom F False)
-- atom ('B'::'r'::t) = y t (SubsetAtom Br False)
-- atom ('S'     ::t) = y t (SubsetAtom S False)
-- atom ('s'     ::t) = y t (SubsetAtom S True)
-- atom ('P'     ::t) = y t (SubsetAtom P False)
-- atom ('p'     ::t) = y t (SubsetAtom P True)
-- atom ('I'     ::t) = y t (SubsetAtom I False)
-- atom ('B'     ::t) = y t (SubsetAtom B False)
-- atom ('b'     ::t) = y t (SubsetAtom B True)
-- atom cs            = bracket cs
-- --------------------------------------------------------------------------------
-- --          Rings and Bonds
-- --------------------------------------------------------------------------------
--
-- bnd : (cs : List Char) -> ResI cs Err (Maybe Bond)
-- bnd ('='  :: t) = y t (Just Dbl)
-- bnd ('-'  :: t) = y t (Just Sngl)
-- bnd (':'  :: t) = y t (Just Arom)
-- bnd ('#'  :: t) = y t (Just Trpl)
-- bnd ('$'  :: t) = y t (Just Quad)
-- bnd ('/'  :: t) = y t Nothing
-- bnd ('\\' :: t) = y t Nothing
-- bnd cs         = y cs Nothing
--
-- dob : (cs : List Char) -> ResI cs Err DotOrBond
-- dob ('.' :: t) = y t Dot
-- dob cs         = mapResI (maybe NoDOB B) $ bnd cs
--
-- ringNr : (cs : List Char) -> ResS cs Err RingNr
-- ringNr ('%'::d1::d2::t) =
--   let ds = pack [d1,d2]
--    in maybe (N $ InvalidRingNr ("%" ++ ds)) (y t) $ read ds
-- ringNr (d          ::t) =
--   let ds = singleton d
--    in maybe (N $ InvalidRingNr ds) (y t) $ read ds
-- ringNr []               = N $ InvalidRingNr ""
--
-- --------------------------------------------------------------------------------
-- --          Parser
-- --------------------------------------------------------------------------------
--
-- headAlpha : List Char -> Bool
-- headAlpha (c :: _) = isAlpha c || c == '['
-- headAlpha _        = False
--
-- rngs : (cs : List Char) -> (0 _ : SuffixAcc cs) -> ST -> ResI cs Err ST
-- rngs cs1 (Access rec) st =
--   if headAlpha cs1 then y cs1 st
--   else
--     let Y b   cs2 p2 = bnd cs1
--         Y r   cs3 p3 = ringNr cs2 | N _ => y cs1 st
--         Y res cs4 p4 = rngs cs3 (rec cs3 $ p3 ~> p2) (addRing b r st)
--      in Y res cs4 $ weaken $ p4 ~> p3 ~> p2
--
-- atm' : (cs : List Char) -> DotOrBond -> Atom -> ST -> ResI cs Err ST
-- atm' cs dob a (MkST n a1 s rs g) =
--   let a2 = MkBAtom n a
--       g2 = insNode n a g
--       g3 = case dob of
--              NoDOB => addBond Nothing  a1 a2 g2
--              B b   => addBond (Just b) a1 a2 g2
--              Dot   => g2
--    in rngs cs (ssAcc cs) (MkST (n+1) a2 s rs g3)
--
-- atm : (cs : List Char) -> ST -> ResS cs Err ST
-- atm cs1 st =
--   if headAlpha cs1
--      then
--        let Y a   cs2 p2 = atom cs1 | N err => N err
--            Y st2 cs3 p3 = atm' cs2 NoDOB a st
--         in Y st2 cs3 $ p3 ~> p2
--      else
--        let Y b   cs2 p2 = dob cs1
--            Y a   cs3 p3 = atom cs2 | N err => N err
--            Y st2 cs4 p4 = atm' cs3 b a st
--         in Y st2 cs4 $ p4 ~> p3 ~> p2
--
-- prs : (cs : List Char) -> (0 _ : SuffixAcc cs) -> (st : ST) -> Result
-- prs cs (Access rec) st =
--   case atm cs st of
--     Y st2 cs2 p2 => prs cs2 (rec cs2 p2) st2
--     N err => case cs of
--       '(' :: t => case atm t $ {stack $= (st.atom ::)} st of
--          Y st2 cs2 p2 => prs cs2 (rec cs2 $ Cons p2) st2
--          N err2       => Stuck err2 t
--
--       ')' :: t => case st.stack of
--         a :: as => prs t (rec t cons1) ({stack := as, atom := a} st)
--         Nil     => Stuck UnexpectedCP (')' :: t)
--
--       []       =>
--         if null (st.rings) && null (st.stack) then End st.mol
--         else Stuck EndOfInput []
--       _        => Stuck err cs
--
--
-- export
-- parse : String -> Result
-- parse "" = End empty
-- parse s  = case atom (unpack s) of
--   N err    => Stuck err (unpack s)
--   Y a cs _ =>
--     let Y st cs2 _ = rngs cs (ssAcc cs) (MkST 1 (MkBAtom 0 a) Nil empty (insNode 0 a empty))
--      in prs cs2 (ssAcc cs2) st

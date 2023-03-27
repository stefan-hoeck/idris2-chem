module Text.Molfile.Reader.Types

import public Text.Molfile.Reader.Util
import Text.Lex.Element
import Text.Lex.Manual.Syntax

%default total

export
version : SnocList Char -> Either Error MolVersion
version  [<'v','2','0','0','0'] = Right V2000
version  [<'V','2','0','0','0'] = Right V2000
version  [<'v','3','0','0','0'] = Right V3000
version  [<'V','3','0','0','0'] = Right V3000
version  sc                     = customPack sc EVersion

export
chiralFlag : SnocList Char -> Either Error ChiralFlag
chiralFlag [<]    = Right NonChiral
chiralFlag [<'0'] = Right NonChiral
chiralFlag [<'1'] = Right Chiral
chiralFlag sc     = customPack sc EChiralFlag

-- Atom references go from 1 to 999, which means the corresponding
-- nodes go from 0 to 998.
toAtomRef : Nat -> Maybe Node
toAtomRef (S k) = if k < 999 then Just $ cast k else Nothing
toAtomRef 0     = Nothing

export %inline
node : (n : Nat) -> Tok False MolFileError Node
node n = nat n toAtomRef

export
maybeNode : (n : Nat) -> Tok False MolFileError (Maybe Node)
maybeNode n = nat n $ \case
  0 => Just Nothing
  n => Just <$> toAtomRef n

export %inline
count : Tok False MolFileError Nat
count = nat 3 Just

dot : Tok False e ()
dot ('.'::xs) = Succ () xs
dot (x::xs)   = single (Expected $ Left ".") Same
dot []        = eoiAt Same

coord : Tok False MolFileError Coordinate
coord cs = case Tok.[| coord (signed 5) dot (nat 4 Just) |] cs of
  Succ (Just v) xs      => Succ v xs
  Succ Nothing  xs @{p} => unknownRange p xs
  Fail x y z            => Fail x y z
  where
    coord : (Bool,Nat) -> () -> Nat -> Maybe Coordinate
    coord (b,n) _ k =
      let val := cast n * Precision + cast k
       in refineCoordinate $ if b then negate val else val

export
coords : Tok False MolFileError (Vect 3 Coordinate)
coords = Tok.[| (\x,y,z => [x,y,z]) coord coord coord |]

export
atomSymbol : SnocList Char -> Either Error AtomSymbol
atomSymbol sc =
  let cs := sc <>> []
   in case lexElement {e = Void} cs @{Same} of
        Succ e [] => Right (El e)
        _      => case pack cs of
          "L"  => Right L
          "A"  => Right A
          "Q"  => Right Q
          "*"  => Right Ast
          "LP" => Right LP
          "R#" => Right RSharp
          v    => custom $ ESymbol v

export
stereoParity : SnocList Char -> Either Error StereoParity
stereoParity [<'0'] = Right NoStereo
stereoParity [<'1'] = Right OddStereo
stereoParity [<'2'] = Right EvenStereo
stereoParity [<'3'] = Right AnyStereo
stereoParity [<]    = Right NoStereo
stereoParity sc     = customPack sc EStereoParity

export
stereoCareBox : SnocList Char -> Either Error StereoCareBox
stereoCareBox [<]    = Right IgnoreStereo
stereoCareBox [<'0'] = Right IgnoreStereo
stereoCareBox [<'1'] = Right MatchStereo
stereoCareBox sc     = customPack sc EStereoCareBox

export
h0designator    : SnocList Char -> Either Error H0Designator
h0designator [<]    = Right H0NotSpecified
h0designator [<'0'] = Right H0NotSpecified
h0designator [<'1'] = Right NoHAllowed
h0designator sc     = customPack sc EH0Designator

export
bondType : SnocList Char -> Either Error BondType
bondType [<'1'] = Right Single
bondType [<'2'] = Right Dbl
bondType [<'3'] = Right Triple
bondType [<'4'] = Right Aromatic
bondType [<'5'] = Right SngOrDbl
bondType [<'6'] = Right SngOrAromatic
bondType [<'7'] = Right DblOrAromatic
bondType [<'8'] = Right AnyBond
bondType sc     = customPack sc EBondType

export
bondStereo : SnocList Char -> Either Error BondStereo
bondStereo [<]    = Right NoBondStereo
bondStereo [<'0'] = Right NoBondStereo
bondStereo [<'1'] = Right Up
bondStereo [<'3'] = Right CisOrTrans
bondStereo [<'4'] = Right UpOrDown
bondStereo [<'6'] = Right Down
bondStereo sc     = customPack sc EBondStereo

export
bondTopo : SnocList Char -> Either Error BondTopo
bondTopo [<]    = Right AnyTopology
bondTopo [<'0'] = Right AnyTopology
bondTopo [<'1'] = Right Ring
bondTopo [<'2'] = Right Chain
bondTopo sc     = customPack sc EBondTopo

export
edge : (x,y : Node) -> Tok False MolFileError Edge
edge x y cs = case mkEdge x y of
  Just v  => Succ v cs
  Nothing => Fail Same cs (Custom EEdge)

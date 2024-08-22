module Text.Molfile.Reader.Types

import Text.Molfile.Reader.Util
import Text.Lex.Elem
import Text.Lex.Manual
import Text.Lex.Manual.Syntax

%default total

export
version : SnocList Char -> Either MolErr MolVersion
version  [<'v','2','0','0','0'] = Right V2000
version  [<'V','2','0','0','0'] = Right V2000
version  [<'v','3','0','0','0'] = Right V3000
version  [<'V','3','0','0','0'] = Right V3000
version  sc                     = packError sc EVersion

export
chiralFlag : SnocList Char -> Either MolErr ChiralFlag
chiralFlag [<]    = Right NonChiral
chiralFlag [<'0'] = Right NonChiral
chiralFlag [<'1'] = Right Chiral
chiralFlag sc     = packError sc EChiralFlag

export
sgroupType : SnocList Char -> Either MolErr SGroupType
sgroupType [<'S','U','P'] = Right SUP
sgroupType _              = Right Other

export %inline
node : {k : _} -> (n : Nat) -> Parser (Fin k)
node n = nat n (tryNatToFin . pred)

export
maybeNode : {k : _} -> (n : Nat) -> Parser (Maybe $ Fin k)
maybeNode n = nat n $ \case
  0   => Just Nothing
  S n => Just <$> tryNatToFin n

export %inline
count : Parser Nat
count = nat 3 Just

dot : Parser ()
dot ('.'::xs) = Right (xs, ())
dot (x::xs)   = Left (EDot x)
dot []        = Left EOI

coord : Parser Coordinate
coord cs =
  case Util.[| coord (signed 5) dot (nat 4 Just) |] cs of
    Right (xs,Just v)  => Right (xs,v)
    Right (xs,Nothing) => Left (ECoordinate $ pack cs)
    Left err           => Left err

  where
    coord : (Bool,Nat) -> () -> Nat -> Maybe Coordinate
    coord (b,n) _ k =
      let val := cast n * Precision + cast k
       in refineCoordinate $ if b then negate val else val

export
coords : Parser (Vect 3 Coordinate)
coords = Util.[| (\x,y,z => [x,y,z]) coord coord coord |]

export
isotope : SnocList Char -> Either MolErr Isotope
isotope sc =
  let cs := sc <>> []
   in case lexElement {e = Void} cs @{Same} of
        Succ e [] => Right (cast e)
        _      => case pack cs of
          "D"  => Right (MkI H $ Just 2)
          "T"  => Right (MkI H $ Just 3)
          v    => Left $ ESymbol v

export
stereoParity : SnocList Char -> Either MolErr StereoParity
stereoParity [<'0'] = Right NoStereo
stereoParity [<'1'] = Right OddStereo
stereoParity [<'2'] = Right EvenStereo
stereoParity [<'3'] = Right AnyStereo
stereoParity [<]    = Right NoStereo
stereoParity sc     = packError sc EStereoParity

export
stereoCareBox : SnocList Char -> Either MolErr StereoCareBox
stereoCareBox [<]    = Right IgnoreStereo
stereoCareBox [<'0'] = Right IgnoreStereo
stereoCareBox [<'1'] = Right MatchStereo
stereoCareBox sc     = packError sc EStereoCareBox

export
h0designator    : SnocList Char -> Either MolErr H0Designator
h0designator [<]    = Right H0NotSpecified
h0designator [<'0'] = Right H0NotSpecified
h0designator [<'1'] = Right NoHAllowed
h0designator sc     = packError sc EH0Designator

export
bondOrder : SnocList Char -> Either MolErr BondOrder
bondOrder [<'1'] = Right Single
bondOrder [<'2'] = Right Dbl
bondOrder [<'3'] = Right Triple
bondOrder sc     = packError sc EBondType

export
queryBondType : SnocList Char -> Either MolErr QueryBondType
queryBondType [<'4'] = Right Arom
queryBondType [<'5'] = Right SngOrDbl
queryBondType [<'6'] = Right SngOrAromatic
queryBondType [<'7'] = Right DblOrAromatic
queryBondType [<'8'] = Right AnyBond
queryBondType sc     = BT <$> bondOrder sc

export
bondStereo : SnocList Char -> Either MolErr BondStereo
bondStereo [<]    = Right NoBondStereo
bondStereo [<'0'] = Right NoBondStereo
bondStereo [<'1'] = Right Up
bondStereo [<'3'] = Right CisOrTrans
bondStereo [<'4'] = Right UpOrDown
bondStereo [<'6'] = Right Down
bondStereo sc     = packError sc EBondStereo

export
bondTopo : SnocList Char -> Either MolErr BondTopo
bondTopo [<]    = Right AnyTopology
bondTopo [<'0'] = Right AnyTopology
bondTopo [<'1'] = Right Ring
bondTopo [<'2'] = Right Chain
bondTopo sc     = packError sc EBondTopo

export
charge : Nat -> Maybe Charge
charge 0 = Just 0
charge 1 = Just 3
charge 2 = Just 2
charge 3 = Just 1
charge 5 = Just (-1)
charge 6 = Just (-2)
charge 7 = Just (-3)
charge _ = Nothing

export
edge : (x,y : Fin k) -> a -> Parser (Edge k a)
edge x y z cs = case mkEdge x y z of
  Just v  => Right (cs, v)
  Nothing => Left EEdge

module Text.Lex.Element

import Chem.Element
import Text.Bounds
import Text.FC
import Text.Lex.Manual

%default total

||| A lexer for chemical elements.
public export
lexElement : StrictTok e Elem
lexElement ('A' :: xs) = case xs of
   'c' :: t  => Succ Ac t
   'g' :: t  => Succ Ag t
   'l' :: t  => Succ Al t
   'm' :: t  => Succ Am t
   'r' :: t  => Succ Ar t
   's' :: t  => Succ As t
   't' :: t  => Succ At t
   'u' :: t  => Succ Au t
   _         => unknownRange p xs
lexElement ('B' :: xs) = case xs of
   'a' :: t  => Succ Ba t
   'e' :: t  => Succ Be t
   'h' :: t  => Succ Bh t
   'i' :: t  => Succ Bi t
   'k' :: t  => Succ Bk t
   'r' :: t  => Succ Br t
   _         => Succ B xs
lexElement ('C' :: xs) = case xs of
   'a' :: t  => Succ Ca t
   'd' :: t  => Succ Cd t
   'e' :: t  => Succ Ce t
   'f' :: t  => Succ Cf t
   'l' :: t  => Succ Cl t
   'm' :: t  => Succ Cm t
   'n' :: t  => Succ Cn t
   'o' :: t  => Succ Co t
   'r' :: t  => Succ Cr t
   's' :: t  => Succ Cs t
   'u' :: t  => Succ Cu t
   _         => Succ C xs
lexElement ('D' :: xs) = case xs of
   'b' :: t  => Succ Db t
   's' :: t  => Succ Ds t
   'y' :: t  => Succ Dy t
   _         => unknownRange p xs
lexElement ('E' :: xs) = case xs of
   'r' :: t  => Succ Er t
   's' :: t  => Succ Es t
   'u' :: t  => Succ Eu t
   _         => unknownRange p xs
lexElement ('F' :: xs) = case xs of
   'e' :: t  => Succ Fe t
   'l' :: t  => Succ Fl t
   'm' :: t  => Succ Fm t
   'r' :: t  => Succ Fr t
   _         => Succ F xs
lexElement ('G' :: xs) = case xs of
   'a' :: t  => Succ Ga t
   'd' :: t  => Succ Gd t
   'e' :: t  => Succ Ge t
   _         => unknownRange p xs
lexElement ('H' :: xs) = case xs of
   'e' :: t  => Succ He t
   'f' :: t  => Succ Hf t
   'g' :: t  => Succ Hg t
   'o' :: t  => Succ Ho t
   's' :: t  => Succ Hs t
   _         => Succ H xs
lexElement ('I' :: xs) = case xs of
   'n' :: t  => Succ In t
   'r' :: t  => Succ Ir t
   _         => Succ I xs
lexElement ('K' :: xs) = case xs of
   'r' :: t  => Succ Kr t
   _         => Succ K xs
lexElement ('L' :: xs) = case xs of
   'a' :: t  => Succ La t
   'i' :: t  => Succ Li t
   'r' :: t  => Succ Lr t
   'u' :: t  => Succ Lu t
   'v' :: t  => Succ Lv t
   _         => unknownRange p xs
lexElement ('M' :: xs) = case xs of
   'c' :: t  => Succ Mc t
   'd' :: t  => Succ Md t
   'g' :: t  => Succ Mg t
   'n' :: t  => Succ Mn t
   'o' :: t  => Succ Mo t
   't' :: t  => Succ Mt t
   _         => unknownRange p xs
lexElement ('N' :: xs) = case xs of
   'a' :: t  => Succ Na t
   'b' :: t  => Succ Nb t
   'd' :: t  => Succ Nd t
   'e' :: t  => Succ Ne t
   'h' :: t  => Succ Nh t
   'i' :: t  => Succ Ni t
   'o' :: t  => Succ No t
   'p' :: t  => Succ Np t
   _         => Succ N xs
lexElement ('O' :: xs) = case xs of
   'g' :: t  => Succ Og t
   's' :: t  => Succ Os t
   _         => Succ O xs
lexElement ('P' :: xs) = case xs of
   'a' :: t  => Succ Pa t
   'b' :: t  => Succ Pb t
   'd' :: t  => Succ Pd t
   'm' :: t  => Succ Pm t
   'o' :: t  => Succ Po t
   'r' :: t  => Succ Pr t
   't' :: t  => Succ Pt t
   'u' :: t  => Succ Pu t
   _         => Succ P xs
lexElement ('R' :: xs) = case xs of
   'a' :: t  => Succ Ra t
   'b' :: t  => Succ Rb t
   'e' :: t  => Succ Re t
   'f' :: t  => Succ Rf t
   'g' :: t  => Succ Rg t
   'h' :: t  => Succ Rh t
   'n' :: t  => Succ Rn t
   'u' :: t  => Succ Ru t
   _         => unknownRange p xs
lexElement ('S' :: xs) = case xs of
   'b' :: t  => Succ Sb t
   'c' :: t  => Succ Sc t
   'e' :: t  => Succ Se t
   'g' :: t  => Succ Sg t
   'i' :: t  => Succ Si t
   'm' :: t  => Succ Sm t
   'n' :: t  => Succ Sn t
   'r' :: t  => Succ Sr t
   _         => Succ S xs
lexElement ('T' :: xs) = case xs of
   'a' :: t  => Succ Ta t
   'b' :: t  => Succ Tb t
   'c' :: t  => Succ Tc t
   'e' :: t  => Succ Te t
   'h' :: t  => Succ Th t
   'i' :: t  => Succ Ti t
   'l' :: t  => Succ Tl t
   'm' :: t  => Succ Tm t
   's' :: t  => Succ Ts t
   _         => unknownRange p xs
lexElement ('U' :: xs) = Succ U xs
lexElement ('V' :: xs) = Succ V xs
lexElement ('W' :: xs) = Succ W xs
lexElement ('X' :: 'e' :: xs) = Succ Xe xs
lexElement ('Y' :: 'b' :: xs) = Succ Yb xs
lexElement ('Y' :: xs) = Succ Y xs
lexElement ('Z' :: 'n' :: xs) = Succ Zn xs
lexElement ('Z' :: 'r' :: xs) = Succ Zr xs
lexElement (x::xs) = unknown p
lexElement []      = eoiAt p

public export %inline
readElement : String -> Maybe Elem
readElement str = case lexElement {e = Void} (unpack str) @{Same} of
  Succ v [] => Just v
  _         => Nothing

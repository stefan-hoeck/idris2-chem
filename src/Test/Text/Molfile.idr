module Test.Text.Molfile

import Chem.Element
import Chem.Types

import Data.Refined
import Data.String

import Test.Chem.Element
import Text.Molfile.Types

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

molVersionRW : (v : MolVersion) -> Just v = read (write v)
molVersionRW V2000 = Refl
molVersionRW V3000 = Refl

chiralFlagRW : (v : ChiralFlag) -> Just v = read (write v)
chiralFlagRW NonChiral = Refl
chiralFlagRW Chiral    = Refl

atomSymbolRW : (v : AtomSymbol) -> Just v = read (write v)
atomSymbolRW L        = Refl
atomSymbolRW A        = Refl
atomSymbolRW Q        = Refl
atomSymbolRW Ast      = Refl
atomSymbolRW LP       = Refl
atomSymbolRW RSharp   = Refl
atomSymbolRW (El H)   = Refl
atomSymbolRW (El He)  = Refl
atomSymbolRW (El Li)  = Refl
atomSymbolRW (El Be)  = Refl
atomSymbolRW (El B)   = Refl
atomSymbolRW (El C)   = Refl
atomSymbolRW (El N)   = Refl
atomSymbolRW (El O)   = Refl
atomSymbolRW (El F)   = Refl
atomSymbolRW (El Ne)  = Refl
atomSymbolRW (El Na)  = Refl
atomSymbolRW (El Mg)  = Refl
atomSymbolRW (El Al)  = Refl
atomSymbolRW (El Si)  = Refl
atomSymbolRW (El P)   = Refl
atomSymbolRW (El S)   = Refl
atomSymbolRW (El Cl)  = Refl
atomSymbolRW (El Ar)  = Refl
atomSymbolRW (El K)   = Refl
atomSymbolRW (El Ca)  = Refl
atomSymbolRW (El Sc)  = Refl
atomSymbolRW (El Ti)  = Refl
atomSymbolRW (El V)   = Refl
atomSymbolRW (El Cr)  = Refl
atomSymbolRW (El Mn)  = Refl
atomSymbolRW (El Fe)  = Refl
atomSymbolRW (El Co)  = Refl
atomSymbolRW (El Ni)  = Refl
atomSymbolRW (El Cu)  = Refl
atomSymbolRW (El Zn)  = Refl
atomSymbolRW (El Ga)  = Refl
atomSymbolRW (El Ge)  = Refl
atomSymbolRW (El As)  = Refl
atomSymbolRW (El Se)  = Refl
atomSymbolRW (El Br)  = Refl
atomSymbolRW (El Kr)  = Refl
atomSymbolRW (El Rb)  = Refl
atomSymbolRW (El Sr)  = Refl
atomSymbolRW (El Y)   = Refl
atomSymbolRW (El Zr)  = Refl
atomSymbolRW (El Nb)  = Refl
atomSymbolRW (El Mo)  = Refl
atomSymbolRW (El Tc)  = Refl
atomSymbolRW (El Ru)  = Refl
atomSymbolRW (El Rh)  = Refl
atomSymbolRW (El Pd)  = Refl
atomSymbolRW (El Ag)  = Refl
atomSymbolRW (El Cd)  = Refl
atomSymbolRW (El In)  = Refl
atomSymbolRW (El Sn)  = Refl
atomSymbolRW (El Sb)  = Refl
atomSymbolRW (El Te)  = Refl
atomSymbolRW (El I)   = Refl
atomSymbolRW (El Xe)  = Refl
atomSymbolRW (El Cs)  = Refl
atomSymbolRW (El Ba)  = Refl
atomSymbolRW (El La)  = Refl
atomSymbolRW (El Ce)  = Refl
atomSymbolRW (El Pr)  = Refl
atomSymbolRW (El Nd)  = Refl
atomSymbolRW (El Pm)  = Refl
atomSymbolRW (El Sm)  = Refl
atomSymbolRW (El Eu)  = Refl
atomSymbolRW (El Gd)  = Refl
atomSymbolRW (El Tb)  = Refl
atomSymbolRW (El Dy)  = Refl
atomSymbolRW (El Ho)  = Refl
atomSymbolRW (El Er)  = Refl
atomSymbolRW (El Tm)  = Refl
atomSymbolRW (El Yb)  = Refl
atomSymbolRW (El Lu)  = Refl
atomSymbolRW (El Hf)  = Refl
atomSymbolRW (El Ta)  = Refl
atomSymbolRW (El W)   = Refl
atomSymbolRW (El Re)  = Refl
atomSymbolRW (El Os)  = Refl
atomSymbolRW (El Ir)  = Refl
atomSymbolRW (El Pt)  = Refl
atomSymbolRW (El Au)  = Refl
atomSymbolRW (El Hg)  = Refl
atomSymbolRW (El Tl)  = Refl
atomSymbolRW (El Pb)  = Refl
atomSymbolRW (El Bi)  = Refl
atomSymbolRW (El Po)  = Refl
atomSymbolRW (El At)  = Refl
atomSymbolRW (El Rn)  = Refl
atomSymbolRW (El Fr)  = Refl
atomSymbolRW (El Ra)  = Refl
atomSymbolRW (El Ac)  = Refl
atomSymbolRW (El Th)  = Refl
atomSymbolRW (El Pa)  = Refl
atomSymbolRW (El U)   = Refl
atomSymbolRW (El Np)  = Refl
atomSymbolRW (El Pu)  = Refl
atomSymbolRW (El Am)  = Refl
atomSymbolRW (El Cm)  = Refl
atomSymbolRW (El Bk)  = Refl
atomSymbolRW (El Cf)  = Refl
atomSymbolRW (El Es)  = Refl
atomSymbolRW (El Fm)  = Refl
atomSymbolRW (El Md)  = Refl
atomSymbolRW (El No)  = Refl
atomSymbolRW (El Lr)  = Refl
atomSymbolRW (El Rf)  = Refl
atomSymbolRW (El Db)  = Refl
atomSymbolRW (El Sg)  = Refl
atomSymbolRW (El Bh)  = Refl
atomSymbolRW (El Hs)  = Refl
atomSymbolRW (El Mt)  = Refl
atomSymbolRW (El Ds)  = Refl
atomSymbolRW (El Rg)  = Refl
atomSymbolRW (El Cn)  = Refl
atomSymbolRW (El Uut) = Refl
atomSymbolRW (El Fl)  = Refl
atomSymbolRW (El Uup) = Refl
atomSymbolRW (El Lv)  = Refl
atomSymbolRW (El Uus) = Refl
atomSymbolRW (El Uuo) = Refl

stereoParityRW : (v : StereoParity) -> Just v = read (write v)
stereoParityRW NoStereo   = Refl
stereoParityRW OddStereo  = Refl
stereoParityRW EvenStereo = Refl
stereoParityRW AnyStereo  = Refl

stereoCareBoxRW : (v : StereoCareBox) -> Just v = read (write v)
stereoCareBoxRW IgnoreStereo = Refl
stereoCareBoxRW MatchStereo  = Refl

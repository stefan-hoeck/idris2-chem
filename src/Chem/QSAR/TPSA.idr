module Chem.QSAR.TPSA

import Chem
import Chem.Aromaticity
import Chem.AtomType
import Chem.QSAR.Util
import Data.Graph.Indexed.Ring.Util
import Data.SortedMap
import Derive.Prelude

%language ElabReflection
%default total

record Profile where
  constructor P
  elem      : Elem
  hcnt      : Nat
  chrg      : Charge
  aromBonds : Nat
  in3ring   : Bool
  bnds      : Bonds

%runElab derive "Profile" [Show,Eq,Ord]

contribs : SortedMap Profile Double
contribs =
  SortedMap.fromList
    [ (P N 0 0 0 False $ BS 3 0 0, 3.24) -- 1
    , (P N 0 0 0 False $ BS 1 1 0, 12.36) -- 2
    , (P N 0 0 0 False $ BS 0 0 1, 23.79) -- 3
    , (P N 0 0 0 False $ BS 1 2 0, 11.68) -- 4
    , (P N 0 0 0 False $ BS 0 1 1, 13.6) -- 5
    , (P N 0 0 0 True $ BS 3 0 0, 3.01) -- 6
    , (P N 1 0 0 False $ BS 3 0 0, 12.03) -- 7
    , (P N 1 0 0 True $ BS 3 0 0, 21.94) -- 8
    , (P N 1 0 0 False $ BS 1 1 0, 23.85) --9
    , (P N 2 0 0 False $ BS 3 0 0, 26.02) -- 10
    , (P N 0 1 0 False $ BS 4 0 0, 0.0) --11
    , (P N 0 1 0 False $ BS 2 1 0, 3.01) --12
    , (P N 0 1 0 False $ BS 1 0 1, 4.36) --13
    , (P N 1 1 0 False $ BS 4 0 0, 4.44) --14
    , (P N 1 1 0 False $ BS 2 1 0, 13.97) --15
    , (P N 2 1 0 False $ BS 4 0 0, 16.61) --16
    , (P N 2 1 0 False $ BS 2 1 0, 25.59) --17
    , (P N 3 1 0 False $ BS 4 0 0, 27.64) --18
    , (P N 0 0 2 False $ BS 0 0 0, 12.89) --19
    , (P N 0 0 3 False $ BS 0 0 0, 4.41) --20
    , (P N 0 0 2 False $ BS 1 0 0, 4.93) --21
    , (P N 0 0 2 False $ BS 0 1 0, 8.39) --22
    , (P N 1 0 2 False $ BS 1 0 0, 15.79) --23
    , (P N 0 1 3 False $ BS 0 0 0, 4.1) --24
    , (P N 0 1 2 False $ BS 1 0 0, 3.88) --25
    , (P N 1 1 2 False $ BS 1 0 0, 14.14) --26
    
    , (P O 0 0 0 False $ BS 2 0 0, 9.23) --27
    , (P O 0 0 0 True $ BS 2 0 0, 12.53) --28
    , (P O 0 0 0 False $ BS 0 1 0, 17.07) --29
    , (P O 0 (-1) 0 False $ BS  1 0 0, 23.06) --30
    , (P O 1 0 0 False $ BS 2 0 0, 20.23) --31
    , (P O 0 0 2 False $ BS 0 0 0, 13.14) --32
   
    , (P S 0 0 0 False $ BS 2 0 0, 25.3) --33
    , (P S 0 0 0 False $ BS 0 1 0, 32.09) --34
    , (P S 0 0 0 False $ BS 2 1 0, 19.21) --35
    , (P S 0 0 0 False $ BS 2 2 0, 8.38) --36
    , (P S 1 0 0 False $ BS 2 0 0, 38.8) --37
    , (P S 0 0 2 False $ BS 0 0 0, 28.24) --38
    , (P S 0 0 2 False $ BS 0 1 0, 21.7) --39
  
    , (P P 0 0 0 False $ BS 3 0 0, 13.59) --40
    , (P P 0 0 0 False $ BS 1 1 0, 34.14) --41
    , (P P 0 0 0 False $ BS 3 1 0, 9.81) --42
    , (P P 1 0 0 False $ BS 3 1 0, 23.47) --43
    ]

parameters {0 b,e,p,r,t,ch,l : Type}
           {auto ce : Cast e Elem}
           {auto cb : Cast b BondOrder}
           {k       : Nat}
           (g       : IGraph k (AromBond b) (Atom e Charge p r HCount t ch l))

  contrib : Elem -> Fin k -> Double
  contrib el n =
    let A a ns := adj g n
        implHs := a.hydrogen
        hc     := cast implHs.value + countElems g H ns 
        tm     := inThreeMemberedRing g n
        pro    := P el hc a.charge (count arom ns) tm (nonAromaticBonds implHs ns)
     in fromMaybe 0.0 $ lookup pro contribs

  ||| Computes the contribution to the total polar surface area (TPSA)
  ||| from a single atom.
  export
  tpsaContrib : Fin k -> Double
  tpsaContrib n =
    case cast @{ce} $ elem $ lab g n of
      O => contrib O n
      N => contrib N n
      S => contrib S n
      P => contrib P n
      _ => 0.0


  ||| Computes the total polar surface area (TPSA) of a molecule.
  export
  tpsa : Double
  tpsa = foldl (\x,v => x + tpsaContrib v) 0.0 (nodes g)

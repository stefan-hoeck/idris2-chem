||| This computes the logP in accordance with the JLogP module in
||| the CDK.
|||
||| This was published in the
||| [J. Chem. Inf.](https://jcheminf.biomedcentral.com/articles/10.1186/s13321-018-0316-5)
module Chem.QSAR.JPlogP

import Chem
import Chem.Aromaticity
import Chem.QSAR.Util
import Data.SortedMap

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

isPolar : Elem -> Bool
isPolar O = True
isPolar N = True
isPolar S = True
isPolar P = True
isPolar _ = False

isElectronWithdrawing : Elem -> Bool
isElectronWithdrawing O  = True
isElectronWithdrawing N  = True
isElectronWithdrawing S  = True
isElectronWithdrawing F  = True
isElectronWithdrawing Cl = True
isElectronWithdrawing Br = True
isElectronWithdrawing I  = True
isElectronWithdrawing _  = False

-- fast failing addition of floating point values with the potential of failure
sumMaybes : Double -> (a -> Maybe Double) -> List a -> Maybe Double
sumMaybes v f []      = Just v
sumMaybes v f (x::xs) =
  case f x of
    Just y  => sumMaybes (v+y) f xs
    Nothing => Nothing

-- list of pairs at the bottom of the source file
weights : SortedMap Nat Double

parameters {0 b,e,p,r,t,c,l : Type}
           {auto ce : Cast e Elem}
           {auto cb : Cast b BondOrder}
           {k       : Nat}
           (g       : IGraph k (AromBond b) (Atom e Charge p r HCount t c l))

  subsel : Elem -> HCount -> AssocList k (AromBond b) -> Nat

  hydrogenSpecial : List (Fin k) -> Nat

  hydrogenCode : Fin k -> Nat
  hydrogenCode n = 101_100 + hydrogenSpecial [n]

  -- returns an atom code in the form CAANSS where
  -- C  = charge+1
  -- AA = Atomic Number
  -- N  = NonH Neighbour count
  -- SS = elemental subselection via bonding and neighbour identification
  atomCode : Fin k -> Nat
  atomCode n =
    let A a ns := adj g n
        el     := cast @{ce} (elem a)
        chrg   := a.charge.value + 1
        nonHs  := countNonHs g ns
        anum   := cast {to = Nat} $ value $ atomicNr el
        add    := subsel el a.hydrogen ns
     in if add > 99 || anum > 99 || nonHs > 9 || chrg < 0
           then 0
           else cast chrg * 100_000 + anum * 1000 + nonHs * 100 + add

  ||| Computes the logP contribution for a single atom and its
  ||| implicit hydrogen atoms.
  |||
  ||| Returns `Nothing` in case the atom is of an unsupported element
  ||| or connectivity.
  export
  jpLogPContrib : Fin k -> Maybe Double
  jpLogPContrib n =
    case hydrogen $ lab g n of
      0 => lookup (atomCode n) weights
      h =>
        let Just cn := lookup (atomCode n) weights     | _ => Nothing
            Just ch := lookup (hydrogenCode n) weights | _ => Nothing
         in Just $ cast h.value * ch + cn
  
  ||| Sums up the logP contributions for all atoms in a molecule.
  |||
  ||| Returns `Nothing` in case `jpLogPContrib` returns `Nothing` for
  ||| at least one atom.
  export %inline
  jpLogP : Maybe Double
  jpLogP = sumMaybes 0.0 jpLogPContrib (nodes g)

--------------------------------------------------------------------------------
-- Implementation
--------------------------------------------------------------------------------

  addBond : (Elem -> Bool) -> AromBonds -> (Fin k, AromBond b) -> AromBonds
  addBond p bs (n,AB t ar) =
    let True  := p (elemAt g n) | False => bs
        False := ar             | True  => {arom $= S} bs
     in case cast @{cb} t of
          Single => {single $= S} bs
          Dbl    => {double $= S} bs
          Triple => {triple $= S} bs

  bondsWhere : (Elem -> Bool) -> AssocList k (AromBond b) -> AromBonds
  bondsWhere p = foldl (addBond p) (ABS 0 0 0 0) . pairs

  bondCount : Fin k -> Nat
  bondCount n = let A a ns := adj g n in numNeighbours a ns

  -- formal oxidation state computed from the bond order of
  -- electron withdrawing neighbours.
  formalOx : Fin k -> Nat
  formalOx = foldl acc 0 . neighboursAsPairs g
    where
      acc : Nat -> (Fin k, AromBond b) -> Nat
      acc c (n,b) =
        case (isElectronWithdrawing (elemAt g n), cast @{cb} b.type) of
          (True, Single) => c + 1
          (True, Dbl)    => c + 2
          (True, Triple) => c + 3
          _              => c

  alphaCarbonyl : Elem -> AssocList k (AromBond b) -> Bool
  alphaCarbonyl el = any (hasNeighbour g el Single) . keys

  nextToAromatic : AssocList k (AromBond b) -> Bool
  nextToAromatic ns =
    not (any AromBond.arom ns) &&
    any (\(n,b) => Single == cast b && isAromatic g n) (pairs ns)

  doubleBondHetero : AssocList k (AromBond b) -> Bool
  doubleBondHetero =
    any (\(n,AB t b) => not b && cast t == Dbl && isPolar (elemAt g n)) . pairs

  isCarbonyl : (Fin k, AromBond b) -> Bool
  isCarbonyl (n, AB t b) =
    not b && cast t == Single && doubleBondHetero (neighboursAsAL g n)

  fluorineSpecial : List (Fin k) -> Nat
  fluorineSpecial [n] =
    case elemAt g n of
      S => 8 -- F-S
      B => 9 -- F-B
      C => case bondCount n of
        2 => 2
        3 => 3
        4 => if formalOx n <= 2 then 5 else 7
        _ => 99
      _ => 1 -- F-hetero
  fluorineSpecial _  = 99

  oxygenSpecial : HCount -> AssocList k (AromBond b) -> Nat
  oxygenSpecial h ns =
    case cast h.value + length ns of
      2 =>
        if      hasElem g N ns then 1
        else if hasElem g S ns then 2
        else if any AromBond.arom ns then 8
        else    3
      1 =>
        if      hasElem g N ns then 4
        else if hasElem g S ns then 5
        else if alphaCarbonyl O ns then 6
        else if alphaCarbonyl N ns then 9
        else if alphaCarbonyl S ns then 10
        else    7
      _ => 0

  nitrogenSpecial : HCount -> AssocList k (AromBond b) -> Nat
  nitrogenSpecial h ns =
    case cast h.value + length ns of
      4 => 9
      3 =>
        if      nextToAromatic ns                  then 1
        else if any isCarbonyl (pairs ns)          then 2
        else if doubleBondHetero ns                then 10
        else if single (bondsWhere isPolar ns) > Z then 3
        else                                 4
      2 =>
        if      any AromBond.arom ns then 5
        else if doubleBondHetero ns  then 6
        else                              7
      1 => 8
      _ => 0

  carbonSpecial : HCount -> AssocList k (AromBond b) -> Nat
  carbonSpecial h ns =
    case cast h.value + length ns of
      4 => if single (bondsWhere isPolar ns) > Z then 3 else 2
      3 => case any AromBond.arom ns of
        True => case bondsWhere isPolar ns of
          ABS 0 (S _) _ _ => 11
          ABS 1 0     _ _ => 5
          ABS 1 _     _ _ => 13
          _              => 4
        False => case bondsWhere isPolar ns of
          ABS 0     _ 1 _ => 7
          ABS _     _ 1 _ => 14
          ABS (S _) _ 0 _ => 8
          _              => 6
      2 => case bondsWhere isPolar ns of
        ABS 0 _ _ 1 => 12
        ABS 1 _ _ 0 => 10
        ABS 1 _ _ 1 => 15
        _          => 9
      _ => if numBonds (bondsWhere isPolar ns) > Z then 1 else 0

  hydrogenSpecial [n] =
    let A a ns := adj g n
     in case cast @{ce} (elem a) of
          C => case any isCarbonyl (pairs ns) of
            True  => 51
            False => case numNeighbours a ns of
              4 => case formalOx n of
                0 => 46
                1 => 47
                2 => 48
                _ => 49
              3 => case formalOx n of
                0 => 47
                1 => 48
                _ => 49
              2 => case formalOx n of
                0 => 48
                _ => 49
              1 => 121
              _ => 0
          _ => 50
  hydrogenSpecial _   = 0

  subsel C h ns = carbonSpecial h ns
  subsel N h ns = nitrogenSpecial h ns
  subsel O h ns = oxygenSpecial h ns
  subsel H h ns = hydrogenSpecial (keys ns)
  subsel F h ns = fluorineSpecial (keys ns)
  subsel _ h ns =
    if any AromBond.arom ns then 10 else numBonds $ bondsWhere isPolar ns
-- -- 
-- -- 

weights =
  fromList
    [ (115201, 0.09994758075256505)
    , (115200, 0.3379378715836258)
    , (134400, -0.601185704550091)
    , (115202, 0.30788026393512663)
    , (207110, -0.26496784659823264)
    , (134404, -1.1724223083800398)
    , (115210, -0.08346526510422402)
    , (153100, 0.9270429695306335)
    , (153101, 1.0145354986151272)
    , (116503, 0.4425591506257104)
    , (133402, -0.2557512835716269)
    , (114200, 0.01526633068977459)
    , (133403, -0.8169297847709985)
    , (5401, 0.10441747048024147)
    , (101147, 1.2616122128062803)
    , (5402, 0.05162677089603265)
    , (101146, 1.3994445700193028)
    , (133401, -0.3639701318790265)
    , (5403, 0.6788714142147848)
    , (101149, 1.3258747052968567)
    , (101148, 1.2711079053599976)
    , (101151, 1.2556350911435799)
    , (133404, -0.6891007636859257)
    , (101150, -0.2363827296335956)
    , (107301, 0.1787473725640726)
    , (107303, -0.016959741231455404)
    , (107302, 0.17510323694483412)
    , (7207, -0.1902718970453204)
    , (107304, 0.1542614658530209)
    , (109101, 0.41374364339440817)
    , (115501, -0.14068629542864905)
    , (115500, 0.17750686328369028)
    , (115503, 0.013887172778612027)
    , (109103, 0.26651823980406203)
    , (115502, -0.11992335751384754)
    , (115505, -0.34311166776744884)
    , (109105, 0.43019405241170144)
    , (115504, -0.1025811855926768)
    , (207409, -0.23852255872700964)
    , (109107, 0.46487210540519147)
    , (109109, 0.4801727828186138)
    , (109108, 0.2430918227919903)
    , (134202, -0.631693669606887)
    , (134200, -0.04910253697266963)
    , (134201, 0.011171177597208612)
    , (106303, -1.5239332211866237)
    , (106302, -1.3023723757750838)
    , (106305, 0.11154050989797104)
    , (134210, 0.8725452294362313)
    , (106304, 0.20930194677993302)
    , (106307, -0.2690238196488019)
    , (106306, 0.01713355115342431)
    , (108101, -0.09994092418236927)
    , (106308, 0.026068238656834854)
    , (108103, 0.009836423634389751)
    , (106311, 0.1427758223243856)
    , (108102, 0.09143879448168145)
    , (108105, -0.4749180976677123)
    , (106313, 0.2897701159093737)
    , (108104, 0.015474674863268114)
    , (108107, 0.03602987937616161)
    , (108106, 0.19048034389371205)
    , (106314, -0.39178934954486583)
    , (108109, -0.10666832936758427)
    , (116301, -0.04914876490157527)
    , (116300, 0.7367961788572792)
    , (116303, -0.16169601215900375)
    , (116302, -0.12643665926860584)
    , (108110, 0.08928780909185945)
    , (5201, 0.2201279736215536)
    , (5202, 0.19045980382858146)
    , (133200, -0.3076946592117401)
    , (208208, 0.7099234399396344)
    , (133201, -0.49680932374826)
    , (105301, -0.1621399782797916)
    , (105300, -0.174370011345452)
    , (105303, -0.1432571497021001)
    , (105302, -0.17755682989875274)
    , (107101, 0.051702151541644426)
    , (107103, -0.2691841786263712)
    , (107102, 0.06496457627779738)
    , (107104, -0.33802382979998147)
    , (107107, 0.394978253857827)
    , (107106, 0.3859974866654674)
    , (207207, -0.07239795705976523)
    , (115301, -0.023836916386805847)
    , (107108, 0.11642255395641928)
    , (207206, -0.24558051744952064)
    , (115300, 0.08797456644925557)
    , (115303, -0.23605983536956895)
    , (115302, -0.10814292962539623)
    , (117101, 0.7369857420763359)
    , (117100, 0.7116079866622599)
    , (153200, 0.7888787630537003)
    , (106103, -3.767115237033892)
    , (106102, -3.616478490407742)
    , (116600, 1.2424471654297324)
    , (106107, -2.416958126564593)
    , (106106, -2.0565095206356196)
    , (114301, -0.13761744158191205)
    , (106109, -0.929959267287108)
    , (114300, -0.3058393642193975)
    , (114302, -0.3095457315739295)
    , (106112, -1.3012751020335893)
    , (116101, 1.2551746199963494)
    , (116100, 0.7001698255404422)
    , (105100, 0.36881886842575007)
    , (216210, 0.7113783097640652)
    , (134302, -0.37554769340770927)
    , (134303, -0.36036185997589393)
    , (115100, 0.6096777283013224)
    , (134300, -0.4657894122488925)
    , (134301, -0.3795150596315356)
    , (106403, -0.6035455702256183)
    , (106402, -0.19123067665076543)
    , (8104, -0.24195926611016633)
    , (108201, 0.030702954811754002)
    , (8105, -0.4215369017701643)
    , (108203, 0.16547595574733062)
    , (8106, -0.2964579842443157)
    , (108202, 0.12058552604519218)
    , (116401, 0.7460081218102875)
    , (116400, 0.9078902724309305)
    , (108208, 0.06665724849079398)
    , (116403, 0.3132146936243478)
    , (116402, 0.5536499705080733)
    , (133302, -0.7030388263360682)
    , (114100, 0.3587262776601395)
    , (133303, -0.4317778955330324)
    , (116404, 0.0372737885433136)
    , (133300, -0.2042709645502799)
    , (133301, 0.25473886515880656)
    , (135100, 0.8603892414982898)
    , (135101, 0.7235643505309818)
    , (107201, 0.25454958160787483)
    , (107203, 0.20036994532453556)
    , (107202, 0.15973823557158393)
    , (107205, -0.2543417785988061)
    , (7108, 0.2634019114789942)
    , (207303, -0.47290811359153156)
    , (107204, 0.1275311923081761)
    , (207302, 0.24535814336356004)
    , (107207, 0.3145047278208787)
    , (207301, 0.36070459894156437)
    , (107206, 0.3113299058370724)
    , (115401, -0.33332080419904164)
    , (115400, -0.10861521692106911)
    , (115403, -0.7356011823089021)
    , (207304, -0.07464529856367844)
    , (115402, -0.37912343134016635)
    , (115404, -0.8103937160471404)
    , (207310, 0.35707776316923207)
    , (153302, 0.6015475892374368)
    , (134100, -0.1363315394071071)
    , (134101, 0.1092440266426836)
    , (153301, 0.5748646504612611)
    , (106203, -2.6563042881537227)
    , (106202, -2.349643420766774)
    , (106204, -0.953850490807928)
    , (106207, -1.5339493033443787)
    , (106206, -1.0109064714897187)
    , (106209, 0.19490613802180773)
    , (114401, -0.16389842380630032)
    , (106208, -1.195325147036)
    , (114400, -0.11455385699777243)
    , (106211, -1.1770219185049515)
    , (114403, -0.1553108949228919)
    , (114402, -0.1103226433176957)
    , (106210, 0.16163164657523407)
    , (106212, -0.2512600932013654)
    , (114404, -0.13111265719465162)
    , (106215, -0.14610561930731214)
    , (106214, -1.6084019086078098)
    , (116201, 0.6390448917281739)
    , (116200, 0.7928741182178681)
    , (116202, 0.5335850658686033)
    , (216301, 0.16768140357444056)
    , (216300, 0.8104414861979382)
    , (105201, 0.06904337130830694)
    , (105202, -0.0745914491562598)
    , (116210, 0.5791544003852439)
    , (216310, 0.16982252294512776)
    ]

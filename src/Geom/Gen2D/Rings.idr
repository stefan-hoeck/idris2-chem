module Geom.Gen2D.Rings

import Chem
import Geom.Gen2D.Place
import Geom.Gen2D.State
import Geom.Gen2D.Types
import Geom.Interpolate
import Data.Graph.Indexed.Ring.Relevant
import Data.SortedSet
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Types and Ring Analysis
--------------------------------------------------------------------------------

0 Cycles : Graph e n -> Type
Cycles = List . Cycle

data BridgeType = Fused | Spiro | Brdg | Fresh | Partitioned

%runElab derive "BridgeType" [Show,Eq,Ord]

record Bridge (g : Graph e n) where
  constructor B
  cycle : Cycle g
  start : Node g
  first : Node g
  rem   : Nodes g
  end   : Node g
  type  : BridgeType

natoms : Cycle g -> List (Cycle g) -> Nat
natoms c = sum . map (numSharedNodes c)

mostComplex :
     SnocList (Cycle g)
  -> List (Cycle g)
  -> (atms, len : Nat)
  -> Cycle g
  -> (Cycle g, List (Cycle g))
mostComplex sx []      atms len r = (r, sx <>> [])
mostComplex sx (x::xs) atms len r =
 let n := natoms x (sx <>> (r::xs))
  in case compare n atms of
       LT => mostComplex (sx:<x) xs atms len r
       GT => mostComplex (sx:<r) xs n    x.ncycle.size x
       EQ => case len >= x.ncycle.size of
         True  => mostComplex (sx:<x) xs atms len r
         False => mostComplex (sx:<r) xs n    x.ncycle.size x

partOf : Bridge g -> Cycle g -> Bool
partOf b c = numSharedNodes b.cycle c > 0

-- splits a cycle into non-empty segments of placed and unplaced nodes.
toBridge : PlaceST s g => Cycle g -> F1 s (Maybe $ Bridge g)
toBridge c t =
  case break1 isPlaced c.nodes t of
    (u::us,[])  # t => Just (B c u u us u Fresh) # t -- all unplaced
    (us,[]    ) # t => Nothing # t                   -- all placed
    (us,p::rem) # t =>
     let Just (b,p2,ns2) # t := nxt p  (rem++us++[p]) t | _ # t => Nothing # t
         Just _          # t := nxt p2 ns2            t | _ # t => Just b # t
      in Just ({type := Partitioned} b) # t
  where
    tpe : Node g -> Node g -> BridgeType
    tpe x y =
     case mkEdg x y of
       Just e  => if contains e c.edgeset then Fused else Brdg
       Nothing => Spiro

    nxt : Node g -> Nodes g -> F1 s (Maybe (Bridge g, Node g, Nodes g))
    nxt p ns = T1.do
      -- first, take placed prefix, then take until placed again
      (ps,u::x)    <- span1  isPlaced ns | (_,[]) => pure Nothing
      (us,p2::rem) <- break1 isPlaced x  | (_,[]) => pure Nothing
      let p1 := List.last (p::ps)
      pure $ Just (B c p1 u us p2 $ tpe p1 p2, p2, rem)

bridge : PlaceST s g => Cycles g -> F1 s (Maybe (Bridge g, Cycles g))
bridge cs = T1.do
  bs <- mapMaybe1 toBridge cs
  case sortBy (comparing type) bs of
    []    => pure Nothing
    b::bs => pure $ Just (b,map cycle bs)

--------------------------------------------------------------------------------
-- Placing Rings
--------------------------------------------------------------------------------

parameters {0 e, n  : Type}
           {auto dg : DebugFlag}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : Graph e n)
           {auto st : PlaceST s g}

  ngon : Cycle g -> F1' s
  ngon c =
    let phi := fullSteps c.ncycle.size
        r   := ngonRadius BOND_LEN c.ncycle.size @{c.ncycle.prf}
     in polygonCorners g c.nodes origin zero phi (scaleTo r vone)

  placeBridge : Cycles g -> Bridge g -> F1' s
  placeBridge placed (B c _ _ _   _ Fresh) = ngon c
  placeBridge placed (B c x f rem y Spiro) = T1.do
    -- center of placed cycle(s)
    cref <- centerOf (placed >>= \x => x.nodes)
    -- positions of the attachment nodes
    px   <- nodePosition x
    let MkArc tot phi r d := ngon BOND_LEN c.ncycle.size @{c.ncycle.prf}
        c                 := translate (scaleTo r $ px - cref) px
    polygonCorners g (f::rem) c zero phi (px - c)

  placeBridge placed (B c x f rem y tpe)   = T1.do
    -- center of placed cycle(s)
    cref <- centerOf (placed >>= \x => x.nodes)
    -- positions of the attachment nodes
    px   <- nodePosition x
    py   <- nodePosition y
    debugIf1 "Placing ring: \{show tpe}, nodes: \{c.nodes}, unplaced: \{f::rem}"
    debugIf1 "Placed center: \{cref}; px: \{px}; py: \{py}"
    let cs  := center2d (the (List _) [px,py])
        rd  := distance px py
        len := max BOND_LEN $ rd * 1.1 / cast (length rem + 2)
        MkArc tot phi r d := arc (S $ length rem) len rd
        v   := scaleTo d $ perpendicularFrom px py cref
        v2  := if tot > pi then v else negate v
        c   := translate v2 cs
        ax  := angleOrZero (c - px)
        ay  := angleOrZero (c - py)
        ns  := f::rem
        px' := translate (rotate tot $ px - c) c
        py' := translate (rotate tot $ py - c) c
    debugIf1 "xy-center: \{cs}; xy-distance: \{rd}; len: \{len}"
    debugIf1 "vectors: v: \{v}; v2: \{v2}, arc center: \{c}"
    debugIf1 "angles: ax: \{ax}, ay: \{ay}, arc: \{tot}, step: \{phi}"
    debugIf1 "Arc: radius: \{r}, dist: \{d}"
    debugIf1 "Images: px': \{px'}, py': \{py'}"
    case (ax - ay < Angle.pi) == (tot > Angle.pi) of
      True  => polygonCorners g ns c zero phi (px - c)
      False => polygonCorners g (reverse ns) c zero phi (py - c)

  layoutSystem : (placed, unplaced : Cycles g) -> F1' s
  layoutSystem ps us t =
   let Just (b,rs) # t := bridge us t | _ # t => () # t
       _           # t := placeBridge (filter (partOf b) ps) b t
    in layoutSystem (b.cycle::ps) (assert_smaller us rs) t

  placeInitialRing : Subgraph g -> F1' s
  placeInitialRing sg =
   let c::cs  := mcb $ componentCycles sg | [] => pure ()
       (r,rs) := mostComplex [<] cs (natoms c cs) (c.ncycle.size) c
    in ngon r >> layoutSystem [r] rs

  export
  placeRing : AttachPoint g -> Nodes g -> Subgraph g -> F1' s
  placeRing None         ns sg = T1.do
    placeInitialRing sg
    _ <- traverse1 (placeNeighbours g) ns
    pure ()
  placeRing (Attach p x) ns sg = T1.do
    pp <- nodePosition p
    xp <- nodePosition x
    unplace p
    placeInitialRing sg
    us <- traverse1 (placeNeighbours g) ns
    pq <- nodePosition p
    xq <- nodePosition x
    let f := alignBond pp xp pq xq
    for1_ (ns ++ join us) $ adjPoint f

module Geom.Gen2D.Rings

import Chem
import Geom.Gen2D.Place
import Geom.Gen2D.State
import Geom.Gen2D.Types
import Data.Graph.Indexed.Ring.Relevant
import Data.SortedSet
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Types and Ring Analysis
--------------------------------------------------------------------------------

0 Cycles : Nat -> Type
Cycles = List . Cycle

0 Nodes : Nat -> Type
Nodes = List . Fin

0 SnocNodes : Nat -> Type
SnocNodes = SnocList . Fin

data BridgeType = Fused | Spiro | Brdg | Fresh | Partitioned

%runElab derive "BridgeType" [Eq,Ord]

record Bridge (k : Nat) where
  constructor B
  cycle : Cycle k
  start : Fin k
  first : Fin k
  rem   : Nodes k
  end   : Fin k
  type  : BridgeType

natoms : Cycle k -> List (Cycle k) -> Nat
natoms c = sum . map (numSharedNodes c)

mostComplex :
     SnocList (Cycle k)
  -> List (Cycle k)
  -> (atms, len : Nat)
  -> Cycle k
  -> (Cycle k, List (Cycle k))
mostComplex sx []      atms len r = (r, sx <>> [])
mostComplex sx (x::xs) atms len r =
 let n := natoms x (sx <>> (r::xs))
  in case compare n atms of
       LT => mostComplex (sx:<x) xs atms len r
       GT => mostComplex (sx:<r) xs n    x.ncycle.size x
       EQ => case len >= x.ncycle.size of
         True  => mostComplex (sx:<x) xs atms len r
         False => mostComplex (sx:<r) xs n    x.ncycle.size x

partOf : Bridge k -> Cycle k -> Bool
partOf b c = contains b.start c.nodeset && contains b.end c.nodeset

-- splits a cycle into non-empty segments of placed and unplaced nodes.
toBridge : PlaceST s k => Cycle k -> F1 s (Maybe $ Bridge k)
toBridge c t =
  case break1 isPlaced c.nodes t of
    (u::us,[])  # t => Just (B c u u us u Fresh) # t -- all unplaced
    (us,p::rem) # t => case go [<] p (rem ++ us) t of
      [b]    # t => Just b # t
      (b::_) # t => Just ({type := Partitioned} b) # t
      []     # t => Nothing # t
    _           # t => Nothing # t -- all placed
  where
    go : SnocList (Bridge k) -> Fin k -> Nodes k -> F1 s (List $ Bridge k)

bridge : PlaceST s k => Cycles k -> F1 s (Maybe (Bridge k, Cycles k))
bridge []      t = Nothing # t
bridge (c::cs) t =
 let Just b # t := toBridge c t | Nothing # t => bridge cs t
     p      # t := go [<] b cs t
  in Just p # t

 where
   go : SnocList (Cycle k) -> Bridge k -> Cycles k -> F1 s (Bridge k, Cycles k)
   go sc b []      t = (b,sc<>>[]) # t
   go sc b (c::cs) t =
    let Just b2 # t := toBridge c t | Nothing # t => go sc b cs t
     in case b.type >= b2.type of
          True  => go (sc:<b.cycle) b2 cs t
          False => go (sc:<c) b cs t

--------------------------------------------------------------------------------
-- Placing Rings
--------------------------------------------------------------------------------

parameters {k : _}
           {0 e, n  : Type}
           {auto dg : DebugFlag}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)
           {auto st : PlaceST s k}

  ngon : Cycle k -> F1' s
  ngon c =
    let phi := fullSteps c.ncycle.size
        r   := ngonRadius BOND_LEN c.ncycle.size @{c.ncycle.prf}
     in polygonCorners g c.nodes origin zero phi (scaleTo r vone)

  placeBridge : Cycles k -> Bridge k -> F1' s
  placeBridge placed (B c _ _ _   _ Fresh) = ngon c
  placeBridge placed (B c x f rem y tpe)   = T1.do -- TODO: Spiro
    -- center of placed cycle(s)
    cref <- centerOf (placed >>= \x => x.nodes)
    -- positions of the attachment nodes
    px   <- nodePosition x
    py   <- nodePosition y
    let cs  := center2d (the (List _) [px,py])
        -- bond length used for ring
        rd  := distance px py
        -- distance from new ring center to center of ring bonds
        MkArc _ phi r d := arc (S $ length rem) rd BOND_LEN
        c   := translate (scaleTo d $ perpendicularFrom px py cref) cs
        ax  := angleOrZero (c - px)
        ay  := angleOrZero (c - py)
        ns  := f::rem
    case ax - ay < Angle.pi of
      True  => polygonCorners g ns c zero phi (px - c)
      False => polygonCorners g (reverse ns) c zero phi (py - c)

  layoutSystem : (placed, unplaced : Cycles k) -> F1' s
  layoutSystem ps us t =
   let Just (b,rs) # t := bridge us t | _ # t => () # t
       _           # t := placeBridge (filter (partOf b) ps) b t
    in layoutSystem (b.cycle::ps) (assert_smaller us rs) t

  placeInitialRing : Subgraph k e n -> F1' s
  placeInitialRing sg =
   let c::cs  := mcb $ componentCycles sg | [] => pure ()
       (r,rs) := mostComplex [<] cs (natoms c cs) (c.ncycle.size) c
    in ngon r >> layoutSystem [r] rs

  export
  placeRing : AttachPoint k -> List (Fin k) -> Subgraph k e n -> F1' s
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

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
    (us,[]    ) # t => Nothing # t                   -- all placed
    (us,p::rem) # t =>
     let Just (b,p2,ns2) # t := nxt p  (rem++us++[p]) t | _ # t => Nothing # t
         Just _          # t := nxt p2 ns2            t | _ # t => Just b # t
      in Just ({type := Partitioned} b) # t
  where
    tpe : Fin k -> Fin k -> BridgeType
    tpe x y =
     case mkEdge x y () of
       Just e  => if contains e c.edgeset then Fused else Brdg
       Nothing => Spiro

    nxt : Fin k -> Nodes k -> F1 s (Maybe (Bridge k, Fin k, Nodes k))
    nxt p ns = T1.do
      -- first, take placed prefix, then take until placed again
      (ps,u::x)    <- span1  isPlaced ns | (_,[]) => pure Nothing
      (us,p2::rem) <- break1 isPlaced x  | (_,[]) => pure Nothing
      let p1 := List.last (p::ps)
      pure $ Just (B c p1 u us p2 $ tpe p1 p2, p2, rem)

bridge : PlaceST s k => Cycles k -> F1 s (Maybe (Bridge k, Cycles k))
bridge cs = T1.do
  bs <- mapMaybe1 toBridge cs
  case sortBy (comparing type) bs of
    []    => pure Nothing
    b::bs => pure $ Just (b,map cycle bs)

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
        len := max BOND_LEN $ rd * 1.1 / cast (length rem + 2)
        -- distance from new ring center to center of ring bonds
        MkArc tot phi r d := arc (S $ length rem) len rd
        v   := scaleTo d $ perpendicularFrom px py cref
        v2  := if tot > pi then v else negate v
        c   := translate v2 cs
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

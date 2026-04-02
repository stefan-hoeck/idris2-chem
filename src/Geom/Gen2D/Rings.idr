module Geom.Gen2D.Rings

import Data.Queue
import Chem
import Geom.Gen2D.Place
import Geom.Gen2D.State
import Geom.Gen2D.Types
import Data.Graph.Indexed.Ring.Relevant
import Data.SortedSet

%default total

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

0 Cycles : Nat -> Type
Cycles = List . Cycle

0 CQueue : Nat -> Type
CQueue = Queue . Cycle

0 CPair : Nat -> Type
CPair k = (CQueue k, Cycles k)

fusedToBePlaced : Cycle k -> List (Fin k) -> Maybe (List (Fin k), Fin k, Fin k)
fusedToBePlaced c xs =
 let (ys,z::zs) := break isPlaced (zip (drop 1 xs) xs) | _ => Nothing
  in Just (map snd . drop 1 $ zs ++ ys, z)
  where
    isPlaced : (Fin k, Fin k) -> Bool
    isPlaced (x,y) = contains x c.nodeset && contains y c.nodeset

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

  fuseTo : Cycle k -> Cycle k -> F1' s
  fuseTo placed new = T1.do
    let Just (ns,x,y) := fusedToBePlaced placed new.ncycle.path | _ => pure ()
    -- center of placed cycle
    cref <- centerOf placed.nodes
    -- positions of the two fused nodes
    px   <- nodePosition x
    py   <- nodePosition y
    let cs  := center2d (the (List _) [px,py])
        -- bond length used for ring
        rd  := distance px py
        -- distance from new ring center to center of ring bonds
        d   := ngonDistance rd new.ncycle.size @{new.ncycle.prf}
        phi := fullSteps new.ncycle.size
        c   := translate (scaleTo d $ perpendicularFrom px py cref) cs
        ax  := angleOrZero (c - px)
        ay  := angleOrZero (c - py)
    case ax - ay < Angle.pi of
      True  => polygonCorners g ns c zero phi (px - c)
      False => polygonCorners g (reverse ns) c zero phi (py - c)

  spiroTo : Cycle k -> Cycle k -> F1' s
  spiroTo _ _ = pure ()

  layoutSystem : CQueue k -> Cycles k -> F1' s
  layoutSystem q xs t =
    case dequeue q of
      Nothing     => () # t
      Just (c,q2) =>
       let (fs,nfs) := partition (isFusedTo c) xs
           (ss,nss) := partition (isSpiro c) nfs
           _ # t    := traverse1_ (fuseTo c) fs t
           _ # t    := traverse1_ (spiroTo c) ss t
           q3       := enqueueAll q2 (fs++ss)
        in layoutSystem (assert_smaller q q3) nss t

  placeInitialRing : Subgraph k e n -> F1' s
  placeInitialRing sg = T1.do
   let c::cs  := mcb $ componentCycles sg | [] => pure ()
       (r,rs) := mostComplex [<] cs (natoms c cs) (c.ncycle.size) c
   ngon r
   layoutSystem (Queue.fromList [r]) rs

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

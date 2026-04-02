module Geom.Gen2D.Place

import Chem
import Geom.Gen2D.State

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

classMap : {k : _} -> List (Fin k, Nat) -> IArray k Nat
classMap ps =
  case sortBy (comparing snd) ps of
    []        => fill k 1
    (x,n)::ps => alloc k Z $ \m => set m x 1 >> go 1 n ps m
  where
    go : Nat -> Nat -> List (Fin k, Nat) -> MArray s k Nat -> F1 s (IArray k Nat)
    go c p []            m t = unsafeFreeze m t
    go c p ((x,n) :: xs) m t =
     let c'    := if n == p then c else S c
         _ # t := set m x c' t
      in go c' n xs m t

export
prioritize : {k : _} -> IGraph k e n -> IArray k Nat
prioritize g = go (fill k 1) k
  where
    %inline
    compRank : IArray k Nat -> Fin k -> Nat
    compRank prev x = 3 * at prev x + sum (at prev <$> neighbours g x)

    go : IArray k Nat -> Nat -> IArray k Nat
    go prev 0     = prev
    go prev (S n) =
     let rank := Indexed.generate k (compRank prev)
         cmap := classMap $ foldrKV (\x,v,xs => (x,v)::xs) [] rank
      in if prev == cmap then prev else go cmap n


parameters {k       : Nat}
           {auto dg : DebugFlag}
           {0 e, n  : Type}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)

  isTerminalD4 : Fin k -> Bool
  isTerminalD4 x =
   let ns := neighbours g x
    in length ns == 4 && count ((> 1) . deg g) ns <= 1

  nextBondVector : Fin k -> MolVector -> (p,c : MolPoint) -> Bool -> MolVector
  nextBondVector x v p c trans =
    case cast @{ch} (lab g x) of
      SP => v
      _  =>
       let a  := compAngle
           va := rotate a (negate v)
           vb := rotate (negate a) (negate v)
        in if distance (translate va p) c >= distance (translate vb p) c
              then va
              else vb

    where
      compAngle : Angle
      compAngle =
        if      isTerminalD4 x then fromDegree 45
        else if isMetal (cast $ lab g x) then fullSteps (deg g x)
        else if trans then fromDegree 120 else fromDegree 60

  ||| Places the atoms in a linear chain.
  |||
  ||| Expects the first atom to be placed and
  ||| places the next atom according to initialBondVector. The rest of the chain
  ||| is placed such that it is as linear as possible (in the overall result, the
  ||| angles in the chain are set to 120 Deg.)
  ||| TODO: Double bond configuration
  export
  placeChain : PlaceST s k => Fin k -> List (Fin k) -> MolVector -> F1' s
  placeChain _ []      _ t = () # t
  placeChain p (n::ns) v t =
   let pp # t := nodePosition p t
       pn     := translate v pp
       b  # t := isPlaced n t
       _  # t := when1 (not b) (place n pn) t
       c  # t := State.center {k} t
    in placeChain n ns (nextBondVector n v pn c True) t

  export
  polygonCorners :
       {auto st : PlaceST s k}
    -> List (Fin k)
    -> MolPoint
    -> (cur,step : Angle)
    -> (dir : MolVector)
    -> F1' s
  polygonCorners []        _ _   _    _   t = () # t
  polygonCorners (x :: xs) p cur step dir t =
   let theta := cur + step
       p2    := translate (rotate theta dir) p
       _ # t := debugIf1 "placing \{show x} at \{show p2}" t
       _ # t := place x p2 t
    in polygonCorners xs p theta step dir t

  export
  distributeAtoms : PlaceST s k => Fin k -> (us,ps : List (Fin k)) -> F1' s
  distributeAtoms x []        _   t = () # t
  distributeAtoms x [u]       [p] t =
   let px # t := nodePosition x t
       pp # t := nodePosition p t
       c  # t := State.center {k} t
    in placeChain x [u] (nextBondVector x (px - pp) px c True) t
  distributeAtoms x us@(_::r) ps  t =
   let px # t       := nodePosition x t
       ps # t       := traverse1 nodePosition ps t
       (start,step) := circularFreeSweep (S $ length r) px ps
    in polygonCorners us px start step (V BOND_LEN 0) t

  export
  placeNeighbours : PlaceST s k => Fin k -> F1 s (List $ Fin k)
  placeNeighbours x t =
   let (us,ps) # t := partition1 isPlaced (neighbours g x) t
       _       # t := debugIf1 "placing neighbours for \{show x}" t
       _       # t := distributeAtoms x us ps t
    in us # t

  ||| Convenience method to place a single atom. This function will first find
  ||| a placed neighbour does not need to be set) and then place this
  ||| new atoms considering the neighbour's neighbours. Essentially this
  ||| utility is useful for sprouting a new atom to an already placed
  ||| structure.
  export
  placeAtom : PlaceST s k => Fin k -> F1' s
  placeAtom x t =
   let False # t := isPlaced x t | _ # t => () # t
    in case filter1 isPlaced (neighbours g x) t of
         []  # t => place x (P 0 0) t
         [y] # t =>
          let ps # t := filter1 isPlaced (neighbours g y) t
           in distributeAtoms y [x] ps t
         ys  # t => let c # t := centerOf ys t in place x c t

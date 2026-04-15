module Geom.Gen2D.State

import Data.Array.Mutable
import public Data.Graph.Indexed
import public Data.Linear.List
import public Data.Linear.Ref1
import public Data.Linear.Traverse1
import public Data.Refined
import public Geom
import public Syntax.T1

%default total

export
BOND_LEN : Double
BOND_LEN = 1.25

||| Internal state for iteratively placing (parts of) the atoms
||| in a molecule.
|||
||| It keeps track of the atoms that have been placed so far
||| but also of the current center of the placed atoms.
export
record PlaceST (s : Type) (k : Nat) where
  [noHints]
  constructor PST
  pos    : MArray s k (Maybe $ Point Mol)
  psum   : Ref s MolPoint
  placed : Ref s Nat

||| Creates a new state for coordinate generation with all
||| coordinates being currently unset and the current center
||| at the origin.
export
placeST : (k : Nat) -> F1 s (PlaceST s k)
placeST k = T1.do
  m <- marray1 k Nothing
  s <- ref1 (P 0 0)
  p <- ref1 Z
  pure (PST m s p)

||| Sets the coordinate of the given node.
|||
||| This can also be used to re-place a node that was already
||| placed. The center of all placed nodes is updated accordingly.
export
place : PlaceST s k => Fin k -> Point Mol -> F1' s
place @{st} x p =
  Core.get st.pos x >>= \case
    Just q  => T1.do
      set st.pos x (Just p)
      mod1 st.psum $ \(P x y) => P (x + p.x - q.x) (y + p.y - q.y)
    Nothing => T1.do
      set st.pos x (Just p)
      mod1 st.placed S
      mod1 st.psum $ \(P x y) => P (x + p.x) (y + p.y)

||| Marks the given node as unplaced by removing its
||| entry from the array of coordinates and adjusting the
||| center of placed nodes accordingly.
|||
||| In case the node is already unset, this is a no-op.
export
unplace : PlaceST s k => Fin k -> F1' s
unplace @{st} x =
  Core.get st.pos x >>= \case
    Nothing => pure ()
    Just p  => T1.do
      set st.pos x Nothing
      mod1 st.placed pred
      mod1 st.psum $ \(P x y) => P (x - p.x) (y - p.y)

||| Returns the current coordinate of the given node.
|||
||| Returns the origin in case the node is currently unplaced.
export
nodePosition : PlaceST s k => Fin k -> F1 s MolPoint
nodePosition @{st} x t =
  case Core.get st.pos x t of
    Just p  # t => p # t
    Nothing # t => origin # t

||| Returns the vector connecting the two nodes by subtracit
||| the position of `x` from the one of `y`.
export
bondVector : PlaceST s k => (x,y : Fin k) -> F1 s MolVector
bondVector x y = T1.do
  px <- nodePosition x
  py <- nodePosition y
  pure $ py - px

||| True, if the given node is currently placed.
export
isPlaced : PlaceST s k => Fin k -> F1 s Bool
isPlaced @{st} x t =
  case Core.get st.pos x t of
    Just p  # t => True # t
    Nothing # t => False # t

||| Returns the center of the currently placed nodes.
export
center : PlaceST s k => F1 s MolPoint
center @{st} t =
  case read1 st.placed t of
    0 # t => P 0 0 # t
    n # t =>
     let P x y # t := read1 st.psum t
         d         := cast {to = Double} n
      in P (x/d) (y/d) # t

||| Computes the center of the given nodes.
|||
||| This uses `nodePosition` internally, therefore, if one of the
||| has not yet been placed, it will be placed at the origin.
export
centerOf : PlaceST s k => List (Fin k) -> F1 s MolPoint
centerOf vs = center2d <$> traverse1 nodePosition vs

||| Returns the current node positions in an immutable array.
|||
||| Unplaced nodes will be put at the origin.
export
getPoints : {k : _} -> PlaceST s k -> F1 s (IArray k $ Point Mol)
getPoints st t =
  let m # t := mmap (fromMaybe origin) st.pos t
   in unsafeFreeze m t

||| Adjusts the position of the given node by applying the
||| given function.
export
adjPoint : PlaceST s k => (Point Mol -> Point Mol) -> Fin k -> F1' s
adjPoint @{st} f i = nodePosition i >>= place i . f

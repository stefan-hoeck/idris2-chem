module Geom.Gen2D.State

import Data.Array.Mutable
import public Data.Graph.Indexed
import public Data.Linear.List
import public Data.Linear.Ref1
import public Data.Linear.Traverse1
import public Data.Refined
import public Geom
import public Syntax.T1

%hide Prelude.(-)
%default total

||| Internal state for iteratively placing (parts of) the atoms
||| in a molecule.
|||
||| It keeps track of the atoms that have been placed so far
||| but also of the current center of the placed atoms.
export
record PlaceST (s : Type) (k : Nat) where
  [noHints]
  constructor PST
  pos    : MArray s k (Maybe $ Point Id)
  psum   : Ref s (Point Id)
  placed : Ref s Nat

export
placeST : (k : Nat) -> F1 s (PlaceST s k)
placeST k = T1.do
  m <- marray1 k Nothing
  s <- ref1 (P 0 0)
  p <- ref1 Z
  pure (PST m s p)

export
place : PlaceST s k => Fin k -> Point Id -> F1' s
place @{st} x p = T1.do
  set st.pos x (Just p)
  mod1 st.placed S
  mod1 st.psum $ \(P x y) => P (x + p.x) (y + p.y)

export
nodePosition : PlaceST s k => Fin k -> F1 s (Point Id)
nodePosition @{st} x t =
  case Core.get st.pos x t of
    Just p  # t => p # t
    Nothing # t => origin # t

export
bondVector : PlaceST s k => Fin k -> Fin k -> F1 s (Vector Id)
bondVector x y = T1.do
  px <- nodePosition x
  py <- nodePosition y
  pure $ py - px

export
isPlaced : PlaceST s k => Fin k -> F1 s Bool
isPlaced @{st} x t =
  case Core.get st.pos x t of
    Just p  # t => True # t
    Nothing # t => False # t

export
center : PlaceST s k => F1 s (Point Id)
center @{st} t =
  case read1 st.placed t of
    0 # t => P 0 0 # t
    n # t =>
     let P x y # t := read1 st.psum t
         d         := cast {to = Double} n
      in P (x/d) (y/d) # t

export
centerOf : PlaceST s k => List (Fin k) -> F1 s (Point Id)
centerOf vs = center2d <$> traverse1 nodePosition vs

export
getPoints : {k : _} -> PlaceST s k -> F1 s (IArray k $ Point Id)
getPoints st t =
  let m # t := mmap (fromMaybe origin) st.pos t
   in unsafeFreeze m t

module Geom.Gen2D.State

import Data.Graph.Indexed
import Data.Linear.List
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.Refined
import Geom
import Syntax.T1

%hide Prelude.(-)
%default total

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
place : PlaceST s k => Fin k -> Point Id -> F1 s Bool
place @{st} x p = T1.do
  set st.pos x (Just p)
  mod1 st.placed S
  mod1 st.psum $ \(P x y) => P (x + p.x) (y + p.y)
  pure True

export
nodePosition : PlaceST s k => Fin k -> F1 s (Point Id)
nodePosition @{st} x t =
  case Core.get st.pos x t of
    Just p  # t => p # t
    Nothing # t => origin # t

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

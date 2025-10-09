module Geom.Gen2D.Types

import Chem
import Data.SortedMap
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--      Settings
--------------------------------------------------------------------------------

||| Checks if a number is in the range [0,1[
public export
ValidSensitivity : Double -> Bool
ValidSensitivity x = 0.0 <= x && x < 1.0

||| Overlap sensitivity for limiting optimization iterations
public export
record Sensitivity where
  constructor OSS
  value : Double
  {auto 0 prf : Holds ValidSensitivity value}

%runElab derive "Sensitivity" [Show,Eq]

export
Cast Sensitivity Double where
  cast oss = oss.value

||| General options for drawing and placing smiles molecules
public export
record SmilesDrawSettings where
  constructor SDS
  bondLength       : Double
  sensivity        : Sensitivity
  maxResolveCycles : Nat

%runElab derive "SmilesDrawSettings" [Show,Eq]


--------------------------------------------------------------------------------
--      Overlapping score
--------------------------------------------------------------------------------

||| Record for the overlapping score
public export
record OScore k where
  constructor OS
  ||| Overlapping score for the whole drawn molecule
  tot     : Double

  ||| Map of atoms with an overlapping score
  -- TODO: Should this be an `IArray`?
  scoreA  : SortedMap (Fin k) Double

  ||| List of overlapping scores between two atoms
  scoreAA : List (Fin k, Fin k, Double)

%runElab deriveIndexed "OScore" [Show,Eq]

--------------------------------------------------------------------------------
--      Tree structure
--------------------------------------------------------------------------------

||| This is either a node with its direct children or a list
||| of nodes belonging to a ring system plus their children.
|||
||| Every node in a graph appears at most once in this structure
|||
||| The connected components of a graph build a list of `RTree`s.
public export
data RTree : Nat -> Type -> Type where
  Node : Fin k -> a -> List (RTree k a) -> RTree k a
  Ring : List (Fin k, a, List $ RTree k a) -> RTree k a

%runElab derivePattern "RTree" [I,P] [Show,Eq]

public export
0 Trees : Nat -> Type -> Type
Trees n a = List (RTree n a)

public export
0 SnocTrees : Nat -> Type -> Type
SnocTrees n a = SnocList (RTree n a)

public export
0 Rings : Nat -> Type -> Type
Rings n a = List (Fin n, a, Trees n a)

public export
0 SnocRings : Nat -> Type -> Type
SnocRings n a = SnocList (Fin n, a, Trees n a)

||| Calculates the size of a RTree structure, resp. sum of all nodes.
export
size : RTree k l -> Nat
size (Node _ _ xs) = assert_total $ S (sum $ map size xs)
size (Ring xs)     = assert_total $ sum $ map (sum . map size . snd . snd) xs

||| Extracts the depth of a RTree structure, which has the depth label.
export
depth : RTree k (Nat,a) -> Nat
depth (Node _ (n,_) _)           = n
depth (Ring [])                  = 0
depth (Ring ((_,(n,_),_) :: xs)) = n

goRT : RTree k a -> (Nat,RTree k (Nat,a))

goT : SnocTrees k (Nat,a) -> Trees k a -> Nat -> (Nat,Trees k (Nat,a))
goT sx []      n = (n,sx <>> [])
goT sx (x::xs) n = let (m,y) := goRT x in goT (sx:<y) xs (max m n)

goR : SnocRings k (Nat,a) -> (p,q,d : Nat) -> Rings k a -> (Nat,Rings k (Nat,a))
goR sx p q d []               = (d,sx <>> [])
goR sx p q d ((k,l,ys) :: xs) =
 let (d2,zs) := goT [<] ys 0
  in goR (sx:<(k,(S d2,l),zs)) (S p) (pred q) (max d $ S d2 + min p q) xs

goRT (Node x l xs) = let (m,ys) := goT [<] xs 0 in (S m,Node x (S m,l) ys)
goRT (Ring xs)     = let (m,ys) := goR [<] 0 (length xs) 0 xs in (m,Ring ys)

export %inline
addDepth : RTree k a -> RTree k (Nat,a)
addDepth = snd . goRT

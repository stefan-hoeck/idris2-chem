module Chem.Util

%default total

||| Extracts the minimal value from a list (if any) according to the
||| given comparison function.
export
minBy : Ord b => (a -> b) -> List a -> Maybe a
minBy _ []     = Nothing
minBy f (h::t) = Just $ go h (f h) t
  where
    go : a -> b -> List a -> a
    go va _  []        = va
    go va vb (x :: xs) =
      let vb2 := f x
       in if vb <= vb2 then go va vb xs else go x vb2 xs

||| Modify those values in a functor that fulfill the given predicate
export %inline
mapIf : Functor f => (a -> Bool) -> (a -> a) -> f a -> f a
mapIf p f = map $ \v => if p v then f v else v

||| Keep and modify those values in a list that fulfill the given predicate
export %inline
mapFilter : (a -> Bool) -> (a -> b) -> List a -> List b
mapFilter p f = mapMaybe (\v => if p v then Just (f v) else Nothing)

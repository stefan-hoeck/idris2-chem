module Text.RW

import Data.Validated

public export
record Read (a : Type) where
  constructor MkRead
  re  : String -> Maybe a
  reE : String -> Either String a

public export
mkRead : (String -> Maybe a) -> String -> Read a
mkRead r n = 
  MkRead r $ \s => maybe (Left $ #"Not a valid \#{n}: \#{s}"#) Right (r s)

public export
mkReadE : (String -> Either String a) -> Read a
mkReadE r = MkRead (\s => either (const Nothing) Just (r s)) r

public export %inline
read : (r : Read a) => String -> Maybe a
read = r.re

public export %inline
readE : (r : Read a) => String -> Either String a
readE = r.reE

public export
record Write (a : Type) where
  constructor MkWrite
  wr : a -> String

public export %inline
write : (w : Write a) => a -> String
write = w.wr

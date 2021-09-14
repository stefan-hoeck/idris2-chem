module Text.RW

public export %inline
mkReadE : (String -> Maybe a) -> String -> String -> Either String a
mkReadE r n = \s => maybe (Left $ #"Not a valid \#{n}: \#{s}"#) Right (r s)

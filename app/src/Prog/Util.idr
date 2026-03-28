module Prog.Util

import public Chem
import public Data.String
import public IO.Async.Loop.Epoll
import public IO.Async.Loop.Posix
import public IO.Async.Posix
import public Text.ILex
import public Text.Smiles

%default total

public export
0 Errs : List Type
Errs = [SmilesParseErr]

public export
0 Prog : Type -> Type
Prog = Async Poll Errs

herr : Interpolation e => e -> Async Poll [] Bool
herr x = stdoutLn "\{x}" $> False

export
herrs : Prog Bool -> Async Poll [] Bool
herrs = handle [herr]

export
quit : Prog Bool
quit = stdoutLn "Goodbye." $> True

export
invalid : Prog ()
invalid = stdoutLn "invalid command"

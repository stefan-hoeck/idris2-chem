module Main

import Prog.Cycles
import Prog.Pretty
import Prog.Util
import IO.Async.Posix

%hide Data.Linear.(.)
%hide Data.Linear.(<$>)
%default total

act : List String -> Prog Bool
act ["q"]         = quit
act ["quit"]      = quit
act ["done"]      = quit
act ("pretty"::s) = prettySmiles s $> False
act ("cycles"::s) = cycles s $> False
act _             = invalid $> False

covering
loop : Async Poll [Errno] ()
loop = Prelude.do
  stdout "Input: "
  args  <- (map trim . words) <$> readnb Stdin String 0xfff
  False <- weakenErrors $ herrs (act args) | True => pure ()
  loop

covering
main : IO ()
main = epollApp (handle [stderrLn . interpolate] loop)

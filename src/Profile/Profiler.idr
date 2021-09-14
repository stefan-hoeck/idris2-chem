module Profile.Profiler

import Data.Nat
import System.Clock

public export
record Task where
  constructor MkTask
  name  : String
  task  : () -> Bool
  runs  : Nat
  0 prf : IsSucc runs

public export
record Result where
  constructor MkResult
  startTime : Clock UTC
  stopTime  : Clock UTC
  success   : Bool
  task      : Task

runner : Nat -> (run : () -> Bool) -> (result : Bool) -> Bool
runner 0     _   res = res
runner (S k) run res = runner k run (run () && res)

export
profile : Task -> IO Result
profile t = do
  start <- clockTime UTC
  res   <- pure $ runner t.runs t.task True
  stop  <- clockTime UTC
  pure $ MkResult start stop res t

scale : Integer
scale = 1000000000

average : Clock Duration -> (n : Nat) -> (0 prf : IsSucc n) -> Clock Duration
average (MkClock s ns) n _ =
  let tot = s * scale + ns
      avg = tot `div` cast n
   in MkClock (avg `div` scale) (avg `mod` scale)

export
report : Result -> String
report r =
  let succ = if r.success then "Success" else "Failed"
      dur  = timeDifference r.stopTime r.startTime
      avg  = average dur r.task.runs r.task.prf
   in #"""
      \#{r.task.name}: \#{show r.task.runs} runs.
        Result:     \#{succ}
        Start Time: \#{show r.startTime}
        End Time:   \#{show r.stopTime}
        Duration:   \#{show dur}
        Per run:    \#{show avg}
      """#

export
profileAndReport : Task -> IO ()
profileAndReport t = do
  putStrLn ""
  res <- profile t
  putStrLn $ report res
  putStrLn ""

module Profile.Profiler

import Data.Nat
import Data.String
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

prettyDuration : Clock Duration -> String
prettyDuration (MkClock s ns) =
  let nano   = ns `mod` 1000
      micro  = (ns `mod` 1000000) `div` 1000
      milli  = ns `div` 1000000
   in #"\#{show s} s \#{show milli} ms \#{show micro} us \#{show nano} ns"#

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
        Duration:   \#{prettyDuration dur}
        Per run:    \#{prettyDuration avg}
      """#

export
profileAndReport : Task -> IO ()
profileAndReport t = do
  putStrLn ""
  res <- profile t
  putStrLn $ report res
  putStrLn ""


-- Profiler for return value handling -----------------------------------------
public export
record ProfileTask a where
  constructor MkProfileTask
  name : String
  desc : String
  task : a -> a
  dres : a
  runs : Nat
  0 prf : IsSucc runs

record ProfileResult a where
  constructor MkProfileResult
  startTime : Clock UTC
  stopTime  : Clock UTC
  task      : ProfileTask a
  result    : a

runnerRes : Nat -> (run : a -> a) -> a -> a
runnerRes 0     _ res = res
runnerRes (S k) f res = runnerRes k f (f res)

measure : ProfileTask a -> IO (ProfileResult a)
measure t = do
  start <- clockTime UTC
  res   <- pure $ runnerRes t.runs t.task t.dres
  stop  <- clockTime UTC
  pure $ MkProfileResult start stop t res

-- Don't like clockTime, so here's that
showDuration : Clock Duration -> String
showDuration (MkClock s ns) =
  let nano    = padLeft 9 '0' $ show ns
      seconds = show s
  in #"\#{seconds}.\#{nano} s"#

-- Report & show result
reportResult : Show a => ProfileResult a -> String
reportResult (MkProfileResult start stop t res) =
  let dur = timeDifference stop start
      avg = average dur t.runs t.prf
  in #"""
     \#{t.name}: \#{show t.runs} runs.
       Description: \#{show t.desc}
       Result:      \#{show res}
       Start Time:  \#{show start}
       End Time:    \#{show stop}
       Duration:    \#{prettyDuration dur}
       Per run:     \#{prettyDuration avg}
     """#

resultRow : Show a => ProfileResult a -> String
resultRow (MkProfileResult start stop t res) =
  let dur = timeDifference stop start
      avg = average dur t.runs t.prf
  in #"\#{t.name};\#{t.desc};\#{show t.runs};\#{showDuration dur};\#{showDuration avg};\#{show res}"#

export
profileAndReportRes : Show a => ProfileTask a -> IO String
profileAndReportRes t = do
  putStrLn ""
  res <- measure t
  putStrLn $ reportResult res
  putStrLn ""
  pure $ resultRow res

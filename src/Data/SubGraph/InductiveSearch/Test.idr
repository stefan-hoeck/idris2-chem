module Data.SubGraph.InductiveSearch.Test


import Data.SubGraph.InductiveSearch
import Data.Graph
import Text.Smiles

import Data.Prim.Bits64
import System
import Data.Maybe
import Data.Vect

%default total

-- Utility --------------------------------------------------------------------

data Success = Worked

data InductiveTestError = ParseError String
                        | TestFailure String

Show InductiveTestError where
  show (ParseError s)  = "Failed to parse SMILES: " ++ s
  show (TestFailure s) = "Function " ++ s ++ " failed to run properly"


getGraph : String -> Either InductiveTestError (Graph Bond Atom)
getGraph s = ext $ parse s
    where ext : Result -> Either InductiveTestError (Graph Bond Atom)
          ext (End x)     = Right x
          ext (Stuck _ _) = Left (ParseError s)


-- Matcher
eqE : Bond -> Bond -> Bool
eqE = (==)
eqV : Atom -> Atom -> Bool
eqV = (==)
matchers : Matchers Bond Atom Bond Atom
matchers = MkMatchers eqE eqV

-- Example types --------------------------------------------------------------

neV : Vect 2 Node
neV = [1,3]

nc1 : NodeClass Atom
nc1 = MkNodeCls (SubsetAtom C) 2 2 -- (length neV) neV

ncs1 : List (NodeClass Atom)
ncs1 = [ MkNodeCls (SubsetAtom C) 2 1 -- (length neV) neV
       , MkNodeCls (SubsetAtom C) 2 3 -- (length neV) neV

       ]


-- Individual Tests -----------------------------------------------------------

mET : Either InductiveTestError Success
mET = if isNothing (mkElTrg 1 []) && isJust (mkElTrg 1 [1,2,4])
      then Right Worked
      else Left (TestFailure "mkElTrg")

---

ncs : Either InductiveTestError Success
ncs = do g  <- getGraph "CCCO"
         ge <- getGraph ""
         if length (nodeClasses $ contexts g) == 3 && length (nodeClasses $ contexts ge) == 0
            then Right Worked else Left (TestFailure "nodeClasses")

----

bestC : Either InductiveTestError Success

newQN : Either InductiveTestError Success
newQN = do
        q <- getGraph ""
        t <- getGraph ""
        if True then Right Worked else Left (TestFailure "newQryNode")
        -- newQryNode matchers

-- Test execution -------------------------------------------------------------
test : Either InductiveTestError Success -> IO ()
test (Left e) = putStrLn (show e) >> exitFailure
test _        = pure ()


export
testInductiveFunctions : IO ()
testInductiveFunctions = do
  _ <- putStrLn "Inductive Search subfunction tests"
  _ <- test mET
  _ <- test ncs
  putStrLn "All Tests successful"

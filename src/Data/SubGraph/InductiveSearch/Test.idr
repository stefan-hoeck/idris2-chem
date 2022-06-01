module Data.SubGraph.InductiveSearch.Test

-- TODO: This file is not necessary for the test of the InductiveSearch
--       file. It is designed to be used to test the behavior of individual
--       functions of this process to narrow down the erroneous function.

import Data.SubGraph.InductiveSearch
import Data.Graph
import Text.Smiles

import Data.Prim.Bits64
import System
import Data.Maybe
import Data.Either
import Data.Vect

%default total

-- Utility --------------------------------------------------------------------

data Success = Worked

data InductiveTestError = ParseError String
                        | VertexExtError String
                        | TestFailure String

Show InductiveTestError where
  show (ParseError s)     = "Failed to parse SMILES: " ++ s
  show (VertexExtError s) = "Failed to apply withVertexLabels for: " ++ s
  show (TestFailure s)    = "Function " ++ s ++ " failed to run properly"


getGraph : String -> Either InductiveTestError (Graph Bond Atom)
getGraph s = ext $ parse s
    where ext : Result -> Either InductiveTestError (Graph Bond Atom)
          ext (End x)     = Right x
          ext (Stuck _ _) = Left (ParseError s)

getGraphVL : String -> Either InductiveTestError (Graph (Bond,Atom) Atom)
getGraphVL s = let Right g := getGraph s | Left e => Left e
               in maybeToEither (VertexExtError s) $ withVertexLabels g

-- Matcher
eqE : Bond -> Bond -> Bool
eqE = (==)
eqV : Atom -> Atom -> Bool
eqV = (==)
matchers : Matchers Bond Atom Bond Atom
matchers = MkMatchers eqE eqV

-- Example types --------------------------------------------------------------

nc1 : NodeClass Atom
nc1 = MkNodeCls (SubsetAtom C) 2 2

ncs1 : List (NodeClass Atom)
ncs1 = [ MkNodeCls (SubsetAtom C) 2 1
       , MkNodeCls (SubsetAtom C) 2 3
       ]


-- Individual Tests -----------------------------------------------------------

ncs : Either InductiveTestError Success
ncs = do g  <- getGraph "CCCO"
         ge <- getGraph ""
         if length (nodeClasses $ contexts g) == 3 && length (nodeClasses $ contexts ge) == 0
            then Right Worked else Left (TestFailure "nodeClasses")

----

newQN : Either InductiveTestError Success
newQN = let Right qcsE := map contexts $ getGraphVL "" | Left e => Left e
            Right tcsE := map contexts $ getGraphVL "" | Left e => Left e
            Right qcs  := map contexts $ getGraphVL "CCO"      | Left e => Left e
            Right qcsI := map contexts $ getGraphVL "CCl"      | Left e => Left e
            Right tcs  := map contexts $ getGraphVL "CC(=O)CS" | Left e => Left e
        in if    isNothing (newQryNode matchers (nodeClasses tcs) qcsE tcs)
              && isNothing (newQryNode matchers (nodeClasses tcsE) qcs tcsE)
              && isNothing (newQryNode matchers (nodeClasses tcs) qcsI tcs)
              && isJust (newQryNode matchers (nodeClasses tcs) qcs tcs)
           then Right Worked else Left (TestFailure "newQryNode")

-- Test execution -------------------------------------------------------------
test : Either InductiveTestError Success -> IO ()
test (Left e) = putStrLn (show e) >> exitFailure
test _        = pure ()


export
testInductiveFunctions : IO ()
testInductiveFunctions = do
  _ <- putStrLn "Inductive Search subfunction tests"
  _ <- test ncs
  _ <- test newQN
  putStrLn "All Tests successful\n"

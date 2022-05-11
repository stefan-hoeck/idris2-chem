module Test.Data.SubGraph

import Data.List
import Data.Vect
import System

import Text.Smiles
import Data.SubGraph.Ullmann
import Data.SubGraph.InductiveSearch

%default total

-- Types ----------------------------------------------------------------------
data IsoTestError = ParseErr String
                  | IsomorphismErr Nat -- Nat is the test example

Show IsoTestError where
   show (IsomorphismErr i) = "Incorrect matching result obtained from substructure search for unit test Nr. " ++ show i
   show (ParseErr s)       = "Failed to parse SMILES string: " ++ s

-- Hit = (SubGraph-) Isomorphism
-- NoMatch = No isomorphism
data Outcome = Hit | NoMatch

-- Type alias
Query  : Type
Query  = String
Target : Type
Target = String

BondMatcher : Type
BondMatcher = Bond -> Bond -> Bool
AtomMatcher : Type
AtomMatcher = Atom -> Atom -> Bool

MatchElement : Type
MatchElement = (Query, Target, AtomMatcher, BondMatcher, Outcome)
MatchList    : Type
MatchList    = List MatchElement


-- Test examples --------------------------------------------------------------
matchList : MatchList
matchList =
  [
    (""         ,"C"                   ,(==),(==),Hit)
  , ("CCCO"     ,"CCO"                 ,(==),(==),NoMatch) 
  , ("CC(=O)O"  ,"CC(=O)OCC[N+](C)(C)C",(==),(==),Hit)  -- Acetylcholine
  , ("CN(C)C"   ,"CC1CC(CCN1)N(C)C"    ,(==),(==),Hit)  -- Dimethyl-(2-methyl-piperidin-4-yl)-amine
  , ("C1CCCCC1" ,"CC1CCCCC1O"          ,(==),(==),Hit)  -- 2-Methylcyclohexanol
  , ("C1CC1"    ,"CC(C)C(C)CC"         ,(==),(==),NoMatch)
  , ("c1ccccc1" ,"CC1CCCCC1O"          ,(==),(==),NoMatch)  -- 2-Methylcyclohexanol
  , ("C1=CC=CC=C1" ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),Hit)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  , ("C[Si]"       ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),Hit)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  ]


-- Helper functions -----------------------------------------------------------

parseToEither : String -> Either IsoTestError (Graph Bond Atom)
parseToEither s = case parse s of
  End x => Right x
  _     => Left $ ParseErr s


checkResult : Outcome -> Nat -> Maybe a -> Either IsoTestError String
checkResult Hit     i Nothing  = Left (IsomorphismErr i)
checkResult NoMatch i (Just _) = Left (IsomorphismErr i)
checkResult _       i _        = Right $ "  Ex. Nr." ++ show i ++ ": Ok"


testAlgo : ((Nat, MatchElement) -> Either IsoTestError String)
        -> MatchList
        -> String
        -> IO ()
testAlgo f x msg =
  let n = length matchList
  in do _ <- putStrLn msg
        out $ traverse f $ zip [1..n] x
 where
   out : Either IsoTestError (List String) -> IO ()
   out (Left s)  = putStrLn (show s) >> exitFailure
   out (Right l) = putStrLn $ foldl (\a,s => a ++ s ++ "\n") "" l



-- Settings -----------------------------------------------------------
-- ullmann
makeTask :   BondMatcher
          -> AtomMatcher
          -> (g : Graph Bond Atom)
          -> Graph Bond Atom
          -> Task (length (contexts g)) Bond Atom Bond Atom
makeTask pe pv q t = MkTask pe pv (fromList $ contexts q) t


-- Algorithm test functions ---------------------------------------------------

testUllmann : (Nat, MatchElement)
           -> Either IsoTestError String
testUllmann (i, (sq,st,pv,pe,o)) = do
  q <- parseToEither sq
  t <- parseToEither st
  checkResult o i $ ullmann $ makeTask pe pv q t

partial
testInductive : (Nat, MatchElement)
             -> Either IsoTestError String
testInductive (i, (sq,st,pv,pe,o)) = do
  q <- parseToEither sq
  t <- parseToEither st
  checkResult o i $ inductiveSearch (MkMatchers pe pv) q t

-- Tests ----------------------------------------------------------------------
partial export
subgraphTests : IO ()
subgraphTests = do
  _ <- putStrLn ""
  testAlgo testUllmann   matchList "━ Isomorphism Unit tests - Ullmann ━"
  testAlgo testInductive matchList "━ Isomorphism Unit tests - Inductive search ━"


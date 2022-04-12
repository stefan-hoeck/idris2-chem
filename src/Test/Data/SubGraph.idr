module Test.Data.SubGraph

import Text.Smiles
import Data.SubGraph.Ullmann
import Data.Vect
import Data.List

%default total

-------------------------------------------------------------------------------
-- Types

data IsoTestError = ParseErr String
                  | IsomorphismErr Nat -- Nat is the test example

Show IsoTestError where
   show (IsomorphismErr i) = "Incorrect matching result obtained from substructure search for unit test Nr. " ++ show i
   show (ParseErr s)       = "Failed to parse SMILES string: " ++ s

-- Hit = (SubGraph-) Isomorphism
-- NoMatch = No isomorphism
data Outcome = Hit | NoMatch

-- Type alias
Query : Type
Query = String

Target : Type
Target = String

BondMatcher : Type
BondMatcher = Bond -> Bond -> Bool

AtomMatcher : Type
AtomMatcher = Atom -> Atom -> Bool


-------------------------------------------------------------------------------
-- Test examples
matchList : List (Query, Target, AtomMatcher, BondMatcher, Outcome)
matchList = 
  [
    (""         ,"C"                   ,(==),(==),Hit)             
  , ("CCCO"     ,"CCO"                 ,(==),(==),NoMatch)             
  , ("CC(=O)O"  ,"CC(=O)OCC[N+](C)(C)C",(==),(==),Hit)  -- Acetylcholine
  , ("CN(C)C"   ,"CC1CC(CCN1)N(C)C"    ,(==),(==),Hit)  -- Dimethyl-(2-methyl-piperidin-4-yl)-amine          
  , ("C1CCCCC1" ,"CC1CCCCC1O"          ,(==),(==),Hit)  -- 2-Methylcyclohexanol
  , ("c1ccccc1" ,"CC1CCCCC1O"          ,(==),(==),NoMatch)  -- 2-Methylcyclohexanol
  , ("C1=CC=CC=C1" ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),Hit)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  , ("C[Si]"       ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),Hit)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  ]




-------------------------------------------------------------------------------
-- Functionality
makeTask :   BondMatcher
          -> AtomMatcher
          -> (g : Graph Bond Atom) 
          -> Graph Bond Atom 
          -> Task (length (contexts g)) Bond Atom Bond Atom
makeTask pe pv q t = MkTask pe pv (fromList $ contexts q) t


parseToEither : String -> Either IsoTestError (Graph Bond Atom)
parseToEither s = case parse s of
  End x => Right x
  _     => Left $ ParseErr s


checkResult : Outcome -> Nat -> Maybe a -> Either IsoTestError String
checkResult Hit     i Nothing  = Left (IsomorphismErr i)
checkResult NoMatch i (Just _) = Left (IsomorphismErr i)
checkResult _       i _        = Right $ "  Ex. Nr." ++ show i ++ ": Ok"


testTask :(Nat,(Query, Target, AtomMatcher, BondMatcher, Outcome))
         -> Either IsoTestError String
testTask (i, (sq,st,pv,pe,o)) = do
  q <- parseToEither sq
  t <- parseToEither st
  checkResult o i $ ullmann $ makeTask pe pv q t


-------------------------------------------------------------------------------
||| Unit tests for finding subgraphs
||| Handles iterating over all tests 
||| and printing the result.
export
ullmannUnitTests : IO ()
ullmannUnitTests = 
  let n = length matchList
  in do
  _ <- putStrLn "━ Isomorphism Unit tests ━"
  putStrLn $ toStr $ traverse testTask $ zip [1..n] matchList
  where 
    toStr : Either IsoTestError (List String) -> String
    toStr (Left s)  = show s
    toStr (Right l) = foldl (\a,s => a ++ s ++ "\n") "" l
    

module Test.Data.SubGraph

import Text.Smiles
import Data.SubGraph.Ullmann
import Data.Vect
import Data.List

%default total

-- Type alias
Query : Type
Query = String

Target : Type
Target = String

BondMatcher : Type
BondMatcher = Bond -> Bond -> Bool

AtomMatcher : Type
AtomMatcher = Atom -> Atom -> Bool

Outcome : Type
Outcome = Bool


-- Test examples
matchList : List (Query, Target, AtomMatcher, BondMatcher, Outcome)
matchList = 
  [
    (""         ,"C"                   ,(==),(==),True)             
  , ("CCCO"     ,"CCO"                 ,(==),(==),False)             
  , ("CC(=O)O"  ,"CC(=O)OCC[N+](C)(C)C",(==),(==),True)  -- Acetylcholine
  , ("CN(C)C"   ,"CC1CC(CCN1)N(C)C"    ,(==),(==),True)  -- Dimethyl-(2-methyl-piperidin-4-yl)-amine          
  , ("C1CCCCC1" ,"CC1CCCCC1O"          ,(==),(==),True)  -- 2-Methylcyclohexanol

  , ("C1=CC=CC=C1" ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),True)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  , ("C[Si]"       ,"C[Si](C)(C)C1=CC2=C(C=C1)C(=C(C=C2)O)N=NC3=CC=C(C=C3)[N+](=O)[O-]" ,(==),(==),True)            -- 1-(4-Nitrophenylazo)-6-(trimethylsilyl)-2-naphtol
  ]




-- Functionality
makeTask :   BondMatcher
          -> AtomMatcher
          -> (g : Graph Bond Atom) 
          -> Graph Bond Atom 
          -> Task (length (contexts g)) Bond Atom Bond Atom
makeTask pe pv q t = MkTask pe pv (fromList $ contexts q) t



parseToEither : String -> Either String (Graph Bond Atom)
parseToEither s = case parse s of
  End x => Right x
  _     => Left $ "Parsing to graph failed for " ++ s

testTask : (Query, Target, AtomMatcher, BondMatcher, Outcome) -> Either String String
testTask (sq,st,pv,pe,o) = do
  q <- parseToEither sq
  t <- parseToEither st
  pure $ expResult $ ullmann $ makeTask pe pv q t 
  where
    expResult : Maybe a -> String
    expResult (Just _) = if o then "Ok" else "Did not expect a match for query { " ++ sq ++ " } in target { " ++ st ++ " }"
    expResult Nothing  = if o then "Expected a match for query { " ++ sq ++ " } in target { " ++ st ++" }" else "Ok"



-- Use this function in the repl to test the algorithm
export
ullmannUnitTests : IO ()
ullmannUnitTests = 
  let n = length matchList
  in do
  _ <- putStrLn ("Number of molecules to test: " ++ show n)
  putStrLn $ toStr $ map (zip [1..n]) $ traverse testTask matchList
  where toStr : Either String (List (Nat, String)) -> String
        toStr (Left s)  = s
        toStr (Right l) = foldl (\a,(i,s) => a ++ (show i) ++ ". " ++ s ++ "\n" ) "" l


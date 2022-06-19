module Profile.Data.Isomorphism

import Data.Either
import Data.String
import Data.Maybe
import Data.Vect
import System.File

import Text.Smiles
import Chem.Element
import Profile.Profiler
import Data.SubGraph.InductiveSearch
import Data.SubGraph.Ullmann

-- Query parsing for search ---------------------------------------------------
data ParseError = ParseErr String | WithVertexLabelsErr
Show ParseError where
  show (ParseErr s)        = "Failed to parse string to molecule: " ++ s
  show WithVertexLabelsErr = "Failed to add vertex labels to bonds"

parseNormal : String -> Either ParseError (Graph Bond Atom)
parseNormal s = case parse s of
    End x => Right x
    _     => Left $ ParseErr s

-- Due to type scrutinee own function
relabel : List (Graph e v) -> Maybe (List (Graph (e,v) v))
relabel = traverse withVertexLabels

fromOrgSubset : OrgSubset -> SmilesElem
fromOrgSubset C = El C
fromOrgSubset O = El O
fromOrgSubset N = El N
fromOrgSubset Cl = El Cl
fromOrgSubset Br = El Br
fromOrgSubset S = El S
fromOrgSubset I = El I
fromOrgSubset F = El F
fromOrgSubset B = El B
fromOrgSubset P = El P
fromOrgSubset (OA sa) = A (SA sa)

toSmilesElem : Atom -> SmilesElem
toSmilesElem (SubsetAtom e) = fromOrgSubset e
toSmilesElem (MkAtom _ e _ _ _) = e

graphtoSmilesElem : Graph Bond Atom -> Graph Bond SmilesElem
graphtoSmilesElem = gmap (\(MkContext k l ns) => MkContext k (toSmilesElem l) ns)


-- Accumulate a result for the substructure search ----------------------------
||| Count the number of hits
countMatches : (qry -> trg -> Maybe _)
            -> qry -> List trg
            -> Nat
countMatches f qry l = foldl go 0 l
  where go : Nat -> trg -> Nat
        go k t = if isJust (f qry t) then S k else k

matchingResults : (qry -> trg -> Maybe _)
               -> qry -> List trg
               -> List Bool
matchingResults f q = foldl (\acc, t => isJust (f q t) :: acc) []

-- Graph data preparation -----------------------------------------------------
record QueryData where
  constructor MkQueryData
  str      : String
  graph    : Graph Bond SmilesElem
  graphVL  : Graph (Bond, SmilesElem) SmilesElem

record TargetData where
  constructor MkTargetData
  str      : String
  graph    : Graph Bond SmilesElem
  graphVL  : Graph (Bond, SmilesElem) SmilesElem
  nclasses : List (NodeClass SmilesElem)

mkQD : String -> Either ParseError QueryData
mkQD s =
  let Right g  := map graphtoSmilesElem (parseNormal s) | Left e  => Left e
      Just grl := withVertexLabels g | Nothing => Left WithVertexLabelsErr
  in pure $ MkQueryData s g grl

mkTD : String -> Either ParseError TargetData
mkTD s =
  let Right g  := map graphtoSmilesElem (parseNormal s) | Left e  => Left e
      Just grl := withVertexLabels g | Nothing => Left WithVertexLabelsErr
  in pure $ MkTargetData s g grl (nodeClasses $ contexts g)

-- algorithm application of input type
applyInductive : QueryData -> TargetData -> Maybe Mapping
applyInductive q t = inductiveSearch (MkMatchers (==) (==))
                                     t.nclasses q.graphVL t.graphVL

||| Return type due to constraint errors
applyUllmann : QueryData -> TargetData -> Maybe ()
applyUllmann q t = map (const ()) $ ullmann $
                   MkTask (==) (==) (fromList $ contexts q.graph) t.graph

-- File handling --------------------------------------------------------------
||| Parse the whole file to a list of molecules
parseFile : (String -> Either ParseError a) -> File
         -> IO (Either FileError (List a))
parseFile prse f = go 1
  where go : Nat -> IO (Either FileError (List a))
        go n = do
          False     <- fEOF f     | True => pure $ Right []
          Right str <- fGetLine f | Left err => pure $ Left err
          Right t     <- pure (prse $ trim str)
           | Left st => putStrLn #"Line \#{show n}: \#{show st}. (\#{str})"# >> go (n+1)
          map (map ((::) t)) $ go (n+1)

||| Parse the targets from a file
parseTargets : String -> IO (Either FileError (List TargetData))
parseTargets path = withFile path Read pure (parseFile mkTD)

||| Writes the contents of the result list to the specified file
writeToFile : String -> List String -> String -> IO ()
writeToFile head resList path = do
     Right _ <- writeFile path $ fastUnlines (head :: resList)
       | Left e => putStrLn (show e)
     pure ()

-- Profiling a list of queries ------------------------------------------------

mkqd : List String -> Either ParseError (List QueryData)
mkqd = traverse mkQD -- Due to type scrutinee
mktd : List String -> Either ParseError (List TargetData)
mktd = traverse mkTD -- Due to type scrutinee

profileTargets : (k : Nat) -> (prf : IsSucc k)
              => List TargetData -> List QueryData -> IO (List String)
profileTargets _ _ [] = pure []
profileTargets k {prf = prf} td (q :: qs) = do
          putStrLn  $ "Query: " ++ q.str
          -- Remove the ullmann if it takes too long for some queries
          si <- profileAndReportRes $ MkProfileTask "inductive" q.str (\_ => countMatches applyInductive q td) Z k prf
          su <- profileAndReportRes $ MkProfileTask "ullmann"  q.str (\_ => countMatches applyUllmann q td) Z k prf
          acc <- profileTargets k {prf = prf} td qs
          -- pure $ si :: acc -- alsp adjust this when removing su
          pure $ si :: su :: acc -- alsp adjust this when removing su


||| Profiling for a list of queries
profileZinc : (k : Nat) -> (prf : IsSucc k) => String -> List String
           -> IO (List String)
profileZinc k {prf = prf} path qryStrs =
  let Right qs := mkqd qryStrs | Left e => putStrLn (show e) >> pure []
  in do
    putStrLn $ "Profiling with multiple queries of file: " ++ path
    Right ts <- parseTargets path | Left e => putStrLn (show e) >> pure []
    profileTargets k {prf = prf} ts qs

||| Profiling by applying a matching k times for each query-target pair
profilePairs : (k : Nat) -> (prf : IsSucc k)
                 => List TargetData -> List QueryData
                 -> IO (List String)
profilePairs _ _ [] = pure []
profilePairs k {prf = prf} ts (q :: qs) = do
          putStrLn  $ "Query: " ++ q.str
          new <- go k {prf = prf} q ts
          acc <- profilePairs k {prf = prf} ts qs
          pure $ new ++ acc -- alsp adjust this when removing su
  where go : (k: Nat) -> (prf : IsSucc k ) => QueryData -> List TargetData -> IO (List String)
        go _ _ [] = pure []
        go k {prf = prf} q (t :: ts) = do
          si <- profileAndReportRes $ MkProfileTask "inductive" (q.str ++ " -> " ++ t.str) (\_ => isJust (applyInductive q t)) False k prf
          acc <- go k {prf = prf} q ts
          pure $ si :: acc

profileIndividual : (k : Nat) -> (prf : IsSucc k)
                 => (qsStr : List String) -> (tsStr : List String)
                 -> IO (List String)
profileIndividual k {prf = prf} qsStr tsStr =
  let Right qs := mkqd qsStr | Left e => putStrLn (show e) >> pure []
      Right ts := mktd tsStr | Left e => putStrLn (show e) >> pure []
      in profilePairs k {prf = prf} ts qs

-- Invocation -----------------------------------------------------------------
||| Adjust the queries for different searches and
||| the number in forListOfQueries to change the
||| number of repetitions per profiling
partial export
profile : IO ()
profile =
  let path     = "resources/zinc.txt"
      queries  = ["C1CCCCC1.C(=O)O.c1ccccc1","C(=O)O"]
      --queries  = ["C1CC1","C1CCC1","C1CCCC1","C1CCCCC1","C1CCCCCC1","C1CCCCCCC1","C1CCCCCCCC1","C1CCCCCCCCC1","C1CCCCCCCCCC1","C1CCCCCCCCCCC1","C1CCCCCCCCCCCC1","C1CCCCCCCCCCCC1","C1CCCCCCCCCCCCC1","C1CCCCCCCCCCCCCC1","C1CCCCCCCCCCCCCCC1","C1CCCCCCCCCCCCCCCC1","C1CCCCCCCCCCCCCCCCC1","CC(C)(C)","CCC(CC)(CC)","CCCC(CCC)(CCC)","CCCCC(CCCC)(CCCC)","CCCCC(C)(C)","CCCCC(CC)(CC)","C1(=CC=CC=C1)O","c1ccccc1O","C(C(CO[N+](=O)[O-])O[N+](=O)[O-])O[N+](=O)[O-]"]
      -- targets  = ["CC1(CC(C(C(C1)OC(=O)c2cc(c(c(c2)O)O)O)OC(=O)c3cc(c(c(c3)O)O)O)OC(=O)c4cc(c(c(c4)O)O)O)OC(=O)c5cc(c(c(c5)O)O)O"]
      resFile  = "resources/zincProfiling.txt"
  in do
    putStrLn   "Profiling Isomon Algorithms on ZINC file"
    putStrLn   "Result: Number of matches"
    resList <- profileZinc 1 path queries
    -- resList <- profileIndividual 100000 queries targets
    writeToFile "Process;Repetitions;TotalTime;AverageTime;Result" resList resFile
    pure ()

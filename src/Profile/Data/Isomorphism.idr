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
||| Profiling for a list of queries
forListOfQueries : (k : Nat) -> (prf : IsSucc k) => String -> List String
                -> IO (List String)
forListOfQueries k {prf = prf} path qryStrs =
  let Right qs := mkqd qryStrs | Left e => putStrLn (show e) >> pure []
  in do
    putStrLn $ "Profiling with multiple queries of file: " ++ path
    Right ts <- parseTargets path | Left e => putStrLn (show e) >> pure []
    go ts qs
  where mkqd : List String -> Either ParseError (List QueryData)
        mkqd = traverse mkQD -- Due to type scrutinee
        go : List TargetData -> List QueryData -> IO (List String)
        go _ [] = pure []
        go td (q :: qs) = do
          putStrLn  $ "Query: " ++ q.str
          si <- profileAndReportRes $ MkProfileTask "inductive" q.str (\_ => countMatches applyInductive q td) Z k prf
          su <- profileAndReportRes $ MkProfileTask "ullmann"  q.str (\_ => countMatches applyUllmann q td) Z k prf
          acc <- go td qs
          pure $ si :: su :: acc

-- Invocation -----------------------------------------------------------------
||| Adjust the queries for different searches and
||| the number in forListOfQueries to change the
||| number of repetitions per profiling
partial export
profile : IO ()
profile =
  let path     = "resources/zinc.txt"
      queries  = ["C(=O)O","CCCC"]
      resFile  = "resources/zincProfiling.txt"
  in do
    putStrLn   "Profiling Isomon Algorithms on ZINC file"
    putStrLn   "Result: Number of matches"
    resList <- forListOfQueries 5 path queries
    writeToFile "Process;Repetitions;TotalTime;AverageTime;Result" resList resFile
    pure ()

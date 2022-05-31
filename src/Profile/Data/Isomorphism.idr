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
data ParseError = ParseErr String
Show ParseError where
  show (ParseErr s) = "Failed to parse string to molecule: " ++ s

parseNormal : String -> Either ParseError (Graph Bond Atom)
parseNormal s = case parse s of
    End x => Right x
    _     => Left $ ParseErr s

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

-- File parsing ---------------------------------------------------------------

||| Parse the whole file to a list of molecules
parseFile : (String -> Either ParseError (Graph e v)) -> File
         -> IO (Either FileError (List (Graph e v)))
parseFile prse f = go 1
  where go : Nat -> IO (Either FileError (List (Graph e v)))
        go n = do
          False     <- fEOF f     | True => pure $ Right []
          Right str <- fGetLine f | Left err => pure $ Left err
          Right t     <- pure (prse $ trim str)
           | Left st => putStrLn #"Line \#{show n}: \#{show st}. (\#{str})"# >> go (n+1)
          map (map ((::) t)) $ go (n+1)

-- Apply substructure search --------------------------------------------------
countMatches : (qry -> trg -> Maybe _)
            -> qry -> List trg
            -> Nat
countMatches f qry l = foldl go 0 l
  where go : Nat -> trg -> Nat
        go k t = if isJust (f qry t) then S k else k

-- Profile function -----------------------------------------------------------
||| Parse the file contents to
parseOnly : IO (Either FileError (List (Graph Bond SmilesElem)))
parseOnly = withFile "resources/zinc.txt" Read pure (parseFile (map graphtoSmilesElem . parseNormal))

prepInductive : Eq tv => List (Graph te tv) -> Maybe (List (List (NodeClass tv), Graph (te,tv) tv))
prepInductive l = let Just gs := relabel l | Nothing => Nothing
                  in pure $ map (\g => (nodeClasses $ contexts g, g)) gs

-- Add IO to show errors in creating the nodeclasses

||| Apply Inductive search algorithm
applyInd : Eq le => Eq lv => (q : Graph (le, lv) lv)
        -> (List (NodeClass lv), Graph (le, lv) lv)
        -> Maybe Mapping
applyInd q (ncs,t) = inductiveSearch (MkMatchers (==) (==)) ncs q t


||| Apply Ullmann
applyUllmann :  Eq le => Eq lv => (q : Graph le lv) -> Graph le lv -> Maybe ()
applyUllmann q t = map (const ()) $ ullmann $ MkTask (==) (==) (fromList $ contexts q) t

-- Invocation -----------------------------------------------------------------
||| Profile the ullmann and inductive search
partial export
profile : IO ()
profile = let file = "resources/zinc.txt" in do
    putStrLn "Profiling"
    Right q  <- pure $ map graphtoSmilesElem $ parseNormal "C(=O)O"    | Left _ => putStrLn "Failed to parse query, abort profiling"
    Right l  <- parseOnly                      | Left _ => putStrLn "Failed to parse file, abort profiling"
    Just  qr <- pure $ withVertexLabels q      | Nothing => putStrLn "Failed to relabel the query"
    Just  lr <- pure $ prepInductive l         | Nothing => putStrLn "Failed to prepare list for inductive search"
    profileAndReportRes $ MkProfileTask "inductive" (\_ => countMatches applyInd qr lr) Z 3 ItIsSucc
    profileAndReportRes $ MkProfileTask "ullmann" (\_ => countMatches applyUllmann q l) Z 3 ItIsSucc
    pure ()




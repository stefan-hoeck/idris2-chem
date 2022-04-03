module Test.Data.SubGraph

import Hedgehog
import Text.Smiles
import Data.SubGraph.UllmannImp

-- Initial test -----------------------------------------------------------------

-- Group ----------------------------------------------------------------------
export
props : Group
props = MkGroup "Graph Properties" []


-- Test the functionality -----------------------------------------------------

mp : Graph Bond Atom
mp = empty 

mGraph : String -> Maybe (Graph Bond Atom)
mGraph t = case parse t of
               End g => Just g
               _     => Nothing

settingMatch : Maybe (Settings Bond Atom Bond Atom)
settingMatch = let qry = mGraph "CCO"
                   trg = mGraph "CCCO"
          in MkSettings <$> qry <*> trg
                        <*> pure (==) <*> pure (==)

settingNoMatch : Maybe (Settings Bond Atom Bond Atom)
settingNoMatch = let qry = mGraph "CCO"
                     trg = mGraph "CCC=O"
          in MkSettings <$> qry <*> trg
                        <*> pure (==) <*> pure (==)
export
testUllImp : IO ()
testUllImp = do
  case settingMatch of
      Nothing => putStrLn "Invalid settings for test (query or target)"
      (Just s)=> case ullmannImp s of
                 Nothing => putStrLn "No substructure  -- cncorrect behavior"
                 (Just _)=> putStrLn "Found substructure  -- correct behavior" 
   
  case settingNoMatch of
      Nothing => putStrLn "Invalid settings for test (query or target)"
      (Just s)=> case ullmannImp s of
                 Nothing => putStrLn "No substructure  -- correct behavior"
                 (Just _)=> putStrLn "Found substructure  -- incorrect behavior" 






-- TODO: Mapping is currently in reversed order, but that shouldn't be a problem
-- :module Text.Smiles
-- :let qry = case parse "CCO" of End x => x
-- :let trg = case parse "CCCO" of End x => x
-- :let stt = MkSettings qry trg (==) (==)
-- :let qs = getQueryVertices {s = stt}
-- :let ts = getTargetVertices {s = stt}
-- :let m1 = case prematch {s = stt} of MkPrematched m => m
-- NOTE: The numbering of q
-- :let q3 = case qs of (x :: _) => x
-- :let q2 = case qs of (_ :: x :: _) => x
-- :let q1 = case qs of (_ :: _ :: x :: _) => x
-- :let co1 = getCodomain q2 m1
-- :let t2 = case value co1 of (x :: _) => x
-- :let t1 = case value co1 of (_ :: x :: _) => x
-- removeFromCodomain t2 co1
-- :let ei = case electiveInst co1 of Just (x,_) => x
-- :let m2 = setInst q2 ei m1
-- :let m3 = domainReduction ei [q3] m2
-- :let m4 = domainReduction t1 [q3] m3
-- isIsomorphism m2
-- isIsomorphism m3
-- isIsomorphism m4
-- ullmannImp stt



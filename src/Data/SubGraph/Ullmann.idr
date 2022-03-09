module Data.SubGraph.Ullmann

------------------------------------------------------------------------------
-- References
-- Ullmann [2010]: Bit-Vector Algorithms for Binary Constraint Satisfaction
--                 and Subgraph Isomorphism
--                 Julian R. Ullmann, King's College London, 2010
--
-- Lecoutre [2009]: Reasoning from last conflict(s) in constraing programming
--                  Christophe Lecoutre et al., Elsevier, 2009
--
-- Boussemart []: Boosting Systematic search by weighting constraints
--                Frederic Boussemart et al., ??, ??


import Data.Graph

import Data.Vect
import Data.List
import Data.IntMap

%default total

-- Types ----------------------------------------------------------------------

public export
record Task (n : Nat)  (eq,vq,et,vt : Type)  where
  constructor MkTask
  edgeMatcher   : eq -> et -> Bool
  vertexMatcher : vq -> vt -> Bool
  query         : Vect n (Context eq vq)
  target        : Graph et vt


record Row eq vq et vt where
  constructor MkRow
  ctxt : Context eq vq        -- Query verticex
  trgs : List (Context et vt) -- Target vertices that can match to the query vertex
  0 prf : NonEmpty trgs


0 Matrix : (n : Nat) -> (eq,vq,et,vt : Type) -> Type
Matrix n eq vq et vt = Vect n (Row eq vq et vt)


-- Construct the matrix -------------------------------------------------------

makeRow : Context eq vq -> List (Context et vt) -> Maybe (Row eq vq et vt)
makeRow q []          = Nothing
makeRow q ts@(_ :: _) = pure $ MkRow q ts IsNonEmpty
       
-- Match vertice labels
-- then make sure that the target covers the query vertices required edge types
match : Task n eq vq et vt -> Context eq vq -> Context et vt -> Bool
match ta q t = 
  let vm = (vertexMatcher ta) (label q) (label t)
      em = isNil $ deleteFirstsBy (flip $ edgeMatcher ta) 
           (values $ neighbours q) (values $ neighbours t)
  in vm && em


-- Build initial mapping with all possible mapping targets
init : Task n eq vq et vt -> Maybe (Matrix n eq vq et vt)
init ta = let trgs     = contexts $ target ta
         in traverse (\q => makeRow q $ filter (match ta q) trgs) (query ta)

-- Domain Reduction -----------------------------------------------------------

-- Removes the set value from all remaining rows (ensure injective mapping)
allDifferent :  Context et vt 
             -> Matrix n eq vq et vt
             -> Maybe (Matrix n eq vq et vt)
allDifferent t m = traverse (\r => makeRow (ctxt r) 
                 $ filter ((/=) (node t) . node) (trgs r)) m

-- For all adjacent query vertices p's of q. Remove all possibly mapped to 
-- values of ts in p that are not adjacent & do not have the matching bond
-- to the set value c (of q).
-- Substeps:
-- 1. Find Edge between q & p
-- 2. Filter c's neighbours for the ones with a matching edge
-- 3. Remove ts that are not in the list of step 2.
directReduction :  (eq -> et -> Bool) 
                -> Context eq vq 
                -> Context et vt 
                -> Matrix n eq vq et vt 
                -> Maybe (Matrix n eq vq et vt)
directReduction em qset tset m = 
  let p = \n => elemBy (==) (node $ ctxt n) (keys $ neighbours qset)
  in traverse (\r => if p r then pure r else reduceRow r) m
  where 
   matchTs : Maybe eq -> (Node, et) -> Bool
   matchTs (Just edq) (_,edt) = em edq edt
   matchTs Nothing    _       = False

   reduceRow : Row eq vq et vt -> Maybe (Row eq vq et vt)
   reduceRow (MkRow p ts _) = makeRow p $ filter 
             (flip (elemBy (==)) 
               (map fst $ filter (matchTs 
                (lookup (node p) $ pairs $ neighbours qset)) -- Edge of q to p
                $ pairs $ neighbours tset)     -- List of possible values in p
             . node) ts
                
-- Reduces neighbouring possible mappings & enforces that no value can be
-- mapped to twice (injective function)
reduce :  (eq -> et -> Bool) 
       -> Context eq vq 
       -> Context et vt 
       -> Matrix n eq vq et vt 
       -> Maybe (Matrix n eq vq et vt)
reduce p q t m = directReduction p q t m >>= allDifferent t


-- Ullmann core procedure -----------------------------------------------------

select :  Task n eq vq et vt 
       -> Context eq vq 
       -> List (Context et vt) 
       -> Matrix m eq vq et vt 
       -> Maybe (Vect (S m) Node)

step :  Task n eq vq et vt 
     -> Matrix k eq vq et vt 
     -> Maybe (Vect k Node)

select _  _ []        _ = Nothing
select ta q (t :: ts) m = 
  let Just m1 := reduce (edgeMatcher ta) q t m | Nothing => select ta q ts m
      Just m2  := step ta m1                    | Nothing => select ta q ts m
  in  Just $ node t :: m2 

step _ [] = Just []
step ta (r :: rs) = select ta (ctxt r) (trgs r) rs


-- Accessor function ----------------------------------------------------------

export
ullmann : Task n eq vq et vt -> Maybe (Vect n Node)
ullmann ta = init ta >>= step ta



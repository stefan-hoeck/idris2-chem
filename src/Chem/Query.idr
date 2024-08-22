module Chem.Query

import Chem
import Chem.Aromaticity
import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
import Data.Graph.Indexed.Query.Subgraph
import Data.Vect
import Text.Smiles.AtomType
import Text.Smiles.Types
import Text.Molfile.AtomType
import Text.Molfile.Types

%default total

--------------------------------------------------------------------------------
-- Bonds
--------------------------------------------------------------------------------

||| The type of bond we use at the target molecule of
||| a substructure search
public export
0 TargetBond : Type
TargetBond = AromBond BondOrder

||| The type of bond we use at the query molecule of
||| a substructure search
public export
0 QueryBond : Type
QueryBond = AromBond BondOrder

||| Default matcher for bonds in a substructure search
export
matchBond : QueryBond -> TargetBond -> Bool
matchBond (AB _ True)   t = t.arom
matchBond (AB Single _) t = True
matchBond (AB q _)      t = q == t.type

export
qbond : Cast b BondOrder => AromBond b -> AromBond BondOrder
qbond (AB t v) = AB (cast t) v

--------------------------------------------------------------------------------
-- Atoms
--------------------------------------------------------------------------------

||| Total number (explicit and implicit) of hydrogens bound to an atom.
public export
record TotH where
  constructor TH
  count : Nat

||| Atom type we use for the target in a substructure search.
|||
||| Note: `TotH` is a counter corresponding to the total number (explicit and
||| implicit) of hydrogen atoms bound to an atom.
public export
0 TargetAtom : Type
TargetAtom = Atom Isotope Charge () () TotH () () ()

||| Number of explicit hydrogens bound to an atom.
public export
record ExplicitH where
  constructor EH
  count : Nat

||| Atom type we use for the query in a substructure search.
|||
||| Note: `ExplicitH` is a counter corresponding to number of explicit
||| hydrogens bound to an atom.
public export
0 QueryAtom : Type
QueryAtom = Atom Isotope Charge () () ExplicitH () () ()

matchIso : Isotope -> Isotope -> Bool
matchIso x y = x.elem == y.elem && (x.mass == Nothing || x.mass == y.mass)

||| Default matcher for atoms in a substructure search
export
matchAtom : QueryAtom -> TargetAtom -> Bool
matchAtom q t =
  matchIso q.elem t.elem &&
  (q.charge == 0 || q.charge == t.charge) &&
  q.hydrogen.count <= t.hydrogen.count

--------------------------------------------------------------------------------
-- Converters
--------------------------------------------------------------------------------

||| Graph type we use for the query in substructure searches.
public export
0 QueryGraph : Type
QueryGraph = Graph QueryBond QueryAtom

||| Graph type we use for the target in substructure searches.
public export
0 TargetGraph : Type
TargetGraph = Graph TargetBond TargetAtom

isH : Cast e Isotope => Cast c Charge => Atom e c p r h t ch l -> Bool
isH v = MkI H Nothing == cast v.elem && 0 == cast {to = Charge} v.charge

-- remove explicit hydrogens from a query graph
removeHs : {k : _} -> IGraph k QueryBond QueryAtom -> QueryGraph
removeHs g = snd <$> subgraphL g (filter (not . isH . lab g) (nodes g))

parameters {0 e,c,p,r,h,t,ch,l,b : Type}
           {k        : Nat}
           {auto cb  : Cast b BondOrder}
           {auto cel : Cast e Isotope}
           {auto cch : Cast c Charge}
           (g        : IGraph k (AromBond b) (Atom e c p r h t ch l))

  0 Atm : Type
  Atm = Atom e c p r h t ch l

  explicitHs : AssocList k (AromBond b) -> Nat
  explicitHs ns = count (\(x,_) => isH $ lab g x) (pairs ns)

  qadj : Adj k (AromBond b) Atm -> Adj k QueryBond QueryAtom
  qadj (A lbl bs) =
    let bs2  := map qbond bs
        eh   := explicitHs bs
        lbl2 := MkAtom (cast lbl.elem) (cast lbl.charge) () () (EH eh) () () ()
     in A lbl2 bs2

  tadj : Cast h HCount => Adj k (AromBond b) Atm -> Adj k TargetBond TargetAtom
  tadj (A lbl bs) =
    let bs2  := map qbond bs
        th   := explicitHs bs + cast (value $ cast {to = HCount} lbl.hydrogen)
        lbl2 := MkAtom (cast lbl.elem) (cast lbl.charge) () () (TH th) () () ()
     in A lbl2 bs2

  ||| Convert an aromatized molecular graph to a target graph to be
  ||| used in a subgraph query.
  export %inline
  toTarget : Cast h HCount => IGraph k TargetBond TargetAtom
  toTarget = mapAdj tadj g

  ||| Convert an aromatized molecular graph to a query graph to be
  ||| used in a subgraph query.
  export %inline
  toQuery : Graph QueryBond QueryAtom
  toQuery = removeHs $ mapAdj qadj g

||| Convert a SMILES graph to one used as a query in a substructure search.
export
smilesQuery : SmilesGraphAT -> QueryGraph
smilesQuery sg =
  let G o g := aromatize atomType sg
   in toQuery g

||| Convert a SMILES graph to one used as a target in a substructure search.
export
smilesTarget : SmilesGraphAT -> TargetGraph
smilesTarget sg =
  let G o g := aromatize atomType sg
   in G o $ toTarget g

||| Convert a .mol-file graph to one used as a query in a substructure search.
export
molQuery : MolGraphAT -> QueryGraph
molQuery sg =
  let G o g := aromatize atomType sg
   in toQuery g

||| Convert a .mol-file graph to one used as a target in a substructure search.
export
molTarget : MolGraphAT -> TargetGraph
molTarget sg =
  let G o g := aromatize atomType sg
   in G o $ toTarget g

--------------------------------------------------------------------------------
-- Query
--------------------------------------------------------------------------------

||| Tries to find a mapping from the query graph to the target graph
|||
||| TODO: Add support for a search limit to make this provably total!
export %inline
substructureI :
     {q,t : Nat}
  -> IGraph q QueryBond QueryAtom
  -> IGraph t TargetBond TargetAtom
  -> Maybe (Vect q $ Fin t)
substructureI = assert_total $ query matchBond matchAtom

||| Tries to find a mapping from the query graph to the target graph.
|||
||| The mapping is returned as a list of node indices. If you need stronger
||| quarantees about the indices, consider using `substructureI` for
||| order-indexed graphs.
export %inline
substructure : QueryGraph -> TargetGraph-> Maybe (List Nat)
substructure (G _ qg) (G _ tg) = map finToNat . toList <$> substructureI qg tg

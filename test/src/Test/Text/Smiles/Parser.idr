module Test.Text.Smiles.Parser

import Chem.Element
import Chem.Types
import Data.Prim.Bits64
import Data.Refined
import Data.SOP
import Data.Vect
import Test.Chem.Element
import Test.Chem.Types
import Text.Smiles
import Hedgehog

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

export
chirality : Gen Chirality
chirality = frequency
  [ (5, pure None)
  , (1, element [CW, CCW, TH1, TH2, AL1, AL2, SP1, SP2, SP3])
  , (1, maybe None TB . TBIx.refine <$> bits8 (linear 1 20))
  , (1, maybe None OH . OHIx.refine <$> bits8 (linear 1 20))
  ]

export
subsetAromatic : Gen SubsetAromatic
subsetAromatic = element [ BArom, CArom, NArom, OArom, PArom, SArom]

export
aromatic : Gen Aromatic
aromatic =
  frequency [(1, element [SeArom, AsArom]), (5, map SA subsetAromatic)]

export
orgSubset : Gen OrgSubset
orgSubset = frequency
  [ (5, element [B,C,N,O,F,P,S,Cl,Br,I])
  , (1, map OA subsetAromatic)
  ]

export
smilesElem : Gen SmilesElem
smilesElem = frequency [(5, map El element), (1, map A aromatic)]

export
hcount : Gen HCount
hcount = fromMaybe 0 . refine <$> bits8 (linear 0 9)

export
atom : Gen Atom
atom = choice
  [ [| MkAtom (maybe massNr) smilesElem chirality hcount charge |]
  , map SubsetAtom orgSubset
  ]

export
bond : Gen Bond
bond = element [Sngl,Dbl,Trpl,Quad,Arom]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

parse_atom : Property
parse_atom = property $ do
  a <- forAll atom
  let str = Writer.atom a
  footnote #"Encoded: \#{str}"#
  parse str === End (mkGraph [0 :> a] Nil)

parse_bond : Property
parse_bond = property $ do
  [a1,a2,b] <- forAll $ np [atom,atom,bond]
  let str = #"\#{atom a1}\#{bond b}\#{atom a2}"#
  footnote #"Encoded: \#{str}"#
  parse str === End (mkGraph [0 :> a1, 1 :> a2] [0 <> 1 :> b])

parse_branch : Property
parse_branch = property $ do
  [a1,a2,a3,b1,b2] <- forAll $ np [atom,atom,atom,bond,bond]
  let str = #"\#{atom a1}(\#{bond b1}\#{atom a2})\#{bond b2}\#{atom a3}"#
  footnote #"Encoded: \#{str}"#
  parse str === End (mkGraph [0 :> a1, 1 :> a2, 2 :> a3]
                             [0 <> 1 :> b1, 0 <> 2 :> b2])

parse_ring : Property
parse_ring = property $ do
  [a1,a2,b1] <- forAll $ np [atom,atom,bond]
  let str = #"\#{atom a1}\#{bond b1}1.\#{atom a2}1"#
  footnote #"Encoded: \#{str}"#
  parse str === End (mkGraph [0 :> a1, 1 :> a2] [0 <> 1 :> b1])

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "SMILES Properties"
          [ ("parse_atom", parse_atom)
          , ("parse_bond", parse_bond)
          , ("parse_branch", parse_branch)
          , ("parse_ring", parse_ring)
          ]

module Geom.Gen2D.Rings

import Chem
import Geom.Gen2D.Place
import Geom.Gen2D.State
import Geom.Gen2D.Types
import Data.Graph.Indexed.Ring.Relevant

%default total

parameters {k : _}
           {0 e, n  : Type}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)
           {auto st : PlaceST s k}

  layoutSystem : List (Cycle k) -> F1' s

  placeInitialRing : Subgraph k e n -> F1' s

  export
  placeRing : AttachPoint k -> List (Fin k) -> Subgraph k e n -> F1' s
  placeRing None         ns sg = placeInitialRing sg
  placeRing (Attach p x) ns sg = T1.do
    pp <- nodePosition p
    xp <- nodePosition x
    placeInitialRing sg
    us <- traverse1 (placeNeighbours g) ns
    xq <- nodePosition x
    let f := alignBond pp xp pp xq
    for1_ (ns ++ join us) $ adjPoint f

--     /**
--      * Layout a set of connected rings (ring set/ring system). <br/>
--      *
--      * Current Scheme:
--      *   1. Lookup the entire ring system for a known template.
--      *   2. If first (most complex) ring is macrocycle,
--      *      2a. Assign coordinates from macro cycle templates
--      *   3. If first is not-macrocycle (or currently doesn't match out templates)
--      *      3a. Layout as regular polygon
--      *   4. Sequentially connected layout rings {@link RingPlacer}
--      *
--      * @param firstBondVector A vector giving the placement for the first bond
--      * @param rs              The connected RingSet to layout
--      */
--     private int layoutRingSet(Vector2d firstBondVector, IRingSet rs) {
--
--         // sort small -> large
--         // Get the most complex ring in this RingSet (largest prioritized)
--         RingSetManipulator.sort(rs);
--         final IRing first = RingSetManipulator.getMostComplexRing(rs);
--
--         final boolean macro         = isMacroCycle(first, rs);
--         int result = 0;
--
--         // Check for an exact match (identity) on the entire ring system
--         if (lookupRingSystem(rs, molecule, rs.getAtomContainerCount() > 1)) {
--             if (hasCorrectDoubleBondConfig(first)) {
--                 for (IAtomContainer container : rs.atomContainers())
--                     container.setFlag(IChemObject.PLACED, true);
--                 rs.setFlag(IChemObject.PLACED, true);
--                 return macro ? 2 : 1;
--             }
--         } else {
--             // attempt ring peeling and re-template
--             final IRingSet core = getRingSetCore(rs);
--             if (core.getAtomContainerCount() > 0 &&
--                 core.getAtomContainerCount() < rs.getAtomContainerCount() &&
--                 lookupRingSystem(core, molecule, !macro || rs.getAtomContainerCount() > 1)) {
--                 if (hasCorrectDoubleBondConfig(first)) {
--                     for (IAtomContainer container : core.atomContainers())
--                         container.setFlag(IChemObject.PLACED, true);
--                 }
--             }
--         }
--
--         // Place the most complex ring at the origin of the coordinate system
--         if (!first.getFlag(IChemObject.PLACED)) {
--             IAtomContainer sharedAtoms = placeFirstBond(first.getBond(0), firstBondVector);
--             if (!macro || !macroPlacer.layout(first, rs)) {
--                 // de novo layout of ring as a regular polygon
--                 Vector2d ringCenterVector = ringPlacer.getRingCenterOfFirstRing(first, firstBondVector, bondLength);
--                 ringPlacer.placeRing(first, sharedAtoms, GeometryUtil.get2DCenter(sharedAtoms), ringCenterVector, bondLength);
--             } else {
--                 result = 2;
--             }
--             first.setFlag(IChemObject.PLACED, true);
--         }
--
--         // hint to RingPlacer
--         if (macro) {
--             for (IAtomContainer ring : rs.atomContainers())
--                 ring.setProperty(RingPlacer.SNAP_HINT, true);
--         }
--
--         // Place all connected rings start with those connected to first
--         int thisRing = 0;
--         IRing ring = first;
--         do {
--             if (ring.getFlag(IChemObject.PLACED)) {
--                 ringPlacer.placeConnectedRings(rs, ring, RingPlacer.FUSED, bondLength);
--                 ringPlacer.placeConnectedRings(rs, ring, RingPlacer.BRIDGED, bondLength);
--                 ringPlacer.placeConnectedRings(rs, ring, RingPlacer.SPIRO, bondLength);
--             }
--             thisRing++;
--             if (thisRing == rs.getAtomContainerCount()) {
--                 thisRing = 0;
--             }
--             ring = (IRing) rs.getAtomContainer(thisRing);
--         } while (!allPlaced(rs));
--
--         return result;
--     }

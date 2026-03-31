module Geom.Gen2D.Rings

import Data.Queue
import Chem
import Geom.Gen2D.Place
import Geom.Gen2D.State
import Geom.Gen2D.Types
import Data.Graph.Indexed.Ring.Relevant
import Data.SortedSet

%default total

natoms : Cycle k -> List (Cycle k) -> Nat
natoms c = sum . map (numSharedNodes c)

mostComplex :
     SnocList (Cycle k)
  -> List (Cycle k)
  -> (atms, len : Nat)
  -> Cycle k
  -> (Cycle k, List (Cycle k))
mostComplex sx []      atms len r = (r, sx <>> [])
mostComplex sx (x::xs) atms len r =
 let n := natoms x (sx <>> (r::xs))
  in case compare n atms of
       LT => mostComplex (sx:<x) xs atms len r
       GT => mostComplex (sx:<r) xs n    x.ncycle.length x
       EQ => case len >= x.ncycle.length of
         True  => mostComplex (sx:<x) xs atms len r
         False => mostComplex (sx:<r) xs n    x.ncycle.length x

0 Cycles : Nat -> Type
Cycles = List . Cycle

0 CQueue : Nat -> Type
CQueue = Queue . Cycle

0 CPair : Nat -> Type
CPair k = (CQueue k, Cycles k)

--     /**
--      * Gat a vector perpendicular to the line, a-b, that is pointing
--      * the same direction as 'ref'.
--      *
--      * @param a first coordinate
--      * @param b second coordinate
--      * @param ref reference vector
--      * @return perpendicular vector
--      */
--     private static Vector2d getPerpendicular(Tuple2d a, Tuple2d b, Vector2d ref) {
--         final Vector2d pVec = new Vector2d(-(a.y-b.y), a.x-b.x);
--         if (pVec.dot(ref) < 0)
--             pVec.negate();
--         return pVec;
--     }

fusedToBePlaced : Cycle k -> List (Fin k) -> Maybe (List (Fin k), Fin k, Fin k)
fusedToBePlaced c xs =
 let (ys,z::zs) := break isPlaced (zip (drop 1 xs) xs) | _ => Nothing
  in Just (map snd . drop 1 $ zs ++ ys, z)
  where
    isPlaced : (Fin k, Fin k) -> Bool
    isPlaced (x,y) = contains x c.nodeset && contains y c.nodeset

perpendicular : (ref, v : Vector Id) -> Vector Id
perpendicular ref (V x y) =
 let v2 := V (-y) x
  in if dot v2 ref >= 0 then v2 else negate v2

ringRadius : Nat -> Double
ringRadius 0 = 1.0
ringRadius n = 2 * sin (pi / cast n)

parameters {k : _}
           {0 e, n  : Type}
           {auto ce : Cast n Elem}
           {auto ch : Cast n Hybridization}
           (g : IGraph k e n)
           {auto st : PlaceST s k}

  ngon : Cycle k -> F1' s

  fuseTo : Cycle k -> Cycle k -> F1' s
  fuseTo placed new = T1.do
    let Just (ns,x,y) := fusedToBePlaced placed new.ncycle.path | _ => pure ()
    cr <- centerOf placed.nodes
    px <- nodePosition x
    py <- nodePosition y
    cs <- centerOf [x,y]
    let r  := ringRadius new.ncycle.length
        nr := sqrt (r*r - 0.5*0.5)
        vc := scaleTo nr $ perpendicular (cr - cs) (px - py)
    ?foobar

  --  public void placeFusedRing(IRing ring,
  --                             IAtomContainer sharedAtoms,
  --                             Vector2d ringCenterVector,
  --                             double bondLength) {
  --      logger.debug("RingPlacer.placeFusedRing() start");

  --      double newRingPerpendicular = Math.sqrt(Math.pow(radius, 2) - Math.pow(bondLength / 2, 2));
  --      ringCenterVector.normalize();
  --      logger.debug("placeFusedRing->: ringCenterVector.length()" + ringCenterVector.length());
  --      ringCenterVector.scale(newRingPerpendicular);
  --      final Point2d ringCenter = getMidPoint(pBeg, pEnd);
  --      ringCenter.add(ringCenterVector);

  --      final Vector2d originRingCenterVector = new Vector2d(ringCenter);

  --      pBeg.sub(originRingCenterVector);
  --      pEnd.sub(originRingCenterVector);

  --      final double occupiedAngle = angle(pBeg, pEnd);

  --      final double remainingAngle = (2 * Math.PI) - occupiedAngle;
  --      double addAngle = remainingAngle / (ring.getRingSize() - 1);

  --      IAtom startAtom;

  --      final double centerX = ringCenter.x;
  --      final double centerY = ringCenter.y;

  --      final double xDiff = beg.getPoint2d().x - end.getPoint2d().x;
  --      final double yDiff = beg.getPoint2d().y - end.getPoint2d().y;

  --      double startAngle;

  --      int direction;
  --      // if bond is vertical
  --      if (xDiff == 0) {
  --          logger.debug("placeFusedRing->Bond is vertical");
  --          //starts with the lower Atom
  --          if (beg.getPoint2d().y > end.getPoint2d().y) {
  --              startAtom = beg;
  --          } else {
  --              startAtom = end;
  --          }

  --          //changes the drawing direction
  --          if (centerX < beg.getPoint2d().x) {
  --              direction = 1;
  --          } else {
  --              direction = -1;
  --          }
  --      }

  --      // if bond is not vertical
  --      else {
  --          //starts with the left Atom
  --          if (beg.getPoint2d().x > end.getPoint2d().x) {
  --              startAtom = beg;
  --          } else {
  --              startAtom = end;
  --          }

  --          //changes the drawing direction
  --          if (centerY - beg.getPoint2d().y > (centerX - beg.getPoint2d().x) * yDiff / xDiff) {
  --              direction = 1;
  --          } else {
  --              direction = -1;
  --          }
  --      }
  --      startAngle = GeometryUtil.getAngle(startAtom.getPoint2d().x - ringCenter.x, startAtom.getPoint2d().y
  --              - ringCenter.y);

  --      IAtom currentAtom = startAtom;
  --      // determine first bond in Ring
  --      //        int k = 0;
  --      //        for (k = 0; k < ring.getElectronContainerCount(); k++) {
  --      //            if (ring.getElectronContainer(k) instanceof IBond) break;
  --      //        }
  --      IBond currentBond = sharedAtoms.getBond(0);
  --      Vector atomsToDraw = new Vector();
  --      for (int i = 0; i < ring.getBondCount() - 2; i++) {
  --          currentBond = ring.getNextBond(currentBond, currentAtom);
  --          currentAtom = currentBond.getOther(currentAtom);
  --          atomsToDraw.addElement(currentAtom);
  --      }
  --      addAngle = addAngle * direction;
  --      atomPlacer.populatePolygonCorners(atomsToDraw, ringCenter, startAngle, addAngle, radius);
  --  }

  spiroTo : Cycle k -> Cycle k -> F1' s

  layoutSystem : CQueue k -> Cycles k -> F1' s
  layoutSystem q [] t = () # t
  layoutSystem q xs t =
    case dequeue q of
      Nothing     => () # t
      Just (c,q2) =>
       let (nfs,fs) := partition (isFusedTo c) xs
           (nss,ss) := partition (isSpiro c) nfs
           _ # t    := traverse1_ (fuseTo c) fs t
           _ # t    := traverse1_ (spiroTo c) ss t
           q3       := enqueueAll q2 (fs++ss)
        in layoutSystem (assert_smaller q q3) nss t

  placeInitialRing : Subgraph k e n -> F1' s
  placeInitialRing sg = T1.do
   let c::cs  := mcb $ componentCycles sg | [] => pure ()
       (r,rs) := mostComplex [<] cs (natoms c cs) (c.ncycle.length) c
   ngon r
   layoutSystem (Queue.fromList [r]) rs

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

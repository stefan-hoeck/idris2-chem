module Main

import Text.Inchi
import Chem.AtomType
import Chem.Rings.Relevant
import Data.Graph.Indexed.Subgraph
import Data.String
import Data.Vect
import System
import System.UV
import System.UV.File
import Text.Molfile
import Text.Smiles
import System

c60 : Either String (Graph () ())
c60 =
  let s := "C12=C3C4=C5C6=C1C7=C8C9=C1C%10=C%11C(=C29)C3=C2C3=C4C4=C5C5=C9C6=C7C6=C7C8=C1C1=C8C%10=C%10C%11=C2C2=C3C3=C4C4=C5C5=C%11C%12=C(C6=C95)C7=C1C1=C%12C5=C%11C4=C3C3=C5C(=C81)C%10=C23"
   in bimap (const ()) (const ()) <$> readSmiles' s

c70 : Either String (Graph () ())
c70 =
  let s := "C12=C3C4=C5C6=C7C8=C9C%10=C%11C%12=C%13C%10=C%10C8=C5C1=C%10C1=C%13C5=C8C1=C2C1=C3C2=C3C%10=C%13C%14=C3C1=C8C1=C3C5=C%12C5=C8C%11=C%11C9=C7C7=C9C6=C4C2=C2C%10=C4C(=C29)C2=C6C(=C8C8=C9C6=C4C%13=C9C(=C%141)C3=C85)C%11=C27"
   in bimap (const ()) (const ()) <$> readSmiles' s

hegoTest : Either String (Graph () ())
hegoTest =
  let s := "C1CC2CCC1CC2"
   in bimap (const ()) (const ()) <$> readSmiles' s

natEdge : {n : Nat} -> (x,y : Nat) -> Maybe (Edge n ())
natEdge x y = join [| mkEdge (tryNatToFin x) (tryNatToFin y) (pure ()) |]

toNext : {n : Nat} -> (x : Nat) -> Maybe (Edge n ())
toNext x = natEdge x (S x)

-- a chain of `n` fused cyclohexane rings
chain : (n : Nat) -> IGraph (4*n+2) () ()
chain n =
  let tot := 4*n + 2
   in mkGraph
        (replicate _ ())
        (catMaybes $ map toNext [0..tot] ++ map close [0..n])
  where
    close : Nat -> Maybe (Edge (4*n+2) ())
    close x = natEdge (2 * x) ((4*n+1) `minus` (2*x)) 

-- an `S m x S n` square grid 
grid : (m,n : Nat) -> IGraph (S m * S n) () ()
grid m n =
  mkGraph (replicate _ ()) (ho ++ ve)
  where
    ho, ve : List (Edge (S m * S n) ())
    ho = do
      x <- [0..m]
      y <- [0..S n]
      let p := x + S m * y
      toList $ natEdge p (S p)

    ve = do
      x <- [0..S m]
      y <- [0..n]
      let p := x + S m * y
      toList $ natEdge p (p + S m)

-- a bracelet of `n` fused cyclohexane rings
bracelet : (n : Nat) -> IGraph (4*n+2) () ()
bracelet n =
  let tot := 4*n + 2
   in mkGraph
        (replicate _ ())
        (catMaybes $ map toNext [0..tot] ++ map close [0..n] ++ [natEdge 0 (2*n), natEdge (2*n+1) (pred tot)])
  where
    close : Nat -> Maybe (Edge (4*n+2) ())
    close x = natEdge (2 * x) ((4*n+1) `minus` (2*x)) 

-- a sequence of `n` isolate cyclohexane rings
seq : (n : Nat) -> IGraph (6*n) () ()
seq n =
  mkGraph
    (replicate _ ())
    (catMaybes $ ([0..n] >>= ring . (6*)) ++ map link [0..n])
  where
    ring : Nat -> List (Maybe $ Edge (6*n) ())
    ring k = natEdge k (k+5) :: map (\x => natEdge (k+x) (k+x+1)) [0..4]

    link : Nat -> Maybe (Edge (6*n) ())
    link k = natEdge (k*6 + 3) (k*6 + 6)

readGraph : List String -> Either String (Graph () ())
readGraph [ "fullerene" ] = c60
readGraph [ "c60" ]       = c60
readGraph [ "c70" ]       = c70
readGraph [ "ht" ]        = hegoTest
readGraph ["chain", n]    = Right (G _ $ chain (cast n))
readGraph ["bracelet", n] = Right (G _ $ bracelet (cast n))
readGraph ["seq", n]      = Right (G _ $ seq (cast n))
readGraph ["grid", m,n]   = Right (G _ $ grid (cast m) (cast n))
readGraph [s]             = bimap (const ()) (const ()) <$> readSmiles' s
readGraph ss              = Left "Invalid args: \{show ss}"

0 Errs : List Type
Errs = [UVError,SmilesParseErr,UVFileError]

0 DocIO : Type -> Type
DocIO = Async Errs

handles : UVLoop => All (\x => x -> Async [] ()) Errs
handles = [putStrLn . interpolate, putStrLn . interpolate, putStrLn . interpolate]

runDoc : (UVLoop => DocIO ()) -> IO ()
runDoc doc = runUV $ handle handles doc

relevant : (Nat,Nat) -> ByteString -> (Nat,Nat)
relevant (x,y) bs =
  case (\(G _ g) => length $ computeCI' g) <$> readSmiles {es = Errs} (toString bs) of
    Left _  => (x,S y)
    Right n => (n + x, y)

acc : (Nat,Nat) -> ByteString -> (Nat,Nat)
acc (x,y) bs =
  case map perceiveSmilesAtomTypes $ readSmiles {es = Errs} (toString bs) of
    Left _  => (x,S y)
    Right _ => (S x, y)

inchi : (Nat,Nat) -> ByteString -> (Nat,Nat)
inchi (x,y) bs =
  case genInchiForSmiles (toString bs) of
    Left _  => (x,S y)
    Right s => (x + length s, y)

app : UVLoop => (accum : (Nat,Nat) -> ByteString -> (Nat,Nat)) -> DocIO ()
app accum = do
  (_::p::_) <- getArgs | _ => putErrLn "Invalid number of arguments."
  (x,y) <- foldLines p 0xffff accum (0,0)
  putOutLn "Got a count of \{show x}"
  putOutLn "Encountered \{show y} errors."

main : IO ()
-- main = runDoc (app relevant)
main = do
  _::t <- getArgs | _ => die "Invalid number of arguments"
  Right (G o g) <- pure (readGraph t) | Left err => putStrLn err
  let cs := computeCI' g
  putStrLn "Found \{show $ length cs} potentially relevant cycles (\{show o})"
  for_ cs printLn

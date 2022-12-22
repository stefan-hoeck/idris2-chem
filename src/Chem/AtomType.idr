module Chem.AtomType

{-
  Stefan Höck: This project is should be based on the source code
  from your bachelor's thesis.

  The goal of this coding project is to clean up that code and get rid of
  all repeating patterns. In order to do so, there are several things you
  should keep in mind:

    * Don't use `String` for atom types: Define an enum type deriving
      `Show`, `Eq` and `Ord` for it, and keep adding new atom types when
      they show up.

    * Most atom types are percieved by comparing the following things:
      element, aromaticity, charge, number and types of bonds (including
      bonds to implicit hydrogen atoms). Group these in a record type and
      derive `Show`, `Eq, and `Ord` for it.

      Now, have a look at function `Data.List.lookup`. Can you see, how
      you can make use of this function plus a list of pairs to come
      up with a general purpose perception function? The list of pairs
      must not be generated anew every time we percieve atom types, so
      use a top-level constant for it.

    * A few atom types require special treatment. Implement those checks
      separately and decide for each of them, whether it should be checked
      before or after running the general perception algorithm.

    * In the end, write a function for converting a graph of type `Graph Bond (Atom ())`
      to a `Maybe (Graph Bond (Atom AtomType))`.

    * Only implement atom types already present in your Bachelor's thesis.

  Marking criteria:

    * Correctness of implementation (write a couple of tests/proofs)
    * DRY-ness of code ("DRY" = "Don't Repeat Yourself")
    * Making use of existing functions from the Idris standard libs.
      (example: `Data.List`, and stuff from the Prelude)
    * Separation of concerns: Split error handling from the rest of
      the functionality. Same goes for grouping / sorting of bonds.
    * Use docstrings / comments to document your code (especially special cases)

  Deadline: 31.01.2023

  A good example for things to watch out for is the following code excerpt:

    ```
    hasODbl : List (Elem,Bond) -> Nat
    hasODbl [] = 0
    hasODbl ((O,Dbl) :: xs) = 1 + hasODbl xs
    hasODbl ((x, y) :: xs) = 0 + hasODbl xs

    hasSDbl : List (Elem,Bond) -> Nat
    hasSDbl [] = 0
    hasSDbl ((S,Dbl) :: xs) = 1 + hasSDbl xs
    hasSDbl ((x, y) :: xs) = 0 + hasSDbl xs

    hasNDbl : List (Elem,Bond) -> Nat
    hasNDbl [] = 0
    hasNDbl ((N,Dbl) :: xs) = 1 + hasNDbl xs
    hasNDbl ((x, y) :: xs) = 0 + hasNDbl xs
    ```

  This is neither DRY (repeats the same code several times), nor does it make
  use of existing functionality (look at `Prelude.count`).
-}

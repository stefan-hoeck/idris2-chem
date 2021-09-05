# Part 1: Functions, ADTs, and Pattern Matching

Idris2 is in many aspekts very similar to Haskell. In this
first part, we will focus on the similarities, so it will
be straight forward for users with a Haskell background
to follow along. This is a literate Idris2 file, and all
Idris2 code will be wrapped in triple backticks as in
the following preamble:

```idris
-- An Idris2 module name must match its file name
module Doc.Tut1

-- Idris2 comes with a totality checker, which can verify
-- that the functions we write are provably total, that is,
-- they will yield a result of the given type in a finite
-- amount of time, without throwing an exception or
-- looping forever.
--
-- We will say more about totality checking later on,
-- for now, just consider turning the totality checker on
-- for all functions as a default, by starting each Idris2
-- source file with the following pragma:
%default total
```

## Before we begin

Idris2 comes with its own REPL (read eval print loop), which
is very basic at the moment (no tab-completion and no command history),
but allows us already to inspect types and holes in detail, which
can be very useful. In order to get a better REPL experience, it
is suggested to run it from within the command line utility
`rlwrap`, which has to be installed separately on your
operating system.

To load this literate Idris2 file into the REPL and try some
of the examples yourself, the following command issued from
the project's root folder (where the .ipkg files are) should do:

```
rlwrap idris2 --find-ipkg src/Doc/Tut1.md
```

## Function Definitions

We start with some simple function definitions.

```idris
square : Integer -> Integer
square x = x * x
```

The above, is almost exactly like Haskell, the only difference
being that Idris2 uses a single colon `:` in type signatures.

Function composition can be done using the dot operator `(.)`:

```idris
shout : String -> String
shout = pack . map toUpper . unpack
```

If you'd like to inspekt the type of a function in the REPL,
write `:t` followed by the function name:

```
> :t unpack
Prelude.unpack : String -> List Char
```

As can be seen, `String` in Idris2 is a primitive data type
unlike in Haskell, where it is an alias for `[Char]`. Also,
the type of a list of characters is `List Char`, unlike in
Haskell, where it is `[Char]`.

Idris2 has a similar constructs to Haskell's type classes. In
Idris2, they are called 'interfaces'. We use them constrain
the types of values accepted by a function:

```idris
printSquare : Num a => Show a => a -> IO ()
printSquare x = printLn $ x * x
```

To run an `IO` action at the REPL, use the `:exec` command:

```
> :exec printSquare 100
10000
```

As in Haskell, we can use patten matching to deconstruct
values of algebraic data types:

```idris
eitherToNat : Either String Integer -> Nat
eitherToNat (Left str) = length str
eitherToNat (Right n)  = cast n
```

Make it your habbit to inspect new functions and types at the
REPL:

```
> :doc Nat
...
> :t length
...
> :doc length
...
> :t cast
...
> :doc Cast
```

Before we leave this section, here is one last example.
In the following type signature, we use syntax special
to Idris2 to give names to the function arguments:

```idris
namedArgs : Show a => (name : String) -> (value : a) -> String
namedArgs name value = name ++ ": " ++ show value
```

We can give names to arguments as a means of documentation
but later on, we will see a much more important use for naming
arguments: We can refer to them later in the type signature, and
that's what dependent types are all about! Here's a teaser
example:

```idris
natOrString : (b : Bool) -> if b then Nat else String
natOrString True = 10
natOrString False = "OK, a String it be!"
```

In the above example, the result type *depended* on one of
the arguments passed to the functions, and we used the
*value* (`b`) of that argument, to calculate the return
type in the type signature! Welcome, to dependent types!

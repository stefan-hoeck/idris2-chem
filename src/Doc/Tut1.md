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
can be very useful. In order to get a better REPL experience including
a command history, it is suggested to run it from within
the command line utility `rlwrap`, which has to be installed
separately on your operating system.

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

The above is almost exactly like Haskell the only difference
being that Idris2 uses a single colon `:` in type signatures.

Function composition can be done using the dot operator `(.)`:

```idris
shout : String -> String
shout = pack . map toUpper . unpack
```

If you'd like to inspect the type of a function in the REPL,
write `:t` followed by the function name. Use `:doc`
to print the function's docstring:

```
> :t unpack
Prelude.unpack : String -> List Char
> :doc unpack
...
```

As can be seen, `String` in Idris2 is a primitive data type
unlike in Haskell, where it is an alias for `[Char]`. Also,
the type of a list of characters is `List Char`, unlike in
Haskell, where it is `[Char]`.

Idris2 has a similar construct to Haskell's type classes. In
Idris2, they are called 'interfaces'. We use them to constrain
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

### Holes

One of the main aspekts of programming in Idris2, is to get
as much help from the type checker as possible. Idris2 can
tell you all about the types in scope, can automatically
generate pattern matching clauses for you (if your editor
supports it), it sometimes can even write whole programs
for you just from the type declarations.

In this section we look at holes.

```idris
getNat : Either (String,Bits8,Nat) (Nat,List Bool) -> Nat
getNat (Left  (x,y,z)) = ?leftClause
getNat (Right (x,y)) = ?rightClause
```

If you get lost in a complex function implementation and
want to have a look at what's going on, just enter a
hole (also called a meta variable) by prefixing a name
with a question mark. Load the file in question into
the REPL, and have a look at the types: `:m` lists
all meta variables, `:t` can be used to dispaly their
types:

```
> :t leftClause
  x : String
  y : Bits8
  z : Nat
```

### Visibility

In order to make functions visible from other modules,
we need to export them. There are three types of
visibilities: `private` (the default: such a function
is not accessible from other modules), `export` (the
function's type signature is exported and it can be
called from other modules), and `public export`
(the function including its implementation is exported).

`private` functions can only be accessed from the module
where they are defined plus all child modules. For instance,
our function `square` would also be accessible from a
hypothetical module `Doc.Tut1.Extra`, for instance.

`public export` functions are necessary to use a function's
implementation in typelevel calculations. This will become
important when we start talking about dependent types.

An example:

```idris
public export
isEven : Integer -> Bool
isEven n = n `mod` 2 == 0
```

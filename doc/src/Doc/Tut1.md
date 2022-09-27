# Part 1: Functions, ADTs, and Pattern Matching

Idris is in many aspekts very similar to Haskell. In this
first part, we will focus on the similarities, so it will
be straight forward for users with a Haskell background
to follow along. This is a literate Idris file, and all
Idris code will be wrapped in triple backticks as in
the following preamble:

```idris
-- An Idris module name must match its file name
module Doc.Tut1

-- Idris comes with a totality checker, which can verify
-- that the functions we write are provably total, that is,
-- they will yield a result of the given type in a finite
-- amount of time, without throwing an exception or
-- looping forever.
--
-- We will say more about totality checking later on,
-- for now, just consider turning the totality checker on
-- for all functions as a default, by starting each Idris
-- source file with the following pragma:
%default total
```

## Before we begin

Idris comes with its own REPL (read eval print loop), which
is very basic at the moment (no tab-completion and no command history),
but allows us already to inspect types and holes in detail, which
can be very useful. In order to get a better REPL experience including
a command history, it is suggested to run it from within
the command line utility `rlwrap`, which has to be installed
separately on your operating system.

To load this literate Idris file into the REPL and try some
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
being that Idris uses a single colon `:` in type signatures.

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

As can be seen, `String` in Idris is a primitive data type
unlike in Haskell, where it is an alias for `[Char]`. Also,
the type of a list of characters is `List Char`, unlike in
Haskell, where it is `[Char]`.

Idris has a similar construct to Haskell's type classes. In
Idris, they are called 'interfaces'. We use them to constrain
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

Make it your habit to inspect new functions and types at the
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
to Idris to give names to the function arguments:

```idris
namedArgs : Show a => (name : String) -> (value : a) -> String
namedArgs name value = name ++ ": " ++ show value
```

We can give names to arguments as a means of documentation,
but later on we will see a much more important use for naming
arguments: We can refer to them later in the type signature, and
that's what dependent types are all about! Here's a teaser
example:

```idris
natOrString : (b : Bool) -> if b then Nat else String
natOrString True  = 10
natOrString False = "OK, a String it be!"
```

In the above example, the result type *depends* on one of
the arguments passed to the function, and we used the
*value* (`b`) of that argument, to calculate the return
type in the type signature! Welcome, to dependent types!

### Holes

One of the main aspects of programming in Idris, is to get
as much help from the type checker as possible. Idris can
tell you all about the types in scope, can automatically
generate pattern matching clauses for you (if your editor
supports it), it sometimes can even write whole programs
for you just from the type declarations.

In this section we look at holes.

```idris
getNat : Either (String,Bits8,Nat) (Nat,List Bool) -> Nat
getNat (Left  (x,y,z)) = ?leftClause
getNat (Right (x,y))   = ?rightClause
```

If you get lost in a complex function implementation and
want to have a look at what's going on, just enter a
hole (also called a meta variable) by prefixing an identifier
with a question mark. Load the file in question into
the REPL, and have a look at the types: `:m` lists
all meta variables, `:t` can be used to dispaly their
types:

```
> :t leftClause
  x : String
  y : Bits8
  z : Nat
------------------------------
leftClause : Nat
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

## Algebraic Data Types

For simple algebraic data types, Idris uses the same syntax
as Haskell. Below is a simple enum type for genders:

```idris
public export
data Gender = Male | Female | NonBinary
```

For data types, `public export` means that the type and data
constructors will be available from other modules. With
only `export` the type is abstract: Its constructors will
not be exported. In most cases, we therefore use `public export`.

Of course, we can also define constructors that take arguments:

```idris
public export
data Error = ReadError String
           | OutOfMemory
           | ParseError Int Int String
```

Finally, data types can be parameterized:

```idris
public export
data Option a = Yes a | No
```

### Records

Whenever we define a data type with only a single
constructor, we use record syntax.

```idris
public export
record Employee where
  constructor MkEmployee
  name       : String
  gender     : Gender
  age        : Nat
  salary     : Double
  supervisor : Maybe Employee
```  

As can be seen, we use slightly different syntax as in
Haskell here. The code snippet below shows, how we can
create `Employee`s, how we can access their fields,
how we can update their fields, and how we can pattern
match on them:

```idris
jane : Employee
jane = MkEmployee "Jane" Female 55 5678.0 Nothing

john : Employee
john = MkEmployee "John" Male 23 2500.0 (Just jane)

ageOfJohn : Nat
ageOfJohn = age john

||| Emily is Jane's twin sister, so we copy most
||| of her
emily : Employee
emily = { name := "Emily", salary := 6000.0 } jane

||| It's John's birthday, so we increase his age by
||| one. `S` is the successor constructor for natural
||| numbers (see `:doc Nat` in the REPL). We could
||| also have written `(+1)` instead.
johnPlus1 : Employee
johnPlus1 = { age $= S } john

||| Here, we pattern match on a record.
||| We also use string interpolation to create
||| the report string.
employeeReport : Employee -> String
employeeReport (MkEmployee nm _ age _ _) =
  #"Employee \#{nm} is \#{show age} years old"#
```

### Newtypes

Haskell has a special construct for single
constructor data types wrapping just a single value:
`newtype`s. In Idris, there is no such thing, however,
single value wrappers are automatically discarded by
the backends, so the effect is the same as with
Haskell's `newtype`s. For instance, in the following
example, values of type `Celsius` are just plain
`Double`s at the backends. This is independet of whether
we define the data type using the `record` or `data`
keyword:

```idris
record Celsius where
  constructor MkCelsius
  value : Double
```

### Interfaces

As mentioned above, Idris comes with a similar construct
as Haskell's type classes: Interfaces. We will see later that
they are actually quite a bit different: They are just
records that Idris will insert automatically as function
arguments where we need them. But that's for another tutorial.

Let's implement `Eq` for `Gender`:

```idris
Eq Gender where
  Male      == Male      = True
  Female    == Female    = True
  NonBinary == NonBinary = True
  _         == _         = False
```

Unfortunately, Idris does not yet provide utilities for
deriving interface implementations automatically as is
possible in Haskell. However, there is
[idris2-sop](https://github.com/stefan-hoeck/idris2-sop),
a library based on
elaborator reflection (a way to programmatically create
Idris code by inspecting existing types and their structure
at compile time), which can do that.

### Exercises

Before we continue, it is probably a good idea to quickly
write some code in Idris. Solutions to the exercises are
available [here](Tut1/Sol.idr).

#### 1. A Simple Enum Type

Below is the definition of a simple enum type for a subset of chemical
elements:

```idris
public export
data Element =
    H                           | He
  | Li | B  | C  | N  | O  | F  | Ne
                 | P  | S  | Cl | Ar
                      | Se | Br | Kr
```

Implement the following functions for `Element` (`read`
should convert the symbol back to an `Element`):

```
atomicNr : Element -> Bits8

fromAtomicNr : Bits8 -> Maybe Element

symbol : Element -> String

read : String -> Maybe Element
```

Provide implementations for interfaces `Eq`, `Ord`, and `Show`
using `atomicNr` and `symbol` in your implementations.
Have a look at the type and documentation of function `on`
from the prelude to help you with this.

Note that `Bits8` is an unsigned integer primitive
ranging from 0 to 255.
`Bits64`. There are also the signed counterparts:
`Int8` up to `Int64`. Finally, `Integer` is a signed
arbitrary precision integral type, and `Nat` is
an unsigned arbitrary precision integral type (with a
lot of magic support from the compiler because it is
so important for writing proofs in Idris).
All of these support the usual arithmetic operations,
and you can use integer literals like `12` to
create a value for one of these types.

#### 2. A Binary Tree

Below is a simple data type for binary trees:

```idris
data BTree a = Leaf
             | Node (BTree a) a (BTree a)
```

Implement interfaces `Eq`, `Ord`, `Functor`, `Foldable`, and `Traversable`
for `BTree`.
In addition, implement the following two functions on
`BTree`:

```
size : BTree a -> Nat

depth : BTree a -> Nat
```

`size` should represent the number of values stored in a `BTree`.
It can be implemented using `foldl`, for instance.
`depth` should represent the maximum number of constructors
before we reach a `Leaf` from the given `BTree`.

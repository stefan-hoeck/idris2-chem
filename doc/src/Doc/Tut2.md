# Part 2: Type Families

What we have seen in the [first part of the tutorial](Tut1.md)
is just plain functional programming very much in the style
of Haskell. We are now ready to start talking about types
in earnest. Fasten your seat belt.

```idris
module Doc.Tut2

import Data.Nat
import Doc.Tut1
import Doc.Tut1.Sol

%default total
```

## The Truth about Idris Type Signatures

Before we start defining more interesting and precise
data types, we need to have a look at the full glory of
Idris type signatures. Open a REPL and enter `:t either`:

```
> :t either
Prelude.either : Lazy (a -> c) -> Lazy (b -> c) -> Either a b -> c
```

That's straight forward to understand: Like the equally named function
in Haskell, `either` takes two functions to extract a value from
an `Either a b`. Since Idris has strict semantics as a default and we at most
need one of the two functions, they are wrapped in a `Lazy` here, meaning
they will only be evaluated when needed.
We will not need lazy evaluation too often, so we won't go into
more details here.

### Implicit Arguments

Now, this is not the full type signature as perceived by Idris. 
In order to have a look at the full type signature, we need to
use `:ti` (that's "give me the type including implicit arguments"):

```
> :ti either
Prelude.either : {0 b : Type} -> {0 c : Type} -> {0 a : Type} -> ...
```

In order to truly understand Idris, programmers *must* be able to digest this.
Arguments in a type signature wrapped in curly braces, are
called 'implicit' arguments. We can always pass them explicitly,
as we will see in a moment, but in the general case, we
expect Idris to figure them out by itself and insert them for us.

For instance, in the following example, it is trivial for
Idris to figure out that `a = String`, `b = Int64`, and `c = Nat`:

```idris
extractNat : Either String Int64 -> Nat
extractNat = either length cast
```

However, consider the following interface:

```idris
interface Read a where
  constructor MkRead
  readMaybe : String -> Maybe a

Read Element where
  readMaybe = read

Read Bool where
  readMaybe "True"  = Just True
  readMaybe "False" = Just False
  readMaybe _       = Nothing
```

Please ignore the `MkRead` constructor for now. We will make
us of it later on. (We could also omit it, but it often comes in
handy to give interfaces their own explicit constructor name, hence
I consider it to be good practice to do so).
Now, go to the REPL and inspect the full type signature of `readMaybe`:

```
> :ti readMaybe
Doc.Tut2.readMaybe : {0 a : Type} -> Read a => String -> Maybe 
```

Again, it includes an implicit argument `a` of type `Type`, plus a
constraint of type `Read a`, where `a` is the same `a` as used
in the beginning of the type signature. Now, try enter `readMaybe "True"`
at the REPL:

```
> readMaybe "True"
Error: Can't find an implementation for Read ?a.
...
```

Uh oh. A type error. What Idris is actually trying to say is,
that it doesn't even know what `a` should be as it can't infer it (how should it?).
So, Idris enters its own hole (`?a`) meaning 'I'll figure out that part
later', but now it complains that there is no implementation for `Read ?a`.

How can we tell Idris that we mean `a` to be `Bool` here? By passing
the argument explicitly:

```
> readMaybe {a = Bool} "True"
Just True
```

Haskell has similar issues and it provides its own language extension
called 'TypeApplications' to solve this. There is no need for any kind
of extension in Idris here, and we will often make use of this.

We are free to chose and only pass certain implicit arguments
if needed. For instance, try the following:

```
> either length cast $ Left "foo"
Error: Ambiguous elaboration. Possible results:
...
```

Here, Idris complains that there are two functions named `length`
in scope (Idris supports overloading of names and is usually pretty good
at disambiguating between them via their types). 
How to proceed? In case of ambiguous names, we can give a unique suffix
of the fully qualified name. Here, the possible fully qualified names
are `Prelude.String.length`, and `Prelude.List.length`, so
it is sufficient to write `String.length` to disambiguate between
the two.

```
> either String.length cast $ Left "foo"
Error: Can't find an implementation for Cast ?from ?to.
...
```

Well, that sort of worked, but now Idris is at a loss of which
implementation of `Cast` to choose. It should be able to
figure out the `?to` part: `String.length` is a function from
`String` to `Nat`, so `?to` should be `Nat`. It still needs
help with the `?from`. What version of `Either String ?` should
we use? Lets opt for `Integer`:

```
> either {b = Integer} String.length cast $ Left "foo"
3
```

As can be seen, there is no need to also be explicit about `a`
and `c`: Idris can figure out those by itself. It's also
not necessary to specify implicit arguments in the correct order,
as we name them explicitly anyway. For instance:

```
> either {a = Int32} {b = Bits8} {c = Integer} cast cast (Left 12)
12
```

### Quantities

There is another peculiarity in the type signature of `either`:

```
> :ti either
Prelude.either : {0 b : Type} -> {0 c : Type} -> {0 a : Type} -> ...
```

What are those zeroes doing there? Idris implements something called
'quantitative type theory'. That sounds complicated, and it can be, however
in our case we are only interested in the two simple cases most of
the time. A quantity in a type signature describes, how often an
argument will be used in the function's implementation:
Quantity `0` means *not at all*, and it is a type error to
use it (for instance by pattern matching on it or passing it
as a non-zero quantity argument to another function). This is
really great, because it allows Idris to erase all values of
quantity `0` at runtime, as they are provably never ever used.
Quantity `1` means *exactly once*, and this is the most difficult
case. We will rarely use this, and won't go into the details here.
As a teaser, `IO` is implemented by using quantity `1`.
The third case is the one we use most of the time: Arbitrarily often.
This is the default Idris choses when we give no quantity at
all.

Therefore, whenever we want to make sure that a value makes
no appearance at runtime, we annotate it with a zero quantity.

For instance, instead of passing an implicit argument to `readMaybe`
explicitly, it would be convenient be have it as an (erased) explicit
argument in the first place
to spare us from having to use curly braces. In Idris,
this is straight forward:

```idris
readMay : (0 a : Type) -> Read a => String -> Maybe a
readMay _ = readMaybe
```

And in the REPL:

```
readMay Bool "True"
Just True
```

Please take some time to figure out what's going on in the
type signature above: The first argument `a` is a provably
erased value of type `Type`, the second is a constraint
of type `Read a` (of quantity 'many'), and the third is
a `String`, again of quantity 'many'. The result is
then a `Maybe a`.

### Auto Implicits

Sometimes, we'd like Idris to find and insert a value of a given type for
us, that it will not be able to determine through type inference alone.
The most common (for now) use case for this is finding
interface implementations.
Our type signature for `readMay` is actually syntactic sugar for
the following more exact signature:

```idris
readMay2 : (0 a : Type) -> {auto _ : Read a} -> String -> Maybe a
readMay2 _ = readMaybe
```

In plain english this means: There is a second implicit argument
(without a name, hence the underscore) of type `Read a`, and we'd
like Idris to try very hard and construct a value of this type
from the implicit scope (that's what the `auto` stands for: perform
an automatic search on the given type and insert it for us).
The implicit scope holds (amongst other things)
all interface implementations.

The immediate question that arises is of course: If `Read a` in the
signature above is just another implicit argument, could we also
provide this manually, that is, can we actually pass values of
type `Read a` around?
The answer - and that's a huge difference from Haskell - is *yes*!
To make this easier, we just give the argument a proper name:

```idris
readMay3 : {auto impl : Read a} -> String -> Maybe a
readMay3 = readMaybe
```

Now, interfaces are just records, and implementations are just values
of those records. If we so like, we can implement them manually
without any fancy syntax (and there are Idris developers, who perfer
implementing them always like this):

```idris
readInt32 : Read Int32
readInt32 = MkRead $ Just . cast

readingAnInt32 : String -> Maybe Int32
readingAnInt32 = readMay3 {impl = readInt32}
```

Neat. Would Idris be able to pass `readInt32` automatically? Nope:

```
> readMay Int32 "foo"
Error: Can't find an implementation for Read Int32.
...
```

Function definitions are not to automatically added to the implicit
scope. In order to do so, we have to use the `%hint` pragma:

```idris
readGender : String -> Maybe Gender
readGender "Male"      = Just Male
readGender "Female"    = Just Female
readGender "NonBinary" = Just NonBinary
readGender _           = Nothing

%hint
readGenderImpl : Read Gender
readGenderImpl = MkRead readGender
```

And now, in the REPL:

```
> readMay Gender "Female"
Just Female
```

### Summary

This section might be quite daunting, but people typically get used
to this quickly, as there is *nothing more* to type signatures in Idris!

There are three kinds of arguments:

  * Explicit arguments, which will have to be provided manually
    by programmers.
  * Implicit arguments, which *can* be provided manually, but can
    typically be figured out by Idris through type inference.
  * Auto implicit arguments, which *can* be provided manually, but
    are otherwise constructed by Idris from the implicit scope,
    where - amongst other things - interface implementations reside.
    In order to add a toplevel function or value to the implicit
    scope, use the `%hint` pragma.

In addition, every function argument is of one of three possible
quantities:

  * `0` : The argument will provably never be used in the function
    implementation, and can therefore be erased at runtime.
  * `1` : The argument *must* be used exactly once. For the time being
    I won't burden you with the details what this exactly
    means and why it is useful.
  * Arbitrarily often : The default.

If in doubt, always have a look at the full type signatures of
functions by using `:ti` in the REPL.

As a final example, have a look at the follwing hole in the REPL:

```idris
readMayFinal : (0 a : Type) -> {auto impl : Read a} -> String -> Maybe a
readMayFinal a str = ?hole1
```

```
> :t hole1
   str : String
 0 a : Type
   impl : Read a
------------------------------
hole1 : Maybe a
```

You see, together with the type of `hole1`, Idris gives us the
types and quantities of all other values - implicit and explicit -
in scope. We can access and use these values if they are not of zero quantity
(even the implicit ones!). For instance, in the following truly final example,
we pattern match on an implicitly provided interface implementation:

```idris
readMayTrulyFinal : (0 a : Type) -> {auto impl : Read a} -> String -> Maybe a
readMayTrulyFinal a str = case impl of
  MkRead fun => fun str
```

## Generalized Algebraic Data Types

Now that we understand how type signatures work in Idris, let's start
and implement a bunch of interesting data types.

### More Flexibility in Data Definitions

In the first part of the tutorial, we learned how to define
new data types using the `data` and `record` keywords. We will
use records a lot, as described there, but for sum types we
will typically use a more powerful syntax except for the
most simple cases.

Below is again a definition of our binary tree data type, this
time with the extended syntax:

```idris
data BTree2 : (a : Type) -> Type where
  Leaf2 : BTree2 a
  Node2 :  (leftBranch : BTree2 a)
        -> (value : a)
        -> (rightBranch : BTree2 a)
        -> BTree2 a
```

This is sometimes referred to as the *GADT syntax* for defining data types,
as something similar is also available in Haskell after enabling
the `GADTs` extension (*GADT* being an acronym for *Generalized
Algebraic Data Types*). With the above declaration, we define
three (yes, three, not two!) new functions: `BTree2`, `Leaf2`, and `Node2`.
In Haskell `BTree2` is called a *type constructor*: A typelevel function
of kind `* -> *`. In Idris, there is no such thing as a *kind system*,
and we don't distinguish between functions that calculate types
and functions that calculated values (that's because in Idris, types
*are* values, or can be treated as such). The term *type constructor*
is still used from time to time, but the distinction is a rather
artificial one.

Before you go on, as a quick exercise, try to predict the full
type signatures for `BTree2`, `Leaf2` and `Node2`, and check your
answer in the REPL by using `:ti`.

The good thing with the above syntax is, that it allows us to
provide explicit types for all new functions created
(`BTree2`, `Leaf2`, and `Node2`), including the ability to explicitly
declare and name all arguments together with their quantities, if
we want or need to do so. It also makes the types of all entities involved
immediately clear. For instance, it can be hard to figure out the
kinds of all parameters in the following Haskell data definition:

```haskell
data Biff p f a b = MkBiff (p (f a) (f b))
```

Can you figure out the kinds of `p`, `f`, `a`, and `b` immediately?
I still find that to be tricky at times.
Not so, if we are more explicit about the types:

```idris
data Biff :  (p : Type -> Type -> Type)
          -> (f : Type -> Type)
          -> (a : Type)
          -> (b : Type)
          -> Type where
  MkBiff : (value : p (f a) (f b)) -> Biff p f a b

aBiff : Biff Either Maybe String Bits16
aBiff = MkBiff . Left $ Just "foo"
```

Since Haskellers themselves find it useful and at times necessary to
be explicit about the kinds of their type constructors, there is
the `KindSignatures` extension, allowing them to annotate their
code in a similar fashion.

### Well-Typed Expressions

While above we talked about readability, we will now talk about
necessity. In this section, we'd like to define a
data type `Expr` to represent a simple language of well typed
arithmetic and boolean expressions.
The `Expr` type constructor should take an additional argument
of type `Type`, to keep track of the type we get when we
evaluate an expression.
The following constructs should be part of our small
language:

  * Natural number literals.
  * Functions `Add` and `Mult` for arithmetic operations
    on natural numbers.
  * Function `IsZero`, operating on a natural number and
    returnning a `Bool`.
  * Function `And` and `Or`, calculating the logical conjunction
    and disjunction of two boolean expressions.

The expression language should be well typed: We must not be allowed
to write bogus expressions like `Add (IsZero 12) 13`, as the type
of `IsZero 13` should be `Expr Bool`, and `Add` is supposed to take
two arguments of `Expr Nat`. Here's how to do this:

```idris
data Expr : (t : Type) -> Type where
  NatLit : (value : Nat)    -> Expr Nat
  Add    : (lh : Expr Nat)  -> (rh : Expr Nat) -> Expr Nat
  Mult   : (lh : Expr Nat)  -> (rh : Expr Nat) -> Expr Nat
  IsZero : (val : Expr Nat) -> Expr Bool
  And    : (lh : Expr Bool) -> (rh : Expr Bool) -> Expr Bool
  Or     : (lh : Expr Bool) -> (rh : Expr Bool) -> Expr Bool

example1 : Expr Bool
example1 = IsZero (NatLit 10) `Or` IsZero (NatLit 0)

example2 : Expr Bool
example2 = IsZero (Mult (NatLit 1) (Add (NatLit 12) (NatLit 100)))
```

What's interesting about this example is, that we can learn something
about the type variable `t` by inspecting the data constructor being
used: If the constructor is `NatLit`, `Add`, or `Mult`, we - and Idris! - know,
that `t` must be `Nat`. Likewise, if the constructor is `IsZero`, `And`, or `Or`,
we - and Idris! - know, that it must be `Bool`.

But with this knowledge we can implement a well-typed and provably total
(that is terminating in a finite number of steps) evaluator for
such expressions:

```idris
eval : Expr t -> t
```

Before we actually implement `eval`, please take a moment to appreciate
what this means: If we succeed in implementing `eval`, we can pass it
a boolean expression and get a boolean in return, or we can pass
it a `Nat` expression and get a natural number in return.

The implementation of `eval` is almost trivial:

```idris
eval (NatLit v)   = v
eval (Add lh rh)  = eval lh + eval rh
eval (Mult lh rh) = eval lh * eval rh
eval (IsZero val) = eval val == 0
eval (And lh rh)  = eval lh && eval rh
eval (Or lh rh)   = eval lh || eval rh
```

And in the REPL:

```
> eval example1
True
> eval example2
False
```

For the sake of convenience, let's implemnt interface `Num` for `Expr Nat`.
This will allow us to use integer literals and operators `(+)`, and `(*)`
to write down arithmetic expressions more conveniently. In addition,
we specify the fixity of `And` and `Or`, to use them as nested
infix operators:

```idris
Num (Expr Nat) where
  fromInteger = NatLit . fromInteger
  (+) = Add
  (*) = Mult

infixr 5 `And`
infixr 4 `Or`

example3 : Expr Nat
example3 = 12 + 100 * 30

example4 : Expr Bool
example4 = IsZero (100 * 31) `Or` IsZero 0 `And` IsZero example3
```

And in the REPL:

```
> example3
Add (NatLit 12) (Mult (NatLit 100) (NatLit 30))
> eval example3
3012
> eval example4
False
```

With the declaration of `Expr`, we actually defined two new and
closely related types: `Expr Nat` and `Expr Bool`. We therefore
speak also of a *family of types*, or a *type family*, and we
say `Expr` is *indexed* over `Type` instead of *parameterized* over
`Type`. The difference between a type index and a type parameter
can be explained as follows: If we can learn something about the
type level argument by looking at the data constructor used,
we talk about an *index*, otherwise we talk about a *parameter*.

So, `Maybe` and `List` each take a parameter of type `Type`, while
`Either` takes two parameters of type `Type`. `Monad` takes a parameter
of type `Type -> Type`, but `Expr` takes an *index* of type `Type`.

Note: `Expr` could be implemented in Haskell almost verbatim as shown above
after enabling the `GADTs` extension.

### Vectors: Lists of a Fixed Length

We now give the "hello world" of dependetly typed programming:
Lists indexed over natural numbers, representing their length.
Although I just said *dependently typed*, this actually does not yet
involve full fledged dependent types. We could encode something
similar (but with less syntactic convenience) in Haskell after
enabling the following extensions: `GADTs`, `DataKinds`, and `KindSignatures`.

```idris
data Vect : (n : Nat) -> (a : Type) -> Type where
  Nil  : Vect Z a
  (::) : (h : a) -> (t : Vect n a) -> Vect (S n) a

vectOfLength2 : Vect 2 String
vectOfLength2 = [ "Hello", "World" ]
```

There is a lot of stuff going on here, so let's break this down a bit:
`Vect` is a function from `Nat` to `Type` to `Type`: We plan to use
the `Nat` index (not *parameter*!) to represent the number of elements
in the `Vect`, and the `Type` parameter (not *index*!) to represent
the types of values stored. So, this again is a *family of parameterized types*:
One parameterized type for each possible length.

This is reflected in the two constructors: `Nil` is an empty `Vect` and
therefore has length zero (`Z`), `(::)` (also called *cons*) takes a value
plus a vector of length `n`, and therefore represents a vector of
length `S n`, which means, that `n` is increased by one (have a look at
the data constructors of `Nat`: `:doc Nat`!).

Idris allows us to use convenient bracket syntax as shown above for
all data types having constructors named `Nil` and `(::)`. Remember,
Idris supports name overloading: The constructors of `List` are likewise
called `Nil` and `(::)`.

In addition, Idris prevents us from making stupid mistakes. The following
will not work at the REPL:

```
> the (Vect 2 Bits8) [1,2,3]
...
```

First, have a look at the full type and docstring of `the`,
and try to figure out what it
does and why it is extremly useful. Then, appreciate the complex error message
we get from running the expression above in the REPL. The issue here is that
Idris will have several constructors called `Nil` and `(::)` in scope, and
will try each of them to satisfy the types. None will work, as the length of
our vector is wrong, so Idris will explain for each constructor what it
tried and why id didn't work.

The following is fine, however, as the length matches the type:

```
> the (Vect 2 Bits8) [1,2]
[1, 2]
```

Now, let us implement some functions, which make use of this
new type level power:

```idris
head : Vect (S n) a -> a
head (h :: _) = h
```

Please remember, that we have `%default total` at the beginning of this
document, so Idris accepts the above definition as being provably total.
Also, see how easy it is to express in the type declaration, that we
only plan to return the `head` of non-empty vectors, and that therefore
there is no need to wrap the result in a `Maybe`.
The `Nil` case is impossible, since `Nil` has type `Vect Z a`, which
does not agree with the expected type of `head`'s argument. We can be
explicit about such impossible cases (this is sometimes necessary in order
to help Idris verify that we covered all cases). As shown in the next code
snippet, I'll insert explicit `impossible` cases most of the time in these
tutorials. Feel free to try out yourself, when they are actually necessary.

```idris
tail : Vect (S n) a -> Vect n a
tail (_ :: t) = t
tail Nil impossible
```

We can take this (much) further. Below are some more interesting functions:

```idris
(++) : Vect m a -> Vect n a -> Vect (m + n) a
Nil ++ v      = v
(h :: t) ++ v = h :: (t ++ v)

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith _ Nil Nil = Nil
zipWith f (h1 :: t1) (h2 :: t2) = f h1 h2 :: zipWith f t1 t2
zipWith _ Nil (_ :: _) impossible
zipWith _ (_ :: _) Nil impossible

Functor (Vect n) where
  map _ Nil      = Nil
  map f (h :: t) = f h :: map f t
```

Before you start thinking that we finally have a programming
language at our hands, which will take us to world dominion,
please be aware that things are not always so easy.
For instance, the following is surprisingly difficult to implement:

```idris
-- reverse : Vect n a -> Vect n a
-- reverse Nil      = Nil
-- reverse (h :: t) = reverse t ++ [ h ]
```

If you uncomment the above, Idris will complain that it can't figure
out that `plus n 1` is the same as `S n`. *We* know this to be true,
since we know the addition of natural numbers to be commutative.
However, Idris can't figure this out on its own, so it needs some help.
This is the moment, where we'd have to write our own proof, but we are not
ready for this yet. Still, if you are curious:
The proof is available from `Data.Nat.plusCommutative`,
and we can use that to implement `reverse`

```idris
reverse : Vect n a -> Vect n a
reverse Nil                = Nil
reverse {n = S k} (h :: t) = rewrite plusCommutative 1 k in reverse t ++ [ h ]
```

It is *not* expected that you understand the example above yet. It's just
there to show you that we can support Idris in verifying stuff for us
and that it is often necessary to do so.


### Isotopes: A Family of *Pure* and *Maybe Not So Pure*

In cheminformatics, when we describe molecules, we sometimes need to
distinguish between *elements* (meaning a natural mixture of isotopes)
and *just a single isotope* in case of an isotopically labelled compound.
In addition, when we are calculating extact molar masses, we always
talk about molecular formulae consisting of a set of specific isotopes
plus their number.

We therefore have (at least) three different entities (types), that are
closely related:

  * A natural mixture of isotopes, all of the same element. This corresponds
    to the `Element` type defined in the first part of the tutorial.
  * A single isotope of explicitly specified atomic number and mass number.
    These are, for instance, needed in order to talk about a specific 
    isotopologue of a molcule.
  * One or the other of the above, which is the default when describing
    a compound in SMILES or Mol format.

Since we already have `Element` for the first item in the list above,
we could just go for an `Isotope` data type for the second item,
and use `Either Element Isotope` for the third. While accurate, it would
require us to use two data constructors (instead of one) to wrap the
information stored in a pure `Isotope`. In addition, `Either` is a data type
with no additional semantics, which could or could not be an
issue later on.

Let us therefore go for a family of types, indexed over a flag describing
its purity.

```idris
||| In Idris, a *type alias* is just a function or constant returning
||| a `Type`. There is therefore no `type` keyword for type aliases as
||| in Haskell.
MassNumber : Type
MassNumber = Nat

||| Purity of an isotope: `Pure` means the isotope is provably
||| pure, and we can extract an `Element` and a `MassNumber` from
||| it. `MixOrPure` means, the isotope might come without an explicit
||| `MassNumber`, in which case it is to be interpreted as a natural
||| mixture of isotopes of the given element.
data Purity = Pure | MixOrPure

||| Perhaps surprisingly, the type of `Mix` is more specific than
||| the type of `Iso`.
data Isotope_ : (p : Purity) -> Type where
  Mix : Element -> Isotope_ MixOrPure
  Iso : Element -> MassNumber -> Isotope_ p

Isotope : Type
Isotope = Isotope_ MixOrPure

PureIsotope : Type
PureIsotope = Isotope_ Pure

element : Isotope_ p -> Element
element (Iso e _) = e
element (Mix e)   = e

massNr : PureIsotope -> MassNumber
massNr (Iso _ mn) = mn
massNr (Mix _) impossible

refine : Isotope_ p -> Maybe PureIsotope
refine (Mix _)    = Nothing
refine (Iso e mn) = Just $ Iso e mn 

||| A molecule (without information about its connectivity)
||| can be considere to be a mapping from isotopes (either pure or
||| a natural mixture) to natural numbers
Molecule : Type
Molecule = List (Isotope, Nat)

||| An isotopologue (without information about its connectivity)
||| can be considere to be a mapping from pure isotopes
||| to natural numbers.
Isotopologue : Type
Isotopologue = List (PureIsotope, Nat)
```

## Exercises

Solutions available [here](Tut2/Sol.idr).

### 1. Enhanced Expressions

Enhance our `Expr` type with string literals of type `Expr String`
and a constructor `Len`, which calculates the length of a string
and returns a natural number. Adjust the implementation of `eval`
accordingly and implement interface `FromString` for `Expr String`.

### 2. More Functions on Vect

Implement the following functions for `Vect`.

```idris
drop2 : Vect (S $ S n) a -> Vect n a

drop : (n : Nat) -> Vect (n + m) a -> Vect m a

take : (n : Nat) -> Vect (n + m) a -> Vect n a

replicate : (n : Nat) -> (v : a) -> Vect n a

||| This should iteratively apply `f` to the initial argument.
||| For instance:
|||
||| `iterate 6 (*2) 1` should return
||| `[1, 2, 4, 8, 16, 32]`
iterate : (n : Nat) -> (f : a -> a) -> (ini : a) -> Vect n a
```

Try them out in the REPL!

### 3. DNA and RNA

Come up with a type family for representing nucleobases, indexed
over a suitable data type. The family should include all
five nucleobases: adenine (A), cytosine (C), guanine (G), thymine (T), and uracil (U),
but should make it possible to represent strands of RNA and DNA
in a type safe manner. For instance, using uracil in a DNA strand should
be a type error.

In addition, implement algorithms for transcribing DNA to RNA and calculate
complementary sequences of DNA and write a function
`readDNA`, which tries to read a DNA sequence from a string of
one-letter codes.

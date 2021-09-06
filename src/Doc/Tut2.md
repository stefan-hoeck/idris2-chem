# Part 2: Type Families

What we have seen in the [first part of the tutorial](Tut1.md)
is just plain functional programming very much in the style
of Haskell. We are now ready to start talking about types
in earnest. Fasten your seat belt.

```idris
module Doc.Tut2

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
of extension in Idris here, and will often make use of this.

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
of the fully qualified name. For instance:

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
we use. Lets opt for `Integer`:

```
> either {b = Integer} String.length cast $ Left "foo"
3
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
Quantity `0` means "not at all", and it is a type error to
use it (for instance by pattern matching on it or passing it
as a non-zero quantity argument to another function). This is
really great, because it allows Idris to erase all values of
quantity `0` at runtime, as they are provably never ever used.
Quantity `1` means "exactly once", and this is the most difficult
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
The answer - and that's a huge difference from Haskell - is "yes"!
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

This section might seem very daunting, but people typically get used
to this quickly, as there is *nothing more* to type signatures in Idris!

There are three kinds of arguments:

  * Explicit arguments, which will only have to be provided manually
    by programmers
  * Implicit arguments, which *can* be provided manually, but can
    typically be figured out by Idris through type inferences
  * Auto implicit arguments, which *can* be provided manually, but
    are otherwise constructed by Idris from the implicit scope,
    where - amongst other things - interface implementations reside.

In addition, ever function argument is of one of three possible
quantities:

  * `0` : The argument will provably never be used in the function
    implementation, and can therefore be erased at runtime
  * `1` : The argument *must* be used exactly once. For the time being
    I'll won't burden you with the details what this exactly
    means and why it is useful
  * Arbitrarily often : The default, meaning "I don't know" or "I don't care"

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
in scope.

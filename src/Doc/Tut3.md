# Part 3: Types as Propositions, Values as Proofs

We got our hands dirty with type familes, and they already allowed
us to write expressive and exact types. What more could we wish for?
The answer is: Type refinements!
We sometimes want to operate only on a subset of the possible
values of a given type, and we'd lake Idris to do two things for us:
Preventing us from passing values not in the desired subset at runtime *and*
compile time, and filling in proofs that our values actually belong to
the desired subsets automatically.

In this section we will learn the following: We can use *types* to
define predicates on other types, and *values* as proofs that our
predicates actually hold.

```idris
module Doc.Tut3

import Doc.Tut2.Sol

%default total
```

## A Predicate for Non-Empty Lists

Assume we'd like to implement `head` for `List`s, but instead of wrapping
the potential result in a `Maybe`, we actually want to accept only non-empty
lists as arguments. There are several ways to deal with this: Using a `Vect (S n) a`
as shown in the previous part is one of them. Defining an explicit data type
for non-empty lists is another one. Such a data type is available from module
`Data.List1` from base.

More interesting, however, is to refine our list type itself by defining
a *predicate* for it. This is extremly useful, as it can be extended to
lots of other predicates on types. Want to make sure that two lists
are of the same length? Define a predicate (we'll do that later in this
part of the tutorial). Want to make sure a list is of at least a
given length, so that we can use a natural number to safely access
an element at a given index? Write a predicate. Want to make sure,
that a value of type `Bits8` is within a given limited range? Write
a predicate. These examples should be enough to tickle your curiosity,
so let's get started.

Typically, a *predicate* for a given type `t` is a new data type, indexed
over `t`, the constructors of which only target a subset of possible
values of `t`. For instance, a predicate (sometimes also called a *view*) for
non-empty lists would look as follows:

```idris
data NonEmpty : (values : List a) -> Type where
  ItIsNonEmpty : NonEmpty (h :: t)
```

Please note, that there is no constructor for `NonEmpty` with an empty
list index. There is an interface to express this: `Uninhabited`.
An implementation of `Uninhabited ty` is a proof, that there can not be a
value of type `ty`:

```idris
Uninhabited (NonEmpty Nil) where
  uninhabited _ impossible
```

We will see use cases for `Uninhabited` later on.

Let us now use `NonEmpty` to implement a provably total version of `head`
for non-empty lists:

```idris
head1 : (xs : List a) -> (prf : NonEmpty xs) -> a
head1 (h :: _) _ = h
head1 Nil      _ impossible
```

Note, how we gave our list argument a name (`xs`) in the type declaration,
and how we referenced that name in the type of `prf`. So our function
takes a list of values named `xs`, plus a value of type `NonEmpty xs`
as a proof that `xs` is actually non-empty. From this proof, Idris
can figure out that the second pattern match is indeed `impossible`
(by inspecting the available constructors of `NonEmpty` plus their
types) and accepts our implementation of `head1` to be indeed total.

Let's try this at the REPL:

```
> head1 [1,2] ItIsNonEmpty
1
> head1 [] ItIsNonEmpty
Error: When unifying NonEmpty (?h :: ?t) and NonEmpty [].
...
```

It works! However, as can be seen above, we do not actually
do anything with `prf`. It should
therefore be possible to erase it at runtime:

```idris
head2 : (xs : List a) -> (0 prf : NonEmpty xs) -> a
head2 (h :: _) _ = h
head2 Nil      _ impossible
```

That's better!
Assume now that we read a list of values from the command line
and want to return the first value of that list. We can no longer
come up with a `NonEmpty` at compile time, since we know nothing
about what our users will input in advance, so what shall we do?
We write a generator function for `NonEmpty`!

```idris
nonEmpty : (xs : List a) -> Maybe (NonEmpty xs)
nonEmpty Nil         = Nothing
nonEmpty xs@(_ :: _) = Just ItIsNonEmpty

headMay2 : List a -> Maybe a
headMay2 xs = (\prf => head2 xs prf) <$> nonEmpty xs
```

We got pretty far already. We have a type-level guarantee that we call
`head2` only on non-empty lists, and we have the ability to come up
with a proof of non-emptiness at runtime. Still, `head2` is not *that*
convenient to use as at compile time and in the REPL: We have to
pass around the proofs of non-emptiness manually. Enter auto-implicits:

```idris
head : (xs : List a) -> {auto 0 prf : NonEmpty xs} -> a
head (h :: _) = h
head Nil impossible

headMay : List a -> Maybe a
headMay xs = (\_ => head xs) <$> nonEmpty xs
```

Data constructors are automatically added to the implicit scope (!), so
Idris2 can come up with a proof of non-emptiness at compile time on its
own. We can try this at the REPL:

```
> head [1,2,3,4]
1
```

Now we have all the required ingredients together: Use indexed data types
to refine existing types and require them as erased auto implicit arguments
to get both: Strong guarantees at runtime and convenient syntax at
compile time.

## Matching Implicits and Zipping Lists

The implementation of `zipWith` for `List`s provided by Idris will
silently drop the remainder of the longer list, which is sometimes
the desired behavior. More often, however, I consider it to be a bug
if the two lists I try to zip are not of equal length. Let's declare
a refined version of `zipWith` in the spirit of the one we wrote
for `Vect`, where we accept only lists of equal length.

First, we need a predicate for a pair of lists of equal length.
This will have to be a data type indexed over two list
arguments. Here is its definition plus a generator function:

```idris
data SameLength : (as : List a) -> (bs : List b) -> Type where
  SLNil  : SameLength Nil Nil
  SLCons : SameLength as bs -> SameLength (a :: as) (b :: bs)

sameLength : (as : List a) -> (bs : List b) -> Maybe (SameLength as bs)
sameLength Nil        Nil        = Just SLNil
sameLength (ha :: ta) (hb :: tb) = SLCons <$> sameLength ta tb
sameLength _          _          = Nothing
```

Take a moment to figure out what the definition of `SameLength` tells
us: Two lists are of equal length, if they either are both empty,
or if we cons single values onto two lists of equal length. Note also
that the two lists not necessarily store values of the same
types. This is important, since when we zip two lists, they are also
typically not holding values of the same types.

Implementing `zipWithSL` is now straight forward. Or is it?
Our first try might look as the one commented out below. However,
this won't compile. Idris can't find a value of type
`SameLength ta tb` in the recursive case.

```idris
-- zipWithSL :  (f : a -> b -> c)
--           -> (as : List a)
--           -> (bs : List b)
--           -> {auto 0 prf : SameLength as bs}
--           -> List c
-- zipWithSL _ Nil        Nil        = Nil
-- zipWithSL f (ha :: ta) (hb :: tb) = f ha hb :: zipWithSL f ta tb
-- zipWithSL _ Nil (_ :: _) impossible
-- zipWithSL _ (_ :: _) Nil impossible
```

I could just show you the solution for this, but we will do
this in several steps to learn something about type-driven
development in Idris. It is best to follow along with
your own version of the code. In order to keep Idris happy
and still being able to typecheck this file
I'll append numbers to the function names in
the different steps shown below.

First, we should experiment with inserting some holes. Auto search
couldn't find the required `prf` in the recursive step, so we
start there by explicitly passing a hole. In order to unclutter
the code, I'll drop the `impossible` cases: Idris is happy without
them.

```idris
zipWithSL1 :  (f : a -> b -> c)
           -> (as : List a)
           -> (bs : List b)
           -> {auto 0 prf : SameLength as bs}
           -> List c
zipWithSL1 _ Nil        Nil        = Nil
zipWithSL1 f (ha :: ta) (hb :: tb) =
  f ha hb :: zipWithSL1 f ta tb {prf = ?recPrf}
```

This typechecks, and Idris will give the following information
about `recPrf` and its context in the REPL:

```
> :t recPrf
 0 c : Type
 0 b : Type
 0 a : Type
   ha : a
   ta : List a
   hb : b
   tb : List b
 0 prf : SameLength (ha :: ta) (hb :: tb)
   f : a -> b -> c
------------------------------
recPrf : SameLength ta tb
```

So, we need to somehow convey to Idris that `ta` and `tb`
are of the same length. We already have a value of type
`SameLength (ha :: ta) (hb :: tb)`, so we seem to be
pretty close. You might already have figured out what to do,
but I'd like to check one more hole:

```idris
zipWithSL2 :  (f : a -> b -> c)
           -> (as : List a)
           -> (bs : List b)
           -> {auto 0 prf : SameLength as bs}
           -> List c
zipWithSL2 _ Nil        Nil        = Nil
zipWithSL2 f (ha :: ta) (hb :: tb) =
  f ha hb :: zipWithSL2 f ta tb {prf = ?adjPrf prf}
```

Here, we check what the type of a hypothetical function
`adjPrf` would be, if it could convert the existing
`prf` value to a value of the expected type in the
recursive call. Let's inspect its type:

```
> :t adjPrf
 0 c : Type
 0 b : Type
 0 a : Type
   ha : a
   ta : List a
   hb : b
   tb : List b
 0 prf : SameLength (ha :: ta) (hb :: tb)
   f : a -> b -> c
------------------------------
adjPrf : SameLength (ha :: ta) (hb :: tb) -> SameLength ta tb
```

OK, from the type of `adjPrf` we learn, that we need to
extract the proof of same length for the tails of the lists
only. But, looking at the data constructors of `SameLength`,
this should be trivially possible, as a value of type
`SameLength (ha :: ta) (hb :: tb)` was by definition
constructed with the `SLCons` constructor.

```idris
unconsSL : SameLength (a :: as) (b :: bs) -> SameLength as bs
```

Now, the above type reads like a mathematical proposition:
"If two non-empty lists are of the same length, then their
tails must be of the same length". We can now *proof* this
proposition by implementing this function while satisfying
the totality checker:

```idris
unconsSL (SLCons sl) = sl
unconsSL SLNil impossible
```

We can use this *proof* to help the typechecker
and are now able to finish the implementation of `zipWithSL`:

```idris
zipWithSL3 :  (f : a -> b -> c)
           -> (as : List a)
           -> (bs : List b)
           -> {auto 0 prf : SameLength as bs}
           -> List c
zipWithSL3 _ Nil        Nil        = Nil
zipWithSL3 f (ha :: ta) (hb :: tb) =
  f ha hb :: zipWithSL3 f ta tb {prf = unconsSL prf}
```

Before we leave this section, I'll show you one last
technique we could have used in the implementation of `zipWithSL`.
The only thing `unconsSL` does, is performing a pattern match
in order to extract the smaller part of the proof.
It is possible to this in the implementation of `zipWithSL` directly,
that is, it is possible to pattern match on named implicit
arguments:

```idris
zipWithSL :  (f : a -> b -> c)
          -> (as : List a)
          -> (bs : List b)
          -> {auto 0 prf : SameLength as bs}
          -> List c
zipWithSL _ Nil        Nil                          = Nil
zipWithSL f (ha :: ta) (hb :: tb) {prf = SLCons sl} =
  f ha hb :: zipWithSL f ta tb
```

There is no longer a need to pass on the smaller proof
explicitly in the recursive call, as all local variables are
automatically part of the implicit scope.
"But wait!", you'll say, "Didn't you say we were not allowed
to pattern match on erased arguments?". I'm glad you rememberd :-).
Strictly speaking, we are not pattern matching on `prf` here,
but on the argument lists `as` and `bs`. From their structure
the structure of `prf` follows immediately, therefore we
are allowed to deconstruct it here.

Let's try `zipWithSL` at the REPL:

```
> zipWithSL3 (+) [1,2,3] [4,5,6]
[5, 7, 9]
> zipWithSL3 (+) [1,2,3] [4,5,6,7]
Error: Can't find an implementation for SameLength [1, 2, 3] [4, 5, 6, 7]
...
```

## Being Just

In Haskell, there is a partial function called `fromJust` defined
in `Data.Maybe`, which extracts a value from a `Maybe` throwing
an exception in case of a `Nothing`.
We'd like to implement in Idris a provably total function, which
allows us to do the same. After what we learned above this should
be straight forward, so, as an exercise, try and come up with a
solution of your own before looking at the code below.

And here's my own version of this:

```idris
data IsJust : (m : Maybe a) -> Type where
  IsIsJust : IsJust (Just v)

fromJust : (m : Maybe a) -> {auto 0 prf : IsJust m} -> a
fromJust (Just v) = v
fromJust Nothing impossible
```

This is actually available from module `Data.Maybe` in the base
library. However, what's the use of this? Let me show you.

Remember the DNA sequences we implemented in [the second part
of the tutorial](Tut2.md)? We implemented `readDNA`
of type `String -> Maybe DNASeq`. However, we sometimes
want to define DNA sequences at compile time and doing so
via list syntax can become cumbersome quickly:

```idris
aDNASeq : DNASeq
aDNASeq = [C,G,A,T,T,C,G,A]
```

It would be much more convenient, if we could use the string literal
`"CGATTCGA"` in the example above. In order to be able to use
string literals to construct a data type, we either need to implement
interface `FromString`, or we need to implement a function called
`fromString`. When we are dealing with a partial function -
as is the case here: not all strings represent valid sequences of DNA -
we go for the latter.

```idris
fromString : (s : String) -> {auto 0 prf : IsJust (readDNA s)} -> DNASeq
fromString s = fromJust $ readDNA s

anotherDNASeq : DNASeq
anotherDNASeq = "CAGGTTTCCGACC"
```

This is really cool, but does it scale?
The answer is: Well enough for many use cases. If
I increase the length of the string in `anotherDNASeq` to
1000 characters, Idris takes about a minute to typecheck
the file on my machine. There is, however, work in progress
to make these typelevel calculations a lot faster.

## Exercises

It may take some time to solve all the exercises below. Just
take it slow and do them one at a time. Make sure to use of holes
and let Idris help you if you get stuck.
Solutions available [here](Tut3/Sol.idr).

### 1. RNA from String Literals

Implement a function `readRNA` and provide an implementation
of `fromString` as we did for DNA above. At first, try to come up
with a solution without looking at the code above.
Use the REPL to experiment with this and make sure, that no
invalid strings are accepted.

### 2. Zipping Vectors of Different Lengths

Sometimes we'd like to zip two vectors of unknown origin, so we
can't use `zipWith` directly. Write a predicate as a witness that
two vectors are actually of the same length, and use this to
implement `zipWithSLV`.

Make sure to look at the solution afterwards, as it explains several
ways to do this.

### 3. Safe Indexing into Lists

We'd like to access the n-th element of a list in a safe manner.
A total implementation of such a function in Haskell might be similar
to the following Idris code:

```idris
atMaybe : Nat -> List a -> Maybe a
atMaybe _     Nil      = Nothing
atMaybe Z     (h :: _) = Just h
atMaybe (S k) (_ :: t) = atMaybe k t
```

Write a predicate witnessing that a natural number is a valid
index into a given list. Use this to implement function `at`
in the spirit of `atMaybe` but without having to wrap the
result in a `Maybe`.

### 4. Predecessor of a Natural Number

We'd like to safely calculate the predecessor of a non-zero
natural number. Come up with a suitable predicate and implement
function `safePred` in the spirit of what we done so far in
this part of the tutorial.

### 5. Division by 2

Write a predicate witnessing that a natural number is even
and implement a function for safely dividing such a number by two.
In addition, declare a function proposing that the sum of two
even numbers is an even number. Proof this proposition by
implementing the function.

### 6. Remainder of Division by 2

Write two predicates on natural numbers: The first witnessing that
a natural number is odd, the second witnessing that a natural
number equals 1. Next, implement a function calculating the
remainder of a natural number when dividing it by 2.
Finally, declare a type proposing that the remainder of calculating
an odd number by 2 equals 1.
Implement this function as a proof that the proposition holds.

### 7. Assoc List

An assoc list is a list of key value pairs:

```idris
AssocList : (k : Type) -> (v : Type) -> Type
AssocList = List (k,v)
```

Define a predicate witnessing that a given key is in an
assoc list, and implement function `lookup` for extracting
the value at that position.

Note: In this case, the predicate can't be erased at runtime,
as we need it to figure out, where in the list the key is
located. Also, do not use interface `Eq` or something similar
in your implementation.

### 8. Assoc Vect

Same as exercise 7 but use a `Vect` instead of a list. Implement
function `delete`, where the value associated with
a given key should be removed.
The types of the function should reflect that the resulting `Vect`
is one element shorter.

### 9. Head of Concatenated Lists

Below is an implementation of list concatenation function
(we do not use `concatenate` defined on `Foldable`, as it won't
properly reduce a compile time):

```idris
conc : List (List a) -> List a
conc []        = []
conc (x :: xs) = x ++ conc xs
```

Define a predicate witnessing that a list of lists holds
at least one non-empty list. Proof (by writing a proposition
and implementing it) that concatenating a list of lists using `conc`
where at least one list is non-empty results in a non-empty list.
Finally, implement a function `headOfMany` taking a list of lists
of which at least one is non-empty and returning the head of
the concatenated result. Important: Make use of the proposition
you proved above and implement `headOfMany` by invoking a
`head` function like the one defined in this tutorial.

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
so lets get started.

Typically, a *predicate* for a given type `t` is a new data type, indexed
over `t`, the constructors of which only target as subset of possible
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
as a proof that `xs` is actually non-empty.

Let's try this at the REPL:

```
> head1 [1,2] ItIsNonEmpty
1
> head1 [] ItIsNonEmpty
Error: When unifying NonEmpty (?h :: ?t) and NonEmpty [].
...
```

As can be seen above, we do not actually do anything with `prf`. It should
therefore be possible to erase it at runtime:

```idris
head2 : (xs : List a) -> (0 prf : NonEmpty xs) -> a
head2 (h :: _) _ = h
head2 Nil      _ impossible
```

Assume now that we read a list of values from the command line
and want to return the first value of that list. We can no longer
come up with a `NonEmpty` at compile time, so what shall we do?
We write a generator function for `NonEmpty`:

```idris
nonEmpty : (xs : List a) -> Maybe (NonEmpty xs)
nonEmpty Nil         = Nothing
nonEmpty xs@(_ :: _) = Just ItIsNonEmpty

headMay2 : List a -> Maybe a
headMay2 xs = (\prf => head2 xs prf) <$> nonEmpty xs
```

We got pretty far, already. We have a type-level guarantee that we call
`head2` only on a non-empty list, and we have the ability to come up
with a proof of non-emptyness at runtime. Still, `head2` is not *that*
convenient to use. Enter auto implicits:

```idris
head : (xs : List a) -> {auto 0 prf : NonEmpty xs} -> a
head (h :: _) = h
head Nil impossible

headMay : List a -> Maybe a
headMay xs = (\_ => head xs) <$> nonEmpty xs
```

Data constructors are automatically added to the implicit scope (!), so
Idris2 can come up with a proof of non-emptyness at compile time on its
own.

```
> head [1,2,3,4]
1
```

Now, we have all the required ingredients together: Use indexed data types
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

Implementing `zipWithSL` is now straight forward, or is it?
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
your own version of the code. In order to keep Idris happy,
and still being able to typecheck this file,
I'll number the different steps shown below.

First, we should experiment with inserting some holes. Auto search
couldn't find the required `prf` in the recursive step, so we
start there:

```idris
zipWithSL1 :  (f : a -> b -> c)
           -> (as : List a)
           -> (bs : List b)
           -> {auto 0 prf : SameLength as bs}
           -> List c
zipWithSL1 _ Nil        Nil        = Nil
zipWithSL1 f (ha :: ta) (hb :: tb) =
  f ha hb :: zipWithSL1 f ta tb {prf = ?recPrf}
zipWithSL1 _ Nil (_ :: _) impossible
zipWithSL1 _ (_ :: _) Nil impossible
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
zipWithSL2 _ Nil (_ :: _) impossible
zipWithSL2 _ (_ :: _) Nil impossible
```

Here, we check, what the type of a hypothetical function
`adjPrf` would be, if it could convert the existing
`prf` value to a value of the expected type in the
recursive call. Let's check its type:

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
zipWithSL3 _ Nil (_ :: _) impossible
zipWithSL3 _ (_ :: _) Nil impossible
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
zipWithSL _ Nil (_ :: _) impossible
zipWithSL _ (_ :: _) Nil impossible
```

Here, there is no longer a need to pass on the smaller proof
explicitly in the recursive call, as all local variables are
automatically part of the implicit scope.
*But wait!*, you'll say, *didn't you say we were not allowed
to pattern match on erased arguments?*. I'm glad, you rememberd :-).
Strictly speaking, we are not pattern matching on `prf` here,
but on the argument lists `as` and `bs`. From their structure
the structure of `prf` follows immediately, therefore we
are safe to deconstruct it here.

Let's try `zipWithSL` at the REPL:

```
> zipWithSL3 (+) [1,2,3] [4,5,6]
[5, 7, 9]
> zipWithSL3 (+) [1,2,3] [4,5,6,7]
Error: Can't find an implementation for SameLength [1, 2, 3] [4, 5, 6, 7]
...
```

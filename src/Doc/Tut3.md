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

Data constructors are automatically added to the implicit scope, so
Idris2 can come up with a proof of non-emptyness at compile time on its
own.

```
> head [1,2,3,4]
1
```

Now, we have all the required ingredients together: Use indexed data types
to refine existing types and require them as erased auto implicit arguments
to get strong guarantees both a runtime and convenient syntax at compile time.

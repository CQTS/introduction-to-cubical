```
module 1--Type-Theory.1-2--Inductive-Types where
```

# Lecture 1-2: Inductive Types

<!--
```
open import Library.Prelude
```
-->

In the last lecture, we saw some abstract type theory. In this
lecture, we'll get to define our own concrete data types.


## The Booleans

A data type, also known as an inductive type, is a type whose elements
are built up out of "constructors". Here is the data type of Booleans:

```
data Bool : Type where
  true  : Bool
  false : Bool
```

This definition says, intuitively, that to construct a Boolean we
either construct it out of ``true`` or out of ``false`` ---
that is, a Boolean is either ``true`` or ``false``.

What makes a data type "inductive" is its "induction principle": to
define a function out of an inductive type, it suffices to define the
behavior of the function on all the constructors. For example, we may
define the logical ``not`` by saying what it does to
``true`` and to ``false``:

```
not : Bool → Bool
not true = false
not false = true
```

Induction may seem like an odd name if you are used to "proof by
induction" from your discrete math course, but we will see below that
the induction principle for ``ℕ`` is basically the mathematical
induction you are used to.

The method of writing functions where we describe what they do on
particular forms of their input is called "pattern matching", we
already saw an example of this when writing functions with pair types
as arguments. Agda has nice support for working with pattern matching
--- it can automatically write out all cases you need to cover to
define a function out of an inductive data type. This is called doing
a "case split". To have Agda do this for you, place your cursor in a
hole and press `C-c C-c`. You will be prompted for the list of
variables separated by spaces that you want to apply case-splitting to.

Try this below: press `C-c C-c` in the hole for ``and`` below and
enter `x y`, to have Agda split this definition into all the cases you
need to handle. (Recall that the logical "and" of two Booleans `x` and `y` is
``true`` exactly when both `x` and `y` are ``true`` and
``false`` otherwise.)

```
_and_ : Bool → Bool → Bool
-- Exercise:
x and y = {!!}
```

You don't have to split on all variables at once. Give a definition of
the logical "or" by case splitting only on the variable `x`. (Recall
that the logical "or" of two Booleans `x` and `y` is ``true`` if
either of `x` or `y` are ``true`` and ``false`` if they are
both ``false``.)

```
_or_ : Bool → Bool → Bool
-- Exercise:
x or y = {!!}
```

Here is the definition of logical implication. There is a strange
feature of this definition which has a fancy Latin name: "ex falso
quodlibet" --- ``false`` implies anything. Over the course of
this and the next lecture, we'll see why this is a useful principle to
take, even if it seems unintuitive.

```
_implies_ : Bool → Bool → Bool
true implies true  = true
true implies false = false
false implies _    = true
```

Here we use a "wildcard" (the underscore "_") to say that the
definition we are given is valid for anything we put in that spot, so
we don't bother giving the variable a name at all.

In general, inductive data types are characterized by their "induction
principles". In this lecture we will start by focusing on a simpler
version of this principle, "recursion", and will return to induction
in a later lecture.

The recursion principle for a type packs together the data that is
necessary to produce a non-dependent function out of it. To construct
a function `Bool → A`, we just need two elements of `A` to serve as
the images of ``true`` and ``false``. We can write out the
recursion principle for ``Bool`` as follows:

```
Bool-rec : {A : Type}
         → A
         → A
         → (Bool → A)
Bool-rec a1 a2 true = a1
Bool-rec a1 a2 false = a2
```

The ``Bool`` type is so simple that the name "recursion" feels
inappropriate: the principle doesn't actually do a recursive call of
any kind! The name will make more sense when we get to ``ℕ``.

The recursion principle for Booleans is known under a more familiar
name: the "if-then-else" pattern familiar from almost every
programming language:

```
if_then_else_ : {A : Type}
              → Bool
              → A
              → A
              → A
if b then a1 else a2 = Bool-rec a1 a2 b
```

::: Aside:
As in the definition of composition `f ∘ g`, we are using underscores
to tell Agda where the function arguments go. Writing the application
`if b then a1 else a2` is considered by Agda precisely the same as
`if_then_else_ b a1 a2`. (We won't use this kind of "mixfix" notation
much.)
:::

We won't usually need ot use the recursion principle ``Bool-rec``
by name: instead, we can just do a pattern match on an argument of
type ``Bool`` ourselves as we did above for the Boolean
operations ``not``, ``and``, and so on. But, for some
practice, try using `Bool-rec`{.Adga} to re-implement these:

```
not-fromRec : Bool → Bool
-- Exercise: (Don't pattern match on `x`!)
not-fromRec x = {!!}

-- You will need to use `Bool-rec` twice!
or-fromRec : Bool → Bool → Bool
-- Exercise: (Don't pattern match on either `x` or `y`!)
or-fromRec x y = {!!}
```

There is nothing special about ``Bool`` having two constructors
here, we can equally well define a type for the days of the week:

```
data Day : Type where
  monday    : Day
  tuesday   : Day
  wednesday : Day
  thursday  : Day
  friday    : Day
  saturday  : Day
  sunday    : Day
```

And then define functions out of it by providing cases for each of the
constructors:

```
isWeekend : Day → Bool
isWeekend monday    = false
isWeekend tuesday   = false
isWeekend wednesday = false
isWeekend thursday  = false
isWeekend friday    = false
isWeekend saturday  = true
isWeekend sunday    = true

nextDay : Day → Day
-- Exercise:
nextDay c = {!!}
```


## The Unit Type

``Bool`` is a simple data type, but it isn't the simplest. We can
use even fewer constructors. With one constructor, we have the unit
type ``⊤``, with its unique element ``tt``:

```
data ⊤ : Type where
  tt : ⊤
```

To define a function `⊤ → A`, we just have to say what it does on the
constructor ``tt``. This is so simple that it is difficult to
come up with interesting examples.

```
pick-true : ⊤ → Bool
pick-true tt = true
```

This idea can be packaged up into another recursion principle, which
says that to define a function `⊤ → A`, it suffices to give an element
`a : A` (which is to be the image of the unique element ``tt``).

```
⊤-rec : {A : Type}
      → (a : A)
      → (⊤ → A)
⊤-rec a tt = a
```

There is a sense in which ``⊤`` contains no information, so that
pairing it with another type gives back that type again. We can read
the following two execises as showing that "one times `A` equals `A`".

```
⊤×-to : (A : Type) → ⊤ × A → A
-- Exercise:
⊤×-to A x = {!!}

⊤×-fro : (A : Type) → A → ⊤ × A
-- Exercise:
⊤×-fro A a = {!!}
```


## The Natural Numbers

Enough with the simple data types, let's do some mathematics. We can
define the natural numbers as an inductive data type. There is a
constructor `zero : ℕ`, saying that zero is a natural number, and a
constructor `suc : ℕ → ℕ`, which says that if `n` is already a natural
number then `suc n` (the "successor" of `n`, i.e. `1 + n`) is also a
natural number.

We actually defined ``ℕ`` behind the scenes so that we could use
it in the previous lecture. Its definition, copy-pasted, is:

```
-- data ℕ : Type where
--   zero : ℕ
--   suc  : ℕ → ℕ
```

(But we leave it commented out, so that Agda doesn't complain about
defining a new type with the same name as an existing one.)

Defining functions out of ``ℕ`` is similar to defining functions
out of ``Bool``, we just have to give cases for the two
constructors. The difference is that the ``suc`` constructor
tells us which (other) natural number the provided argument is the
successor of.

Here's a first example:

```
isZero : ℕ → Bool
isZero zero = true
isZero (suc n) = false
```

So, ``isZero`` is ``true`` for zero, and ``false`` for
any successor. In this case, we didn't need to use the variable `n`,
but to do anything interesting we will. For example:

```
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
```

Thinking mathematically, $2 × 0 = 0$, covering the first case. For the
second case, $2 × (1 + n) = 2 + (2 × n)$. To achieve the $2 +$ part,
we use ``suc`` twice, and to achieve the $2 × n$ part, we use the
``double`` function we are currently defining!

Agda allows this kind of recursion so long as it is convinced that the
argument that you provide to the recursive call is smaller than the
argument that you started with. That is certainly the case here,
because we go from `suc n` to just `n`.

We can even do what is called "mutual" recursion, where two
definitions depend on each other to make sense. Here is a definition
of the proposition that a number is even, defined together with the
proposition that a number is odd:

```
isEven : ℕ → Bool
isOdd  : ℕ → Bool

isEven zero = true
isEven (suc n) = isOdd n

isOdd zero = false
isOdd (suc n) = isEven n
```

Using pattern matching, we can define the arithmetic operations on
numbers:

```
_+ℕ_ : ℕ → ℕ → ℕ
zero    +ℕ m = m
(suc n) +ℕ m = suc (n +ℕ m)
```

Remember that you can test any piece of code by typing "C-c C-n" and
then `2 +ℕ 3`, say.

Here we have chosen to split into cases on the left side and leave the
right side alont, but we could equally well split into cases on the
right instead:

```
_+ℕ'_ : ℕ → ℕ → ℕ
n +ℕ' zero = n
n +ℕ' (suc m) = suc (n +ℕ m)
```

We will be able to show that these two versions are equal as
functions, but Agda doesn't consider them *exactly* the same.

Try some other ordinary operations on natural numbers. To figure these
out, calculate what the answer should be mathematically, $(1 + n) × m
= m + (n × m)$ for example, and then turn those equations into
definitions.

```
-- Multiplication
_·ℕ_ : ℕ → ℕ → ℕ
-- Exercise:
n ·ℕ m = {!!}

-- Exponentiation
_^ℕ_ : ℕ → ℕ → ℕ
-- Exercise:
n ^ℕ m = {!!}
```

Make sure to test these using `C-c C-n`!

We can also define a "predecessor" operation, which partially undoes
the successor `suc : ℕ → ℕ`. Of course, it can't fully undo it, since
``zero`` has nowhere to go except ``zero`` again.

```
predℕ : ℕ → ℕ
-- Exercise:
predℕ n = {!!}
```

Finally, we can package the recursion principle up into a function
function, making clear that the pattern matching we've been doing is
the usual definition of a function by recursion:

```
ℕ-rec : {A : Type}
      → A                 -- The base casea
      → (A → A)           -- The recursion law
      → (ℕ → A)
ℕ-rec a r zero = a
ℕ-rec a r (suc n) = r (ℕ-rec a r n)
```

So: we have a base case `a`, which is used for `zero`, and a recursive
case, which is used for `suc n` and handed the result for `n`.

Try re-implementing ``double`` using ``ℕ-rec``:

```
double' : ℕ → ℕ
-- Exercise:
double' = ℕ-rec {!!} {!!}
```

When pattern matching, in the ``suc`` case we are allowed access
to access to the previous `n`: without this, functions like
``predℕ`` are a bit irritating to write. We can define an
improved version of ``ℕ-rec`` that provides access to this `n`.
For an extra challenge, try defineing this only in terms of
``ℕ-rec``!

```
ℕ-rec' : {A : Type}
      → A                 -- The base case
      → (ℕ → A → A)       -- The recursion law
      → (ℕ → A)
-- Exercise:
ℕ-rec' a r n = {!!}
```


## Lists

If this were a course on functional programming, we would spend a lot
more time with lists. This isn't a course on functional programming,
but it's worth seeing a smidge of list-fu.

```
data List (A : Type) : Type where
  []    : List A                -- The empty list
  _::_  : A → List A → List A   -- The list with a head item and a tail remainder list
```

That is, a list is either the empty list ``[]``, or the list `a
:: l` which has `a` at the head and `l` as the remainder of th list.
We use some reasonably common symbols as the names of the two
constructors. Other functional languages might call these `nil` and
`cons`.

A list that we would typically write as `[1, 2, 3]` can be constructed
by stringing together the ``::`` constructor:

```
shortList : List ℕ
shortList = 1 :: 2 :: 3 :: []
```

We can define concatenation of lists by recursion. For example, the
concatenation `[1, 2, 3] ++ [4, 5, 6]` is `[1, 2, 3, 4, 5, 6]`.

```
_++_ : {A : Type} → List A → List A → List A
[] ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)
```

In words, concatenating the empty list to any list doesn't change it,
and when concatenating a list with a head to another list, the result
has the same head, and the remainder is the concatenation with the
remainder.

Compare this to the definition of addition on ``ℕ``, the
structure is *exactly* the same (if we rewrite the second case as
`_::_ x l` rather than using the constructor infix). All that is
different is keeping track of the element of `A`.

We can define the length of a list by recursion, essentially by
forgetting the elements in the list::

```
length : {A : Type} → List A → ℕ
-- Exercise:
length L = {!!}
```

A natural number can be seen as a list of tally marks.

```
ℕ→List⊤ : ℕ → List ⊤
-- Exercise:
ℕ→List⊤ n = {!!}

_ : ℕ→List⊤ 3 ≡ tt :: tt :: tt :: []
_ = λ i → ℕ→List⊤ 3
```

Together with `length : List ⊤ → ℕ`, we have a bijection between the
type of natural numbers and the type of lists of tally marks.


## The Integers

Now we can describe the integers. An integer is either a natural
number or a *strictly* negative number. We have to be careful here, we
don't want more than one copy of 0! Turning this into an inductive
definition:

```
data ℤ : Type where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ
```

The ``negsuc`` constructor represents the negative of the
successor of a natural number, so `negsuc n` represents $-(n + 1)$.

We can define the various arithmetic operations of the integers.
First, we need a few helper functions. This one negates a natural
number into an integer. We can't just define `negℕ n = negsuc n`,
because this would send $n$ to $-(n + 1)$!

```
negℕ : ℕ → ℤ
negℕ zero = pos zero
negℕ (suc n) = negsuc n
```

Next, the successor of an integer, which sends $z$ to $z + 1$, and
similarly the predecessor function which sends $z$ to $z - 1$.

```
sucℤ : ℤ → ℤ
-- Exercise:
sucℤ z = {!!}

predℤ : ℤ → ℤ
-- Exercise:
predℤ z = {!!}
```

Now for addition of integers. Since the integers are a disjoint union
of the natural numbers and the negative numbers, it helps to handle
these two cases separately. You will have to use ``sucℤ`` and
``predℤ`` in these definitions.

```
-- This should correspond to $z + n$, where $n$ is a natural number
_+pos_ : ℤ → ℕ → ℤ
-- Exercise:
z +pos n = {!!}

-- This should correspond to $z + -(n+1)$, where $n$ is a natural number
_+negsuc_ : ℤ → ℕ → ℤ
-- Exercise:
z +negsuc n = {!!}

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ pos n = m +pos n
m +ℤ negsuc n = m +negsuc n
```

We can negate an integer, and define the subtraction of integers in
terms of addition and negation.

```
-_ : ℤ → ℤ
-- Exercise:
- z = {!!}

_-ℤ_ : ℤ → ℤ → ℤ
m -ℤ n = m +ℤ (- n)
```

See if you can come up with the correct definition for multiplication
of integers. This can be done by case-splitting on only one of the
sides.

```
_·ℤ_ : ℤ → ℤ → ℤ
-- Exercise:
n ·ℤ m = {!!}
```

Make sure to test this one via `C-c C-n`, especially the
``negsuc`` cases! They are easy to get wrong.

Soon we will have the tools to write some test-cases and have Agda
check them, so we don't have to use the "normalise" command by hand.


## Fixities

These final lines specify the precedence that each operator has (so
that `a + b · c` is interpreted as `a + (b · c)`), and whether it
associates to the left or the right (so that `a + b + c` is
interpreted as `(a + b) + c`).

```
infix  8 -_
infixl 7 _·ℕ_ _·ℤ_
infixl 6 _+ℕ_ _+ℤ_ _-ℤ_

infixr 5 _::_
infixr 5 _++_
```

## Unicode Dictionary

| Char | Input              |
|------|--------------------|
| ⇒    | \=> or \Rightarrow |
| ⊤    | \top               |
| ∅    | \0 or \emptyset    |
| ⊎    | \uplus             |
| ·    | \cdot              |
| ℤ    | \bZ                |

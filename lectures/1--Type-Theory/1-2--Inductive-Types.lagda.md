<!--
```
module 1--Type-Theory.1-2--Inductive-Types where

open import Library.Prelude
```
-->


# Lecture 1-2: Inductive Types

In the last lecture, we saw some abstract type theory. In this
lecture, we'll get to define our own concrete data-types.

Agda's data-types come in two flavours which are in some sense mirror
images of each other:

* **Inductive types**: These include Booleans, natural numbers, lists,
  more generally, any type which is specified by a set of options,
  and whose elements are specified by choosing among those options.
* **Record types**: These include product and Σ-types, more generally,
  any type specified by a set of fields, and whose elements are
  specified by choosing a value for each of those fields.

In this Lecture we'll see our first few examples of inductive types.
We'll return to record types in Lecture 1-X.

## Booleans

An inductive type is a type whose elements are built up out of
"constructors". Here is the inductive type of Booleans:

```
data Bool : Type where
  true  : Bool
  false : Bool
```

This definition says that to construct a Boolean we either construct
it using ``true`` or using ``false`` --- that is, a Boolean is either
``true`` or ``false``.

What makes a data type "inductive" is its *induction principle*, a
process which is often called *case analysis*: "to use an element of
an inductive type, it suffices to split into cases for what we would
do for each of the constructors". For example, we may define the
logical ``not`` by saying what the result is in the case the Boolean
is ``true``, and in the case the Boolean is ``false``:

```
not : Bool → Bool
not b = case b of λ
  { true  → false
  ; false → true
  }
```

Here, the ``not`` function accepts the argument `b` and then splits
into cases depending on which constructor of ``Bool`` was used to
construct `b`.

::: Aside:
Induction may seem like an odd name if you are used to "proof by
induction" from your discrete maths course, but we will see below that
the induction principle for ``ℕ`` is basically the mathematical
induction you are used to.
:::

If we do case analysis on a ``Bool`` which is literally ``true`` or
``false`` rather than a variable or some other expression, then the
case analysis will disappear leaving the value of the appropriate
case. This is the *computation rule* for Booleans.

For example, normalising the expression `not false` leads to the case
analysis

```
_ = test-identical

    (case false of λ
      { true  → false
      ; false → true
    })

    true
```

which as you can see does compute to the value ``true``. (Remember you
can normalise any expression you like by typing `C-c C-n`.)

We can construct other functions by nesting this kind of case
analysis. Here's one way we could write a Boolean ``and``
operation:

```
_and_ : Bool → Bool → Bool
_and_ x y = case x of λ
  { true  → case y of λ
            { true  → true
            ; false → false }
  ; false → false
  }

_xor_ : Bool → Bool → Bool
-- Exercise:
x xor y = {!!}
```

mvrnote: recall what xor means here?

mvrnote: multi-line goals are not allowed, consider modifying this exercise

Agda considers definitions with names that contain underscores
specially, and lets us use them in two ways: either literally like any
other definition, as in `_and_ x y`, or with the arguments taking the
place of the underscores, as in `x and y`. We will use infix operators
like this whenever it is closer to normal mathematical practice, as
with these Boolean operators, arithmetic operators like ``_·_``,
pairing ``_,_``, etc.

It is not required to do case analysis on all the variables that are
available. Try giving a definition of the logical "or" by case
analysis only on the variable `x`.

```
_or_ : Bool → Bool → Bool
-- Exercise:
x or y = {!!}
```

::: Aside:
The different choices for how we do case analysis in a definition can
result in different computational behaviour. For example, with the
above definition of ``or``, the expression `true or y` will compute to
``true`` and `false or y` will compute to `y`, but `x or true` and `x
or false` will both be stuck waiting for the value of `x` to do case
analysis on.

```
_ = λ (y : Bool) → test-identical (true or y) true
_ = λ (y : Bool) → test-identical (false or y) y
-- Won't work:
-- _ = λ (x : Bool) → test-identical (x or true) true
-- _ = λ (x : Bool) → test-identical (x or false) x
```
:::


## Pattern Matching

In all the above definitions we accept some elements of an inductive
type as arguments and then immediately split into cases. This is
overwhelmingly the most common situation when working with inductive
types, so Agda gives us some pleasant syntax for it. Rather than
writing definitions with variable names on the left of the `=` sign,
we can write multiple lines of definition, one for each possible
constructor that could occur in that position.

```
not' : Bool → Bool
not' true  = false
not' false = true

_and'_ : Bool → Bool → Bool
true  and' true  = true
true  and' false = false
false and' true  = false
false and' false = false
```

Although there are multiple `=` signs, all of them together constitute
a single definition. Agda uses a mechanism called "coverage checking"
to make sure that every case is covered by your definition, and will
complain if you missed something. If desired, it is always possible to
rewrite such a definition as a single expression that does the
case-splitting manually.

The method of writing functions where we describe what they do on
particular forms of their input is called *pattern matching*. We
already saw an example of this in the previous lecture when writing
functions with pairs as arguments. Agda has nice support for working
with pattern matching --- it can automatically write out all the cases
that are needed to define a function involving an inductive type. To
have Agda do this for you, place your cursor in a hole and press `C-c
C-c`. You will be prompted for the list of variables separated by
spaces that you want to apply case-splitting to.

Try this below: press `C-c C-c` in the hole for ``_xor'_`` below and
enter `x y` to have Agda split this definition into all the cases you
need to handle.

```
_xor'_ : Bool → Bool → Bool
-- Exercise:
x xor' y = {!!}
```

As before, we don't necessarily have to to case-split on all the
variables. Try leaving `y` un-split as you did in the first definition
of ``or``.

```
_or'_ : Bool → Bool → Bool
-- Exercise:
x or' y = {!!}
```

Here is the definition of logical implication. There is a strange
feature of this definition which has a Latin name: "ex falso
quodlibet" --- ``false`` implies anything.

```
_implies_ : Bool → Bool → Bool
true  implies true  = true
true  implies false = false
false implies _     = true
```

Here we use a "wildcard" argument (the underscore `_`) to say that the
definition we are giving is valid for anything we put in that spot, so
we don't have to bother giving the variable a name at all.

There is nothing special about ``Bool`` having exactly two
constructors, we can just as well define a type with seven elements:

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

And define functions out of it by providing cases for each of the
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
-- Exercise: (Use `C-c C-c` to split into cases for you.)
nextDay c = {!!}
```


## The Unit

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

ignore-bool : Bool → ⊤
ignore-bool b = tt
```

Because ``⊤`` contains no information, maps into ``⊤`` provide no
information either.

```
⊤-ump-in-to : {A : Type}
  → ⊤
  → (A → ⊤)
-- Exercise:
⊤-ump-in-to t = {!!}

⊤-ump-in-fro : {A : Type}
  → (A → ⊤)
  → ⊤
-- Exercise:
⊤-ump-in-fro f = {!!}
```

These two functions constitute the universal "mapping-in" property of
``⊤``, like the one that we saw for ``×`` in ``×-ump-to`` and
``×-ump-fro``.

``⊤`` is a little unusual, in that it also has a universal
"mapping-*out*" property, which says that maps out of ``⊤`` just pick
an element of the output type.

```
⊤-ump-out-to : {A : Type}
  → A
  → (⊤ → A)
-- Exercise:
⊤-ump-out-to t = {!!}

⊤-ump-out-fro : {A : Type}
  → (⊤ → A)
  → A
-- Exercise:
⊤-ump-out-fro f = {!!}
```


## Natural Numbers

Enough with the simple data types, let's do some mathematics. We can
define the natural numbers ``ℕ`` as an inductive data type with two
constructors. There is a constructor `zero : ℕ`, saying that zero is a
natural number, and a constructor `suc : ℕ → ℕ`, which says that if
`n` is already a natural number then `suc n` (the "successor" of `n`,
i.e. `1 + n`) is also a natural number.

We actually defined ``ℕ`` behind the scenes so that we could use it in
Lecture 1-1. On the website, you can click on its name to take you
there.

The exact definition of ``ℕ``, copy-pasted, is:

    data ℕ : Type where
      zero : ℕ
      suc  : ℕ → ℕ

(We leave it commented out, so that Agda doesn't complain about
defining a new type with the same name as an existing one.)

Defining functions out of ``ℕ`` is similar to defining functions out
of ``Bool``, we just have to give cases for the two constructors. 

mvrnote: this may be confusing, it could be read as somehow saying
that `suc` takes the number to a smaller one

The difference is that the ``suc`` constructor tells us which natural
number the provided argument is the successor of.

Here's a first example:

```
isZero : ℕ → Bool
isZero zero = true
isZero (suc n) = false

_ = test-identical (isZero 0)  true
_ = test-identical (isZero 19) false
```

So, ``isZero`` is ``true`` for zero, and ``false`` for any successor.

::: Aside:
Agda throws in some secret-sauce that lets us write elements of ``ℕ``
as numerals `1`, `2`, `3`, ..., rather than having to write out `suc
(suc (suc zero))` for `3`, for example.
:::


For ``isZero`` we didn't need to use the variable `n`, but to do
anything interesting we will. For example:

```
doubleℕ : ℕ → ℕ
doubleℕ zero = zero
doubleℕ (suc n) = suc (suc (doubleℕ n))
```

Thinking mathematically, $2 × 0 = 0$, covering the first case. For the
second case, $2 × (1 + n) = 2 + (2 × n)$. To achieve the $2 +$ part,
we use ``suc`` twice, and to achieve the $2 × n$ part, we use a
recursive call to the ``doubleℕ`` function we are currently defining!

mvrnote: draw a diagram of the recursion, or do the unfolding all the way out

Agda allows this kind of recursion so long as it is convinced that the
argument that you provide to the recursive call is smaller than the
argument that you started with. That is certainly the case here,
because we go from `suc n` to just `n`.

We can even do what is called "mutual" recursion, where two
definitions depend on each other to make sense. Here is a definition
of a function that decides whether a number is even, defined together
with the same for whether a number is odd:

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

_ = test-identical (2 +ℕ 3) 5
```

mvrnote: draw a diagram of the recursion, or do the unfolding all the way out

Remember that you can test any piece of code yourself by typing `C-c
C-n` and then `2 +ℕ 3`, say.

Here we have chosen to split into cases on the left side and leave the
right side alone, but we could equally well split into cases on the
right instead:

```
_+ℕ'_ : ℕ → ℕ → ℕ
n +ℕ' zero = n
n +ℕ' (suc m) = suc (n +ℕ' m)

_ = test-identical (2 +ℕ' 3) 5
```

We will be able to show that these two versions of addition do produce
the same result whenever they are handed two concrete elements of
``ℕ``, but Agda isn't able to automatically consider them *exactly*
identical.

```
-- This will fail!
-- _ = test-identical _+ℕ_ _+ℕ'_
```

One way they are not identical is that they have different
computational behaviour:

```
_ = λ (m : ℕ) → test-identical (zero +ℕ m) m
-- Fails, because `+ℕ` case splits on `n`!
-- _ = λ (n : ℕ) → test-identical (n +ℕ zero) n
_ = λ (n : ℕ) → test-identical (n +ℕ' zero) n
```

Try some other ordinary operations on natural numbers. To figure out
how these should go, calculate what the answer should be
mathematically. For example, $(1 + n) × m = m + (n × m)$, and this can
be turned into one of the cases for multiplication.

```
-- Multiplication
_·ℕ_ : ℕ → ℕ → ℕ
-- Exercise:
n ·ℕ m = {!!}

_ = test-identical (0 ·ℕ 1) 0
_ = test-identical (2 ·ℕ 3) 6
_ = test-identical (3 ·ℕ 2) 6

-- Exponentiation
_^ℕ_ : ℕ → ℕ → ℕ
-- Exercise:
n ^ℕ m = {!!}

_ = test-identical (1 ^ℕ 1) 1
_ = test-identical (2 ^ℕ 3) 8
_ = test-identical (3 ^ℕ 2) 9
```

Remember that you can test these manually using `C-c C-n`!

We can also define a "predecessor" operation, which partially undoes
the successor `suc : ℕ → ℕ`. Of course, it can't fully undo it, since
``zero`` has nowhere to go except ``zero`` again.

```
predℕ : ℕ → ℕ
-- Exercise:
predℕ n = {!!}

_ = test-identical (predℕ 0) 0
_ = test-identical (predℕ 1) 0
_ = test-identical (predℕ 19) 18
```


## Lists

If this were a course on functional programming, we would spend a lot
more time working with lists. This isn't a course on functional
programming, but it's worth seeing a little of how ``List``s are
handled.

```
data List (A : Type) : Type where
  []    : List A                -- The empty list
  _::_  : A → List A → List A   -- The list with a head element and a tail remainder
```

That is, a list is either the empty list ``[]``, or the list `a :: l`
which has `a` at the head and `l` as the remainder of the list. We use
some reasonably common symbols as the names of the two constructors.
Other functional languages might call these `nil` and `cons`.

A list that we would typically write as `[1, 2, 3]` can be constructed
by stringing together the ``::`` constructor, and ending with the
``[]`` constructor:

```
shortList : List ℕ
shortList = 34 :: 19 :: []
```

``List`` is our first example of an "indexed" inductive type, a type
constructor that requires an argument. Here, for any type `T`, there
is an inductive type `List T` with those two constructors, where `T`
has been substituted wherever `A` appears in the types of those
constructors. This is what lets us use the `[]` constructor as though
it has type `List ℕ`, and the `::` constructor as though it has type
`ℕ → List ℕ → List ℕ` in the definition of ``shortList``.

It is fairly common to create a list with a singleton element, so here
is a helper that achieves that.

```
[_] : {A : Type} → A → List A
[ a ] = a :: []
```

The type that we want to use for the elements of the list is accepted
as an implicit argument. As usual, `List A` doesn't make sense as a
type unless we have defined what `A` is somewhere.

Concatenation of lists is defined by pattern-matching. For example, the
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

With this in mind, try defining a function to calculate the `length`
of a list.

```
length : {A : Type} → List A → ℕ
-- Exercise:
length L = {!!}

_ = test-identical (length [ tt ]) 1
_ = test-identical (length (1 :: 2 :: 3 :: [])) 3
```

In the other direction, a natural number can be seen as a list of tally marks.

```
ℕ→List⊤ : ℕ → List ⊤
-- Exercise:
ℕ→List⊤ n = {!!}

_ = test-identical (ℕ→List⊤ 0) []
_ = test-identical (ℕ→List⊤ 3) (tt :: tt :: tt :: [])
```

Together with `length : List ⊤ → ℕ`, we have a bijection between the
type of natural numbers and the type of lists of tally marks.

As one final example, try using ``++`` to define a ``reverse``
function.

```
reverse : {A : Type} → List A → List A
-- Exercise:
reverse x = {!!}

_ = test-identical (reverse [ 1 ]) [ 1 ]
_ = test-identical (reverse (1 :: 2 :: 3 :: [])) (3 :: 2 :: 1 :: [])
```


## Integers

We can use the type of natural numbers as a stepping stone to the
integers. An integer is either a natural number or a *strictly*
negative integer. We have to be careful here, we don't want to
accidentally have more than one way to represent 0! =Turning this into
an inductive definition:

```
data ℤ : Type where
  pos    : ℕ → ℤ
  negsuc : ℕ → ℤ
```

The ``negsuc`` constructor represents the negative of the
successor of a natural number, so `negsuc n` represents $-(n + 1)$.

We can define integer versions of the various arithmetic operations
``+ℕ``, ``·ℕ``, and so on. First, we need a few helper functions. This
first one negates a natural number into an integer. We can't just
define `negℕ n = negsuc n`, because this would send $n$ to $-(n + 1)$!

```
negℕ : ℕ → ℤ
negℕ zero = pos zero
negℕ (suc n) = negsuc n
```

::: Aside:
The following code snippet hooks ``ℤ`` into the same mechanism as
``ℕ`` that lets us write numerals rather than chains of ``suc`` and
``zero``. Pay no attention to the man behind the curtain!

```
instance
  Number-ℤ : Number ℤ
  Number-ℤ .fromNat = pos

  Negative-ℤ : Negative ℤ
  Negative-ℤ .fromNeg = negℕ

_ = test-identical 2 (pos (suc (suc (zero))))
_ = test-identical -3 (negsuc (suc (suc (zero))))
```
:::

Next, the successor function which sends $z$ to $z + 1$, and similarly
the predecessor function which sends $z$ to $z - 1$.

```
sucℤ : ℤ → ℤ
-- Exercise:
sucℤ z = {!!}

_ = test-identical (sucℤ 19) 20
_ = test-identical (sucℤ -34) -33

predℤ : ℤ → ℤ
-- Exercise:
predℤ z = {!!}

_ = test-identical (predℤ 19) 18
_ = test-identical (predℤ -34) -35
```

This was all preparation for addition of integers. Since the integers
are a disjoint union of the natural numbers and the negative numbers,
it helps to handle these two cases separately. You will have to use
``sucℤ`` and ``predℤ`` in these definitions.

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
m +ℤ (pos n) = m +pos n
m +ℤ (negsuc n) = m +negsuc n

_ = test-identical (0 +ℤ 0) 0
_ = test-identical (0 +ℤ 1) 1
_ = test-identical (1 +ℤ 0) 1
_ = test-identical (19 +ℤ 34) 53
_ = test-identical (-19 +ℤ 34) 15
```
mvrnote: need tests with negative on right

We can negate an integer, and define the subtraction of integers in
terms of addition and negation.

```
-_ : ℤ → ℤ
-- Exercise:
- z = {!!}

_ = test-identical (- 0) 0
_ = test-identical (- 19) (-19)
_ = test-identical (- (-34)) 34

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

_ = test-identical (0 ·ℤ 0) 0
_ = test-identical (2 ·ℤ 3) 6
_ = test-identical (2 ·ℤ -3) -6
_ = test-identical (-2 ·ℤ 3) -6
_ = test-identical (-2 ·ℤ -3) 6
```

Make sure to test this one via `C-c C-n`, especially the
``negsuc`` cases! They are easy to get wrong.


## Recursion Principles

As we mentioned above, these inductive data types are characterised by
their "induction principles". In this lecture we focus on a simpler
version of this principle, "recursion", and will return to induction
in Lecture 1-X.

The recursion principle for a type packs together the data that is
necessary to produce a function out of it into some other type. In the
case of ``Bool``, to construct a function `Bool → A` for any type `A`
we just need two elements of `A` to serve as the values of the
function when the ``Bool`` is ``true`` and ``false``. We can write out
the recursion principle for ``Bool`` as follows:

```
Bool-rec : {A : Type}
  → A
  → A
  → (Bool → A)
Bool-rec a1 a2 true = a1
Bool-rec a1 a2 false = a2
```

The ``Bool`` type is so simple that the name "recursion" feels
inappropriate: the recursion principle doesn't actually do any
recursion! The name will make more sense when we do the same for
``ℕ``.

::: Aside:
The recursion principle for Booleans has a more familiar name: the
"if/then/else" pattern familiar from almost every programming
language:

```
if-then-else : {A : Type}
  → Bool
  → A
  → A
  → A
if-then-else b a1 a2 = Bool-rec a1 a2 b
```
:::

This function is one side of a universal mapping property. Given two
elements of `A`, we can make a function `Bool → A`. But from such a
function we can also extract the two elements of `A` we started with:

```
Bool-rec-fro : {A : Type}
  → (Bool → A)
  → A × A
-- Exercise:
Bool-rec-fro f = {!!}
```

We won't usually need to use the recursion principle ``Bool-rec`` by
that name: instead, we can just do an ordinary pattern match on an
argument of type ``Bool``. But, for some practice, try using
``Bool-rec`` to re-implement these:

```
not-fromRec : Bool → Bool
-- Exercise: (Don't pattern match on `x`!)
not-fromRec x = Bool-rec {!!} {!!} {!!}

-- You will need to use `Bool-rec` twice!
or-fromRec : Bool → Bool → Bool
-- Exercise: (Don't pattern match at all!)
or-fromRec x y = Bool-rec {!!} {!!} {!!}
```

mvrnote: add some tests for these two

The recursion principle for the unit type is even simpler. To define a
function `⊤ → A`, it suffices to give an element of `A` (which is to
be the image of the unique element ``tt``), and that's it.

```
⊤-rec : {A : Type}
  → A
  → (⊤ → A)
⊤-rec a tt = a
```

Again, we can go back: from such a function `⊤ → A`, we can recover
the original value of `A`:

```
⊤-rec-fro : {A : Type}
  → (⊤ → A)
  → A
⊤-rec-fro f = f tt
```

More excitingly, we have the recursion principle for ``ℕ``. To define
a function `ℕ → A`, we need an element of a `A` to use for ``zero``,
and a function `A → A` that takes us from the value for `n` to the
value for `suc n`. By ordinary mathematical induction, this will be
enough to give a value to every element of ``ℕ``.

```
ℕ-rec : {A : Type}
  → A                 -- The base casea
  → (A → A)           -- The recursion law
  → (ℕ → A)
ℕ-rec a r zero = a
ℕ-rec a r (suc n) = r (ℕ-rec a r n)
```

Try re-implementing ``double`` using ``ℕ-rec``:

```
double' : ℕ → ℕ
-- Exercise:
double' = ℕ-rec {!!} {!!}
```

When pattern matching, in the ``suc`` case we are allowed access to
access to the previous `n`: without this, functions like ``predℕ`` are
a bit irritating to write. (Try it!)

We can define an improved version of ``ℕ-rec`` that gives access to
the current `n` in the inductive step.

```
ℕ-rec' : {A : Type}
  → A
  → (ℕ → A → A)
  → (ℕ → A)
-- Exercise:
ℕ-rec' a r zero = {!!}
ℕ-rec' a r (suc n) = {!!}
```

For an extra challenge, try defining this only in terms of the less powerful
``ℕ-rec``!

```
ℕ-rec'' : {A : Type}
  → A                 -- The base case
  → (ℕ → A → A)       -- The recursion law
  → (ℕ → A)
-- Exercise:
ℕ-rec'' a r n = ℕ-rec {!!} {!!} {!!}
```


## Fixities

These final lines specify the precedence that each operator has, so
that `a + b · c` is interpreted as `a + (b · c)`. They also specify
whether it associates to the left or the right, so that `a + b + c` is
interpreted as `(a + b) + c`, and `a :: b :: []` is interpreted as
`a :: (b :: [])`.

```
infix  8 -_
infixl 7 _·ℕ_ _·ℤ_
infixl 6 _+ℕ_ _+ℤ_ _-ℤ_

infixr 5 _::_
infixr 5 _++_
```


## References and Further Reading

coverage checker
Elaboration:
https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf
https://pl.ewi.tudelft.nl/master-projects/master/2022/10/25/kayleigh-lieverse/
https://jesper.sikanda.be/files/thesis-final-digital.pdf
https://link.springer.com/chapter/10.1007/11780274_27

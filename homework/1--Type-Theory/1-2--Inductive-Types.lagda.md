# Homework 1-2: Inductive Types
```
module homework.1--Type-Theory.1-2--Inductive-Types where

open import homework.Library.Prelude

```
Topics Covered:
* Booleans
* The Empty and Unit types
* Natural numbers
* Lists
* Coproducts
* Integers

In the last lecture, we saw some abstract type theory. In this
lecture, we'll get to define our own concrete data types.

A data type, also known as an inductive type, is a type whose elements
are built up out of "constructors". Here is the data type of Boolean
values:
```
data Bool : Type where
  true  : Bool
  false : Bool
```

This definition says, intuitively, that to construct a Boolean we
either construct it out of `true` or out of `false` --- that is, a
Boolean is either `true` or `false`.

What makes a data type "inductive" is its "induction principle": to
define a function out of an inductive type, it suffices to define the
behavior of the function on all the constructors. For example, we may
define the logical `not` by saying what it does to `true` and to
`false`:
```
not : Bool → Bool
not true = false
not false = true
```

Induction may seem like an odd name if you are used to "proof by
induction" from your discrete math course, but we will see below that
the induction principle for `ℕ` is basically the induction you are
used to.

The method of writing functions where we describe what they do on
particular forms of their input is called "pattern matching". Agda has
nice support for the pattern matching style of defining functions ---
it can automatically write out all cases you need to cover to define a
function out of an inductive data type. This is called doing a "case
split". To have Agda do this for you use the emacs function
agda2-make-case (`C-c C-c` in agda2-mode) with your cursor in a hole,
and then list the variables you want to case split on, separated by
spaces.

Try this here: press `C-c C-c` in hole 0 below and type `x y`, and watch
Agda split this definition into all the cases you need to handle. The
logical "and" of two Booleans `x` and `y` is `true` just when both `x`
and `y` are `true`.

```
_and_ : Bool → Bool → Bool
-- Exercise:
x and y = {!!}
```

You don't have to split on all variables at once. Give a definition of
the logical "or" by case splitting only on the variable `x`:
```
_or_ : Bool → Bool → Bool
-- Exercise:
true or y = {!!}
false or y = {!!}
```

Here is the definition of logical implication. There is a strange
feature of this definition which has a fancy Latin name: "ex falso
quodlibet" --- false implies anything. Over the course of this and the
next lecture, we'll see why this is a useful principle to take, even
if it seems unintuitive.

```
_⇒_ : Bool → Bool → Bool
true ⇒ true  = true
true ⇒ false = false
-- Here we use a "wildcard" (the underscore "_") to say that the
-- definition we are given is valid for anything we put in that spot.
false ⇒ _    = true
```

In general, inductive data types are characterized by their induction
principles. In this lecture we will start focussing on a simpler
incarnation, "recursion", and will return to induction in the next
lecture.

The recursion principle for a type packs together the data that is
necessary to produce a non-dependent function out of it. To construct
a function `Bool → A`, we just need two elements of `A` to serve as
the images of `true` and `false`. We can write out the recursion
principle for `Bool` as follows:

```
Bool-rec : {ℓ : Level} {A : Type ℓ}
         → A
         → A
         → (Bool → A)
Bool-rec a1 a2 true = a1
Bool-rec a1 a2 false = a2
```

The recursion principle for Booleans is known under a more common
name: the "if-then-else" pattern familiar in many programming
languages:
```
if_then_else_ : {ℓ : Level} {A : Type ℓ}
              → Bool
              → A
              → A
              → A
if b then a1 else a2 = Bool-rec a1 a2 b
```
As in the definition of composition `f ∘ g`, we are using underscores
to tell Agda where the function arguments go. Writing the
application `if b then a1 else a2` is the same as
`if_then_else_ b a1 a2`.

`Bool` is a pretty simple data type, but it isn't the simplest. We can
use even fewer constructors. With one constructor, we have the unit
type `⊤`:

```
data ⊤ : Type₀ where
  tt : ⊤

⊤-rec : {ℓ : Level} {A : Type ℓ} (a : A)
      → (⊤ → A)
⊤-rec a tt = a
```

The recursion principle for the unit type `⊤` says that to define a
function `⊤ → A`, it suffices to give an element `a : A` (which is to
be the image of the single element `tt : ⊤`).

We can go even further, however. We can define a data type `∅` with no
constructors. This is called the "empty type":
```
data ∅ : Type₀ where
```

The recursion principle of the empty type is a version of the "ex
falso quodlibet" principle of logic: with no assumptions, we may
define a map `∅ → A`. The definition of this map is also by pattern
matching, except in this case there are no constructions and so no
patterns to match with. Agda has special syntax for this situation:
`()`, the empty pattern.

```
∅-rec : {ℓ : Level} {A : Type ℓ}
        → ∅ → A
∅-rec ()
```

Enough with the simple data types, let's start to do some
mathematics. We can define the natural numbers with a recursive data
type. We have a constructor `zero : ℕ`, saying that zero is a natural
number, and a constructor `suc : (n : ℕ) → ℕ` which says that if `n`
is already a natural number, then `suc n` (the "successor" of `n`, or
`n + 1`) is a natural number.
```
data ℕ : Type₀ where
  zero : ℕ
  suc  : ℕ → ℕ

-- This lets us use numerals 0, 1, ... to construct elements of `ℕ`
{-# BUILTIN NATURAL ℕ #-}
```

The recursion principle for the natural numbers is the usual
definition of a function by recursion:
```
ℕ-rec : {ℓ : Level} {A : Type ℓ}
      → (a₀ : A)                 -- The base case
      → (recurse : ℕ → A → A)    -- The recursion law
      → (ℕ → A)
ℕ-rec a₀ recurse zero = a₀
ℕ-rec a₀ recurse (suc n) = recurse n (ℕ-rec a₀ recurse n)
```

Using pattern matching, we can define the arithmetic operations on
numbers:
```
_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

_·_ : ℕ → ℕ → ℕ
-- Exercise:
n · m = {!!}
```

Here we have chosen to case-split on the first argument, but we could
instead case-split on the second:
```
_+s_ : ℕ → ℕ → ℕ
n +s zero = n
n +s (suc m) = suc (n + m)
```
We will be able to show that these two versions are equal, but Agda
doesn't consider them exactly the same.

We can also define a "predecessor" operation, which partially undoes
the successor `suc : ℕ → ℕ`. Of course, it can't fully undo it, since
`zero` has nowhere to go but to itself.

```
predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n
```

If this were a course on functional programming, we would spend a lot
more time with lists. This isn't a course on functional programming,
but it's worth seeing a smidge of list-fu.

```
data List (A : Type) : Type where
  [] : List A                   -- The empty list, which has nothing in it
  _∷_  : A → List A → List A    -- Adding a single item to the front of a list
```

We use some reasonably common symbols as the names of the two
constructors. Other languages might call these `nil` and `cons`.

A list that we would typically write as `[1, 2, 3]` can be constructed
by stringing together the `_∷_` constructor:

```
shortList : List ℕ
shortList = 1 ∷ 2 ∷ 3 ∷ []
```

We can define concatenation of lists by recursion. For example, the
concatenation `[1, 2, 3] ++ [4, 5, 6]` is `[1, 2, 3, 4, 5, 6]`.

```
infixr 5 _++_

_++_ : {A : Type} → List A → List A → List A
[] ++ L2 = L2                        -- concatenating the empty list to a list doesn't change it.
(x ∷ L1) ++ L2 = x ∷ (L1 ++ L2)      -- [x, rest] ++ L2 should be [x, rest ++ L2].
```
Compare this to the definition of addition on `ℕ`, the structure is
*exactly* the same (if we write the second case as `_∷_ x L` maybe).

We can define the length of a list by recursion:
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
```

Together with `length : List ⊤ → ℕ`, we have a bijection between the
type of natural numbers and the type of lists of tally marks. We don't
yet have the tools to express this, but we will develop them in Part 2
of this course.

Next, let's define the disjoint union of two types. An element of the
disjoint union `A ⊎ B` should either be an element of `A` or an element
of `B`. We can turn this into the definition of an inductive type.
```
data _⊎_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
```
The names of the constructors mean "in-left" and "in-right".

The recursion principle for the disjoint union is "dual" to the
universal mapping property of the product that we saw at the end of
the last lecture. There, we had that `f : C → A` and `g : C → B` we
get `×-ump f g : C → A × B`. Now, from `f : A → C` and `g : B → C`, we
get a map `⊎-rec f g : A ⊎ B → C,`.

```
⊎-rec : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      → (f : A → C)
      → (g : B → C)
      → (A ⊎ B → C)
⊎-rec f g (inl a) = f a
⊎-rec f g (inr b) = g b
```

Since a `Bool` is either `true` or `false`, we should be able to see
`Bool` and the disjoint union of the set `{true}` (represented by `⊤`)
and `{false}` (represented by another copy of `⊤`). We can construct
maps to that effect:
```
Bool→⊤⊎⊤ : Bool → ⊤ ⊎ ⊤
-- Exercise:
Bool→⊤⊎⊤ b = {!!}

⊤⊎⊤→Bool : ⊤ ⊎ ⊤ → Bool
-- Exercise:
⊤⊎⊤→Bool c = {!!}
```

Clearly, if you turned a `Bool` into an element of `⊤ ⊎ ⊤` and then
back into a Boolean using these maps, you'd get to where you started;
and vice-versa. Therefore, these maps give a bijection between Bool
and `⊤ ⊎ ⊤`.

There is a sense in which ⊎ acts like an addition of types, and ∅ acts
like zero. This addition of types satisfies the expected laws up
to equivalence, but again we can't yet fully express that.
```
∅⊎-to : {ℓ : Level} (A : Type ℓ) → ∅ ⊎ A → A
-- Exercise:
∅⊎-to A x = {!!}

∅⊎-fro : {ℓ : Level} (A : Type ℓ) → A → ∅ ⊎ A
-- Exercise:
∅⊎-fro A a = {!!}
```

Now we can describe the integers. An integer is either a natural
number or a strictly negative number, so we can turn this into an
inductive definition:
```
data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ
```

It's worth noting that the integers are the disjoint union of two
copies of the natural numbers (with one copy shifted up by one and
then negated):
```
ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
-- Exercise:
ℤ→ℕ⊎ℕ z = {!!}


ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
-- Exercise:
ℕ⊎ℕ→ℤ z = {!!}
```

We can define the various arithmetic operations of the
integers. First, we need a few helper functions. This one negates a
natural number into an integer (without shifting it first):
```
neg : ℕ → ℤ
neg zero = pos zero
neg (suc n) = negsuc n
```

Now we can define the successor of integers which sends `z` to `z +
1`, and the predecessor function which sends `z` to `z - 1`. This time, we can send zero to -1.
```
sucℤ : ℤ → ℤ
-- Exercise:
sucℤ z = {!!}

predℤ : ℤ → ℤ
-- Exercise:
predℤ z = {!!}
```

Now we turn our attention to defining addition of integers. Since the
integers are the disjoint union of two copies of the natural numbers,
there are two cases to handle. We'll make things simpler by separating
these cases out.

```
_+pos_ : ℤ → ℕ → ℤ
-- Exercise:
z +pos n = {!!}

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

_-_ : ℤ → ℤ → ℤ
m - n = m +ℤ (- n)
```

See if you can come up with the correct definition for multiplication
of integers.
```
_·ℤ_ : ℤ → ℤ → ℤ
-- Exercise:
n ·ℤ m = {!!}
```

## Functions as products

We will sometimes think of the dependent function type as a
generalised cartesian product. In a function with type `(x : A) → B
x`, the `x : A` acts like an index, and then for each index we have an
element of the corresponding type. If `A` has exactly two elements `0`
and `1`, say, then `(x : A) → B x` is the binary cartesian product of
`B 0` and `B 1`.

## Operator precedence

We defined some operators in this module. The following lines specify
the precedence that each operator has (so `a + b · c` is interpreted
as `a + (b · c)`), and whether it associates to the left or the right
(so `a + b + c` is interpreted as `(a + b) + c`).

```
infix  8 -_
infixl 7 _·_ _·ℤ_
infixl 6 _+_ _+ℤ_ _-_

infixr 5 _∷_
```

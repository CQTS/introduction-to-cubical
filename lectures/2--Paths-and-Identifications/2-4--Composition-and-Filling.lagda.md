<!--
```
module 2--Paths-and-Identifications.2-4--Composition-and-Filling where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C D : Type ℓ
    x y z w : A
```
-->


# Lecture 2-4: Composition and Filling

Cubical Agda adds a number of primitive notions that make working with
paths-between-paths easier. To understand how they work, we will
really have to start putting the "cubical" in Cubical Agda.

In this lecture, we will learn about partial elements (open boxes) and
composition (filling those open boxes). Before we dive into all these
cubical features, it will be worth exploring an analogue in the more
familiar Boolean world.


## Warm-up: Boolean Partial Elements

Let's revisit our function ``IsTrue`` which converts a Boolean into a
type. Recall that we defined `IsTrue true` to be ``⊤``, with its
element ``tt`` a proof that ``true`` is in fact ``true``. And we
defined `IsTrue false` to be ``∅``, since there should be no way to
prove that ``false`` is ``true``. Let's give a special name to the
element `tt : IsTrue true` to help us remember. (Yes, this is a bit
silly.)

```
IsTrue-true : IsTrue true
IsTrue-true = tt
```

A *Boolean partial element* of a type `A` is an element of `A` which
exists only conditionally, with the condition being some Boolean `φ`.

```
BooleanPartial : Bool → Type → Type
BooleanPartial φ A = IsTrue φ → A
```

Any actual element of `A` is also a partially defined one: if it
always exists, then it certainly still exists when `φ` happens to be
``true``.

```
just : {A : Type} {φ : Bool} → A → BooleanPartial φ A
just a = λ _ → a
```

And there's always the completely undefined element of `A` which is
defined when ``false`` is ``true``, i.e., never.

```
nothing : {A : Type} → BooleanPartial false A
nothing = ∅-rec
```

Now, you might wonder at the utility of these definitions. After all,
if `φ` is ``true``, then `BooleanPartial φ A` is `⊤ → A`, which is
equivalent to `A`. If `φ` is ``false``, then `BooleanPartial φ A` is `∅
→ A`, which is equivalent to `⊤`. In other words, this type is either
equivalent to `A` or ``⊤``, depending on whether `φ` is ``true`` or
``false`` --- what's the big deal?

The reason that ``BooleanPartial`` is an interesting type is that,
when we use it, we don't think of `φ` as representing a single Boolean
value; we think of `φ` as representing a Boolean *formula*. That is,
we will usually be using this type *in context* and in that case, `φ`
can be some formula involving other Booleans (or other things
entirely).

Consider this function which divides a natural number evenly in two,
for example.

```
halfOf : (n : ℕ) → BooleanPartial (isEven n) ℕ
halfOf zero          = just zero         -- half of 0 is 0
halfOf (suc zero)    = nothing           -- half of 1 is not defined
halfOf (suc (suc n)) = suc ∘ halfOf n    -- half of (n + 2) is one more than half of n
```

This function cannot produce a natural number on every input, since
not every input can be divided evenly in two. We can, however, think
of `halfOf n` as a *partially defined* element of ``ℕ``; specifically,
`halfOf n` is only well-defined when `isEven n` is ``true`` --- or, in
other words, `IsTrue-true : IsTrue (isEven n)` using our definitions
above.

Here's another example of a partially defined element, which shows
what can happen when `φ` is a Boolean formula.

```
zeroOrOne-Partial : (b : Bool) → BooleanPartial (b or (not b)) ℕ
zeroOrOne-Partial true = just zero
zeroOrOne-Partial false = just (suc zero)
```

We can ask whether a partial element `p` *extends* to an fully defined
element `x`. That is, is there an `x : A` so that `p ≡ just x`? In
this case, we say that "`x` *extends* `p`". For ``zeroOrOne-Partial``
we can say the answer is yes.

```
zeroOrOne-Total : Bool → ℕ
zeroOrOne-Total true = zero
zeroOrOne-Total false = suc zero

zeroOrOne-PartialExtends : zeroOrOne-Partial ≡ just ∘ zeroOrOne-Total
zeroOrOne-PartialExtends i true = just zero
zeroOrOne-PartialExtends i false = just (suc zero)
```

In the case of ``halfOf`` above, the answer is no --- not every
natural number can be evenly divided in half.

Here's a practical exercise in Boolean partial functions. Write a
function which takes the first `n` elements of a list, as long as the
list has at least `n` elements.

```
_≤_ : ℕ → ℕ → Bool
zero ≤ m = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

take : (n : ℕ) (L : List A) → BooleanPartial (n ≤ length L) (List A)
-- Exercise:
take n L = {!!}

-- mvrnote: tests
```


## Cubical Partial Elements

Now we come to partial elements defined on intervals. As we saw in
Lecture 2-X, the interval ``I`` has the structure of a De Morgan
algebra. This lets us write down logical formulas with cubical
variables, like `i ∨ (j ∧ ~ k)`. Thinking of ``I`` as the
topological unit interval $[0, 1]$, this formula is meant to represent
the function $\max(x, \min(y, 1 - z))$; thinking logically, it seems
to say "`i` or (`j` and not `k`)". It will be useful to take both
perspectives.

Similarly to the Booleans, we will say that a formula like `i ∨ (j ∧ ~
k)` is "true" when it equals `i1`. This corresponds to a subset of the
cube $[0, 1]³$, namely, the set $$\{ (x, y, z) ∣ \max(x, \min(y, 1 -
z)) = 1 \}.$$ We can therefore think of these interval formulas as
describing "subsets of cubes $I^n$", even though ``I`` isn't actually
a set that we can take subsets of.

For example, the formula `i ∨ ~ i` (which can be read "`i` or not
`i`") should correspond to the subset $\{ x ∈ [0, 1] ∣ \max(x, 1-x) =
1 \}$, which a bit of thinking shows is the subset of the interval
consisting of the endpoints $\{0, 1\} ⊆ [0 , 1]$. We will therefore
think of the formula `i ∨ ~ i` as defining the part of the interval
consisting only of the endpoints ``i0`` and ``i1``.

Since `i ∨ ~ i` is a common pattern, it's reasonable to give it a
name. We call it `∂ i`, since ``∂`` typically means "boundary" in
mathematics.

```
∂ : I → I
∂ i = i ∨ ~ i
```

Corresponding to ``IsTrue`` for Booleans, Agda uses a built-in type
family `I → Type` called ``IsOne`` (roughly). And corresponding to
``BooleanPartial``, Agda provides a primitive type former `Partial φ
A` where `φ : I` is an element of the interval --- thought of as a
formula --- and `A` is a type. Interpreting the formula `φ` as
describing part of a cube, the type `Partial φ A` is then functions
from that piece of the cube to `A`.

We can see that `i ∨ ~ i` really behaves like the endpoints of the
interval by defining a ``Partial`` element on it which sends ``i0`` to
``true`` and ``i1`` to ``false``:

```
trueOrFalse : (i : I) → Partial (i ∨ ~ i) Bool
trueOrFalse i (i = i0) = true
trueOrFalse i (i = i1) = false
```

This uses some built-in Agda syntax to "pattern match" on the hidden
element of `IsOne (i ∨ ~ i)`. Agda checks that all of the formula is
covered, so the above definition fails if one of the lines is omitted.
And in more complicated situations, Agda makes sure that the different
cases are exactly equal wherever they overlap. (We'll see this below.)

We can't turn ``trueOrFalse`` into a *total* element of
``Bool`` which is ``true`` on ``i0`` and ``false``
on ``i1``; there is no way to jump from ``true`` to
``false`` as we move along the interval. (We proved this in
``true≢false``).

But because the partial element only has to be defined on the
endpoints, we can say what the values of ``trueOrFalse`` on those
endpoints are and not worry about what happens in between.

For a more interesting partial element, consider an open box:

        ∙         ∙
        ^         ^              ^    
        |         |            j |        
        |         |              ∙ — >    
        ∙ — — — > ∙                i      

This open box is part of a square, so we are in the context of two
interval variables `i j : I`. Now we need to figure out how to
describe the open box as a formula, which is to say, as a function
into `I`.

```
open-box : I → I → I
open-box i j =
-- (continued below)
```

We want an expression `open-box i j : I` which equals `i1` exactly
when the coordinates `(i, j)` lie on the open box. Now, `i` and `j`
are in the open box if they are in the left of the box, the right of
the box, or the bottom of the box. So our `φ i j` will be the "union"

```
  (right-of-box i j) ∨ (left-of-box i j) ∨ (bottom-of-box i j)
  where
   right-of-box : I → I → I
   left-of-box : I → I → I
   bottom-of-box : I → I → I
```

of those three sides. Now, `(i, j)` is on the right of the box just
when `i = i1`.

```
   right-of-box i j = i
```

Similarly, `(i, j)` is on the left of the box when `i = i0`, or in
other words when `~ i = i1`.

```
   left-of-box i j = ~ i
```

Finally, `(i, j)` is on the bottom of the box when `j = i0`, or when
`~ j = i1`, so

```
   bottom-of-box i j = ~ j
```

This completes our definition of the function `open-box : I → I → I`.
There was no need to split it out, we could have simply written a
single formula

```
open-box' : I → I → I
open-box' i j = (~ i) ∨ i ∨ (~ j)
```

Try it yourself: describe a formula which gives the two sides of a box

        ∙         ∙
        ^         ^              ^
        |         |            j |
        |         |              ∙ — >
        ∙         ∙                i

```
sides-of-square : I → I → I
-- Exercise:
sides-of-square i j = {!!}
```

How about a three dimensional example. Come up with a formula to
describe this part of the cube consisting of the bottom face and the
three sides shown in the picture

                ∙                   ∙
              / ^                 / ^
            /   |               /   |
          /     |             /     |
        ∙ — — — — — — — — > .       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       . — — — — — | — — > ∙
        |     /             |     /
        |   /               |   /
        | /                 | /
        ∙ — — — — — — — — > ∙

```
exercise-shape : I → I → I → I
-- Exercise:
exercise-shape i j k = {!!}
```


## Extensibility and Composition

Just as we did for Boolean partial elements, we can ask whether a
partial element defined on some part of a cube can be extended to the
whole cube. The partial element ``trueOrFalse`` above definitely
cannot extend to a whole element, since a whole element `p i : Bool`
for `i : I` for which `p i0 = true` and `p i1 = false` would be a path
`true ≡ false`, something we've already checked is contradictory in
``true≢false``.

However, Agda bakes in guarantees that certain partial elements can be
extended to total ones. In short, Agda allows us to "close off open
boxes" using an operation called ``hcomp`` (which stands for
"homogeneous composition"). An open box is a part of the cube which
contains the entire bottom face and some pieces of the side walls.

::: Aside:
Every element of a type universe `Type ℓ` is supports ``hcomp``, and
that encompasses almost every type that we use in practice. For
technical reasons, some of Agda's back-end plumbing types do not
support ``hcomp``. The only ones that get mentioned in these notes are
the interval ``I`` itself, the ``IsOne`` predicate, and partial
elements ``PartialP``. The types for which ``hcomp`` works are called
*fibrant* types, taking a name from homotopy theory. The types for
which ``hcomp`` fails live in their own universe hierarchy ``SSet``.
:::

Let's see an example, which implements a crucial operation on paths:
path composition. The most natural notion of path composition in our
cubical setting is "double composition", which composes three paths in
a line

        r         p         q
    w — — — > x — — — > y — — — > z

by drawing them as three sides of a square:

          w         z
          ^         ^            ^
    sym r |         | q        j |
          |         |            ∙ — >
          x — — — > y              i
               p

We can represent this open box as a partial element:

```
double-comp-box : {x y z w : A}
  → (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i j : I) → Partial (open-box i j) A
double-comp-box r p q i j (i = i0) = (sym r) j
double-comp-box r p q i j (i = i1) = q j
double-comp-box r p q i j (j = i0) = p i
```

We want to cap this box to get a path `w ≡ z`. This exactly what
``hcomp`` does: speaking loosely, we have

    hcomp (the formula for where the sides are) 
          (the partial box)
      : (the type of full top face)

For this particular cube we get the "double composite" of the input
paths, which we will write as `r ∙∙ p ∙∙ q`.

```
_∙∙_∙∙_ : (r : w ≡ x) → (p : x ≡ y) → (q : y ≡ z) → w ≡ z
(r ∙∙ p ∙∙ q) i = hcomp (∂ i) (double-comp-box r p q i)
```

Writing more formally, ``hcomp`` takes in two arguments:

* A formula `φ : I`, specifying which sides of the box are going to be
  present in the next argument.
  
  For the double composite, we are specifying the left and right sides
  of the square, that is, the places where where `∂ i` holds.
  
* An open box `box : (j : I) → Partial (φ ∨ ~ j) A`. We can think of
  `box` as specifying a vertical slice of the open box as `j` runs
  from ``i0`` to ``i1``. Each vertical slice will be defined in more
  or fewer places depending on the formula `φ`. When `j` is ``i0``,
  the formula `φ ∨ ~ j` always holds and so these vertical slices are
  all defined when `j = i0`.

  For the double composite, `box j` is totally defined when `i = i0`,
  because we are on the left side of the square in that case, and
  similarly when `i = i1` and we are on the right side of the square.
  Otherwise, we only know for sure that `box j` is defined when `j =
  i0`, in which case we are on the bottom of the square.

And the result is an element `hcomp φ box : A` with the following
guarantee:

* If the formula `φ` holds, then `hcomp φ box` is identical to the
  value of `box i1`, which we know is defined because `box` is known
  to be defined when `φ` holds.

  For the double composite, there are two places where `φ` holds: `i =
  i0` and `i = i1`. When `i = i0`, the value of `box i1` is `(sym r)
  i1 = r i0 = w`. When `i = i1`, the value of `box i1` is `q i1 = z`.

This guarantee is the reason Agda knows that our definition is
actually a path `w ≡ z`!

::: Aside:
We can use a pattern-matching `λ` to inline the definition of the
sides of the box when doing an ``hcomp``. This is the same as
defining the sides separately, it just avoids giving them a name.

```
double-comp-inline : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
double-comp-inline r p q i 
  = hcomp (∂ i) (λ { j (i = i0) → (sym r) j
                   ; j (i = i1) → q j
                   ; j (j = i0) → p i })

_ = λ {A : Type} {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → test-identical 
    (r ∙∙ p ∙∙ q) 
    (double-comp-inline r p q)
```
:::

We are now ready to define ordinary composition of paths.

             p ∙ q
          x ∙ ∙ ∙ > z
          ^         ^            ^
     refl |         | q        j |
          |         |            ∙ — >
          x — — — > y              i
               p

```
infixr 30 _∙_
_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q
```

::: Aside:
It seems like we shouldn't really need to specify the left side of the
box in this definition. The following code seems like a fine way to
define the composite:

```
{- Error!
_∙∙_ : x ≡ y → y ≡ z → x ≡ z
(p ∙∙ q) i = hcomp i (λ { j (i = i1) → q j 
                             ; j (j = i0) → p i })
-}
```

The problem is that when a case is left off like this, Agda fills in
the missing side with another ``hcomp`` of a lower dimension. In
this case, it gives us `hcomp (λ ()) x` in the top left corner.
Unfortunately, this is is not exactly the same as `x`, so this fails
to give us a path `x ≡ z`. This is related to the fact that
transporting over ``refl`` does not give us the identity function
definitionally.
:::


## Constructing Cubes

Let's do an example of a proper 3D cube. Let's say we want to
construct this square:

            q
       y — — — > z
       ^         ^
     p |         | q            ^
       |         |            j |
       x — — — > y              ∙ — >
            p                     i

```
diamond : (p : x ≡ y) (q : y ≡ z) → Square p q p q
```

To construct this via ``hcomp``, we need to cook up a cube (using a
third dimension `k`) with this square as the top face, and where we
know definitions for all the remaining sides.

                          q
                y — — — — — — — — > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x — — — — — — — — > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       ? — — — — — | — — > ?
        |  ?  /             |     /
        |   /               |   /  ?
        | /                 | /
        ? — — — — — — — — > ?
                  ?

We can make some educated guesses about which ``Square`` will work
best as the bottom face. The bottom-left corner should be `x`, because
``refl`` is the only immediately available path that ends in `x`.
Similarly, the two bottom-middle corners should be `x` or `y`. If we
choose `x`, then two of the resulting faces will involve all of `x`,
`y` and `z`, so in the hope of keeping thing simple we go with `y`.
Finally, if the bottom-right corner is `z`, then the bottom face is
exactly the thing we are trying to construct, so to make any progress
we must go with `y`:


                          q
                y — — — — — — — — > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x — — — — — — — — > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       y — — — — — | — — > y
        |  p  /             |     /
        |   /               |   /
        | /                 | /
        x — — — — — — — — > y
                  p

Now we have, in fact, seen all of these faces before! (Review the
interval algebra in Lecture 2-X if necessary.)

```
diamond-tube : {x y z : A} 
  → (p : x ≡ y) → (q : y ≡ z)
  → (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
-- Exercise:
diamond-tube p q i j k (i = i0) = {!!}
diamond-tube p q i j k (i = i1) = {!!}
diamond-tube p q i j k (j = i0) = {!!}
diamond-tube p q i j k (j = i1) = {!!}
diamond-tube p q i j k (k = i0) = {!!}

-- Exercise:
diamond p q i j = hcomp {!!} {!!}
```

The composition problems that result in some desired square are not
unique. Try constructing the same ``diamond`` square as above,
but using the following alternative cube:

                            q
                  y — — — — — — — — > z
            p   / ^             q   / ^
              /   |               /   |
            /     |   p         /     |
          x — — — — — — — — > y       |
          ^       |           ^       | q                  ^   j
          |       |           |       |                  k | /
          |       |           |       |                    ∙ — >
          |       |           |       |                      i
    sym p |       y — — — — — | — — > y
          |     /             |     /
          |   /               |   /
          | /                 | /
          y — — — — — — — — > y

```
diamond-tube-alt : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
-- Exercise:
diamond-tube-alt p q i j k (i = i0) = {!!}
diamond-tube-alt p q i j k (i = i1) = {!!}
diamond-tube-alt p q i j k (j = i0) = {!!}
diamond-tube-alt p q i j k (j = i1) = {!!}
diamond-tube-alt p q i j k (k = i0) = {!!}

diamond-alt : (p : x ≡ y) → (q : y ≡ z) → Square p q p q
diamond-alt p q i j = hcomp (∂ i ∨ ∂ j) (diamond-tube-alt p q i j)
```

A crucial application of ``hcomp`` for 3-d cubes is showing that the
composition square ``double-comp-box`` has a filler. That is, not only
do we have the double-composition path `r ∙∙ p ∙∙ q` at the top, but
the interior of the square is filled in and we have an element of
``Square`` for

               q
          y — — — > z
          ^         ^
       p  |         | r ∙∙ p ∙∙ q          ^
          |         |                    j |
          x — — — > w                      ∙ — >
             sym r                           i

We orient this square in a diagonally flipped way. You will have to
trust us that this is the most convenient orientation to use this
square in!

Here's the cube we want to fill.

                          q
                y — — — — — — — — > z
              / ^                 / ^
         p  /   |               /  r ∙∙ p ∙∙ q
          /     | sym r       /     |
        x — — — — — — — — > w       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       y — — — — — | — — > y
        |  p  /             |     /
        |   /               |   / p
        | /                 | /
        x — — — — — — — — > x

We use a new trick to construct this cube. As mentioned above, if a
face is missing from the partial element then ``hcomp`` fills in the
missing face at the top with an ``hcomp`` of a lower dimension. In the
cube we are trying to construct, the ``hcomp`` of the sides for the
for the `i = i1` face is exactly the double-composite `r ∙∙ p ∙∙ q`
that we wanted as the top edge in the first place. So we don't have to
worry about giving a `i = i1` case at all. (Which is lucky, because
that's exactly the ``Square`` we are trying to construct right now!)

```
∙∙-filler-tube : {w x y z : A}
    (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i j k : I) → Partial (~ i ∨ ∂ j ∨ ~ k) A
-- Exercise:
∙∙-filler-tube r p q i j k (j = i0) = {!!}
∙∙-filler-tube r p q i j k (j = i1) = {!!}
∙∙-filler-tube r p q i j k (i = i0) = {!!}
∙∙-filler-tube r p q i j k (k = i0) = {!!}

∙∙-filler : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → Square p (r ∙∙ p ∙∙ q) (sym r) q
∙∙-filler r p q i j = hcomp (~ i ∨ ∂ j) (∙∙-filler-tube r p q i j)
```

We also have the filler for ordinary composition, just by setting the
path `r` to ``refl``.

               q
          y — — — > z
          ^         ^                   ^    
       p  |         | p ∙ q           j |       
          |         |                   ∙ — >   
          x — — — > x                     i     
             refl                        

```
∙-filler : (p : x ≡ y) (q : y ≡ z) → Square p (p ∙ q) refl q
∙-filler p q = ∙∙-filler refl p q
```


## Properties of Path Composition

Let's set about proving some basic facts about path composition.

First, ``refl`` is the unit for path composition. The fact that
``refl`` can be cancelled on the right is exactly an instance of the
``∙-filler`` square above.

           refl
        y — — — > z
        ^         ^                     ^      
     p  |         | p ∙ refl          j |       
        |         |                     ∙ — >   
        x — — — > w                       i     
           refl                       

```
∙-idr : (p : x ≡ y) → p ≡ p ∙ refl
-- Exercise:
∙-idr p = {!!}
```

::: Aside:
Proving ``∙-idr`` and similar justifies orienting ``∙-filler`` the way
we do: when proving an identity involving paths, we are constructing a
square whose top and bottom are ``refl``. When the right-hand side of
the identity is a composite, it is useful to have the filler oriented
so that the composite is also on the right-hand side.
:::

To cancel ``refl`` on the left, we have to build another cube.

                y — — — — — — — — > y
              / ^                 / ^
         p  /   |               /  refl ∙ p
          /     |             /     |
        x — — — — — — — — > x       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |    sym p  |       |                      i
        |       y — — — — — | — — > x
        |  p  /             |     /
        |   /               |   /
        | /                 | /
        x — — — — — — — — > x


```
∙-idl-tube : {x y : A} (p : x ≡ y) → (i j k : I) → Partial (~ i ∨ ∂ j ∨ ~ k) A
-- Exercise:
∙-idl-tube {x = x} p i j k (i = i0) = {!!} -- Constant in the `k` direction
∙-idl-tube {x = x} p i j k (j = i0) = {!!} -- Completely constant
∙-idl-tube {x = x} p i j k (j = i1) = {!!} -- Constructed from `p` using a connection
∙-idl-tube {x = x} p i j k (k = i0) = {!!} -- Constructed from `p` using connections in a different way

∙-idl : (p : x ≡ y) → p ≡ refl ∙ p
∙-idl {x = x} p i j = hcomp (~ i ∨ ∂ j) (∙-idl-tube p i j)
```

Next, that composing a path with its inverse is equal to ``refl``.

                    x — — — — — — — — > x
                  / ^                 / ^
     p ∙ sym p  /   |               /
              /     |             /     |
            x — — — — — — — — > x       |
            ^       | sym p     ^       |                    ^   j
            |       |           |       |                  k | /
            |       |           |       |                    ∙ — >
            |       |    sym p  |       |                      i
            |       y — — — — — | — — > x
            |  p  /             |     /
            |   /               |   /
            | /                 | /
            x — — — — — — — — > x

Here, the face on the left is exactly the composition square for `p`
and `sym p`, so we can leave it off.

```
∙-invr-tube : {x y : A} (p : x ≡ y) → (i j k : I) → Partial (i ∨ ∂ j ∨ ~ k) A
-- Exercise:
∙-invr-tube {x = x} p i j k (i = i1) = {!!}
∙-invr-tube {x = x} p i j k (j = i0) = {!!}
∙-invr-tube {x = x} p i j k (j = i1) = {!!}
∙-invr-tube {x = x} p i j k (k = i0) = {!!}

∙-invr : (p : x ≡ y) → p ∙ sym p ≡ refl
∙-invr p i j = hcomp (i ∨ ∂ j) (∙-invr-tube p i j) 

∙-invl : (p : x ≡ y) → sym p ∙ p ≡ refl
-- Exercise: (Use symmetry and save work!)
∙-invl p = {!!}
```

Finally, that composition is associative via one final cube.


                      z — — — — — — — — > z
                    / ^                 / ^
     r ∙ (p ∙ q)  /   |               /  (r ∙ p) ∙ q
                /     |             /     |
              w — — — — — — — — > w       |
              ^       |           ^       | q                  ^   j
              |     q |           |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |           |       |                      i
              |       y — — — — — | — — > y
             r ∙ p  /             |     /
              |   /               |   /  r ∙ p
              | /                 | /
              w — — — — — — — — > w

```
∙-assoc-tube : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) A
-- Exercise: (Hint: a couple of cases use ``∙-filler``)
∙-assoc-tube {w = w} r p q i j k (i = i0) = {!!}
∙-assoc-tube {w = w} r p q i j k (i = i1) = {!!}
∙-assoc-tube {w = w} r p q i j k (j = i0) = {!!}
∙-assoc-tube {w = w} r p q i j k (j = i1) = {!!}
∙-assoc-tube {w = w} r p q i j k (k = i0) = {!!}

∙-assoc : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → r ∙ (p ∙ q) ≡ (r ∙ p) ∙ q
∙-assoc r p q i j = hcomp (∂ i ∨ ∂ j) (∙-assoc-tube r p q i j)
```


## Equational Reasoning

As should be familiar from ordinary pen-and-paper mathematics, it is
very useful to produce an equality by chaining together lots of
simpler ones. There is a common Agda pattern that is used to give this
some nice syntax, and the following lines set it up:

```
step-≡ : (x : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

syntax step-≡ x q p = x ≡⟨ p ⟩ q

_∎ : (x : A) → x ≡ x
_ ∎ = refl

infixr 2 step-≡
infix  3 _∎
```

Here's how to use it:

```
private
  example1 : (w x y z : A)
    → (p : w ≡ x)
    → (q : x ≡ y)
    → (r : y ≡ z)
    → w ≡ z
  example1 w x y z p q r =
    w ≡⟨ p ⟩
    x ≡⟨ q ⟩
    y ≡⟨ r ⟩
    z ∎

  example2 : (f : A → B) (g : B → A)
    → (η : (x : A) → x ≡ g (f x))
    → (ε : (y : B) → f (g y) ≡ y)
    → (x : A) → f x ≡ f x
  example2 f g η ε x =
    f x         ≡⟨ ap f (η x) ⟩
    f (g (f x)) ≡⟨ ε (f x) ⟩
    f x         ∎
```

Try it yourself by re-proving a path version of ``+ℕ-≡ℕ-comm``.

```
+ℕ-comm-helper : (n m : ℕ) → (n +ℕ (suc m)) ≡ suc (n +ℕ m)
+ℕ-comm-helper zero m = refl
+ℕ-comm-helper (suc n) m = ap suc (+ℕ-comm-helper n m)

+ℕ-comm : (n m : ℕ) → (n +ℕ m) ≡ (m +ℕ n)
-- Exercise:
+ℕ-comm n zero = +ℕ-idr n
+ℕ-comm n (suc m) =
     n +ℕ suc m   ≡⟨ {!!} ⟩
     suc (n +ℕ m) ≡⟨ {!!} ⟩
     suc (m +ℕ n) ∎
```

And the following lemma about path composition. Each
step will involve a lemma we've proven above.

```
∙l-cancel : (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
-- Exercise:
∙l-cancel p q =
     p ∙ (sym p  ∙ q) ≡⟨ {!!} ⟩
     (p ∙ sym p) ∙ q  ≡⟨ {!!} ⟩
     refl ∙ q         ≡⟨ {!!} ⟩
     q                ∎
```

We encourage you to use this syntax when chaining paths together, it
makes it a lot easier to understand what's going on when you can see
the intermediate points that the composite path is passing through!


## Equivalences Revisited

Now that we have path composition, we can finally prove that
equivalences compose!

This function takes a lot of data as input but the the idea is very
simple: we just compose the provided sections and retracts and use
path composition to combine the provided proofs.

```
∘-isEquiv : (e₁ : B ≃ C) (e₂ : A ≃ B) → isEquiv (e₁ .map ∘ e₂ .map)
∘-isEquiv (packEquiv f₁ g₁ s₁ g'₁ r₁) (packEquiv f₂ g₂ s₂ g'₂ r₂) 
  = packIsEquiv (g₂ ∘ g₁) to-fro (g'₂ ∘ g'₁) fro-to
  where
    to-fro : isSection (f₁ ∘ f₂) (g₂ ∘ g₁)
    -- Exercise:
    to-fro b = f₁ (f₂ (g₂ (g₁ b))) ≡⟨ {!!} ⟩
               f₁         (g₁ b)   ≡⟨ {!!} ⟩
                              b    ∎

_∘e_ : (B ≃ C) → (A ≃ B) → (A ≃ C)
(e₁ ∘e e₂) .map = e₁ .map ∘ e₂ .map
(e₁ ∘e e₂) .proof = ∘-isEquiv e₁ e₂

infixr 9 _∘e_
```

Just as we did for paths, we'll throw in some syntax for chaining
equivalences together.

```
_≃⟨_⟩_ : {B : Type ℓ'} {C : Type ℓ''} (X : Type ℓ) → (X ≃ B) → (B ≃ C) → (X ≃ C)
_ ≃⟨ f ⟩ g = g ∘e f

_∎e : (X : Type ℓ) → (X ≃ X)
_∎e = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _∎e
```

Composition of paths is also enough to let us invert equivalences. The first
step is showing that in the data of an equivalence, the section and
retract functions are in fact equal. Again, we'll explain in
Lecture 2-X why we need to have two different functions in the first
place!

```
sec≡ret : (e : A ≃ B) → (b : B) 
  → e .proof .section .map b ≡ e .proof .retract .map b
sec≡ret (packEquiv f g s g' r) b =
  -- Exercise:
         g b   ≡⟨ {!!} ⟩
  g' (f (g b)) ≡⟨ {!!} ⟩
  g' b         ∎
```

Then, we take the original section as our new function `B → A` and use
the original `f : A → B` as both its section and retract. Showing that
it is a retract is easy: for that we have exactly the original section
proof. Showing that it is a section will require a use of ``sec≡ret``.

```
invEquiv : A ≃ B → B ≃ A
invEquiv (packEquiv f g s g' r) = inv→equiv g f newIsSection s
  where
    newIsSection : isSection g f
    -- Exercise:
    newIsSection a = {!!}
```


## References and Further Reading

https://agda.readthedocs.io/en/latest/language/sort-system.html

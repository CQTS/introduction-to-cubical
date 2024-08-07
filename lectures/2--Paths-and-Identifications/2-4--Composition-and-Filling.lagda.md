```
module 2--Paths-and-Identifications.2-4--Composition-and-Filling where
```


# Lecture 2-4: Composition and Filling

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
    x y z w : A
```
-->

Cubical Agda adds a number of primitive notions that make working with
paths-between-paths easier. To understand how they work, we will
really have to start putting the "cubical" in Cubical Agda.

In this lecture, we will learn about partial elements (open boxes) and
composition (filling those open boxes). To understand how partial
elements work with the interval, it will be worth exploring an
analogue in the more familiar Boolean world.


## Warmup: Boolean Partial Elements

First, let's revisit our function `isTrue : Bool → Type` which
converts a Boolean into a type. Recall that we defined `isTrue true`
to be ``⊤`` --- with its element `tt : ⊤` a proof that `true` is
in fact true --- and we defined `isTrue false` to be ``∅`` ---
since there should be no way to prove that `false` is true. Let's give
a special name to the element `tt : isTrue true` to help us remember.

```
trueIsTrue : IsTrue true
trueIsTrue = tt
```

A Boolean partial element of a type `A` is an element of `A` which
exists only conditionally, with the condition being some Boolean `φ`.

```
BooleanPartial : Bool → Type → Type
BooleanPartial φ A = IsTrue φ → A
```

Any actual element of `A` is also a partially defined one: if it
always exists, then it certainly still exists when `φ` happens to be
true.

```
just : {A : Type} {φ : Bool} → A → BooleanPartial φ A
just a = λ _ → a
```

And there's always the completely undefined element of `A` which is
defined when ``false`` is true, i.e., never.

```
nothing : {A : Type} → BooleanPartial false A
nothing = ∅-rec
```

Now, you might wonder at the utility of these definitions. After all,
if `φ` is `true`, then `BooleanPartial φ A` is `⊤ → A`, which is
equivalent to `A`. If `φ` is `false`, then `BooleanPartial φ A` is `∅
→ A`, which is equivalent to `⊤`. In other words, this type is either
equivalnt to `A` or `⊤`, depending on whether `φ` is `true` or
`false` --- what's the big deal?

The reason that ``BooleanPartial`` is an interesting type is
because when we use it, we don't think of `φ` as representing a single
Boolean value; we think of `φ` as representing a Boolean *formula*.
That is, we will usually be using this type *in context* and in that
case, `φ` can be some formula involving other Booleans (or other
things entirely).

Consider this function which divides a natural number evenly in two,
for example.

```
halfOf : (n : ℕ) → BooleanPartial (isEven n) ℕ
halfOf zero = just zero                  -- half of 0 is 0
halfOf (suc zero) = nothing              -- half of 1 is not defined
halfOf (suc (suc n)) = suc ∘ (halfOf n)  -- half of (n + 2) is one more than half of n.
```

This function cannot produce a natural number on every input, since
not every input can be divided evenly in two. We can, however, think
of `halfOf n` as a partially defined element of ``ℕ``;
specifically, `halfOf n` is a partially defined natural number which
is well defined if `isEven n` is ``true`` - or, in other words,
if we have `trueIsTrue : isTrue (isEven n)`, using our definitions
above.

Here's another example of a partially defined element, which shows
what can happen when `φ` is a Boolean formula.

```
zeroOrOnePartial : (b : Bool) → BooleanPartial (b or (not b)) ℕ
zeroOrOnePartial true = just zero
zeroOrOnePartial false = just (suc zero)
```

We can ask whether a partial element `p` *extends* to an entire (fully
defined) element `x`. That is, is there an `x : A` so that `p ≡ just
x`? In this case, we say that "`x` *extends* `p`". For
``zeroOrOne`` we can say the answer is yes.

```
zeroOrOneTotal : Bool → ℕ
zeroOrOneTotal true = zero
zeroOrOneTotal false = suc zero

zeroOrOnePartialExtends : zeroOrOnePartial ≡ just ∘ zeroOrOneTotal
zeroOrOnePartialExtends i true = just zero
zeroOrOnePartialExtends i false = just (suc zero)
```

In the case of ``halfOf`` above, the answer is no --- not every
natural number can be evenly divided in half.

Here's a fun exercise in Boolean partial functions. Write a function
which takes the first `n` elements of a list --- as long as it has at
least `n` elements.

```
_≤_ : ℕ → ℕ → Bool
zero ≤ m = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

take : (n : ℕ) (L : List A) → BooleanPartial (n ≤ length L) (List A)
-- Exercise:
take n L = {!!}
```


## Partial Elements

Now we come to partial elements defined on intervals. As we saw in
Lecture 2-2, the interval ``I`` has the structure of a De Morgan
algebra. This lets us write down logical formulas with cubical
variables, like `i ∨ (j ∧ ~ k)`. Thinking of ``I`` as the
topological unit interval $[0, 1]$, this formula is meant to represent
the function $\max(x, \min(y, 1 - z))$; thinking logically, it seems
to say "`i` or (`j` and not `k`)". It will be useful to take both
perspectives.

Similarly to the Booleans, we will say that a formula like `i ∨ (j ∧ ~
k)` is "true" when it equals `i1`. This corresponds to a subset of the
cube $[0, 1]³$, namely, the set $\{ (x, y, z) ∣ \max(x, \min(y, 1 - z)) = 1 \}$.
We can therefore think of these interval formulas as
describing "subsets of cubes $I^n$" --- even though ``I`` isn't actually
a set that we can take subsets of.

For example, the formula `i ∨ ~ i` (which can be read "`i` or not `i`")
should correspond to the subset $\{ x ∈ [0, 1] ∣ \max(x, 1-x) = 1 \}$,
which a bit of thinking shows is the set of endpoints $\{0, 1\} ⊆ [0 , 1]$
of the unit interval. We will therefore think of the formula `i
∨ ~ i` as defining the part of the interval consisting only of the
endpoints ``i0`` and ``i1``.

Agda has a primitive type former `Partial φ A` where `φ : I` is an
element of the interval --- but thought of as a formula --- and `A` is
a type. Thinking of `φ` as describing part of a cube, we can think of
`Partial φ A` as the functions from that piece of cube to `A`.

We can see that `i ∨ ~ i` really behaves like the endpoints of the
interval by defining a ``Partial`` element on it which sends
``i0`` to ``true`` and ``i1`` to ``false``:

```
trueOrFalse : (i : I) → Partial (i ∨ ~ i) Bool
trueOrFalse i (i = i0) = true
trueOrFalse i (i = i1) = false
```

We can't turn ``trueOrFalse`` into a *total* element of
``Bool`` which is ``true`` on ``i0`` and ``false``
on ``i1``; there is no way to jump from ``true`` to
``false`` as we move along the interval. (We proved this in
``true≢false``).

But because the partial element only has to be defined on the
endpoints, we can say what the values of ``trueOrFalse`` on those
endpoints are and not worry about what happens in between.

Since `i ∨ ~ i` is a common pattern, it's reasonable to give it a
name. We call it `∂ i`, since ``∂`` typically means "boundary" in
mathematics.

```
∂ : I → I
∂ i = i ∨ ~ i
```

As a more interesting partial element, consider an open box:

        ∙         ∙
        ^         ^
        |         |          ^
        |         |        j |
        ∙ — — — > ∙          ∙ — >
                               i

The open box above is part of a square, so we are in the context of
two interval variables `i j : I`. Now we need to figure out how to
describe the open box as a formula, which is to say, as a function
into `I`.

```
open-box : I → I → I
open-box i j =
-- (continued below)
```

We want an expression `open-box i j : I` which equals `i1` exactly
when the pair of `i` and `j` lies on the open box. Now, `i` and `j`
are in the open box if they are in the left of the box, the right of
the box, or the bottom of the box. So our `φ i j` will be the "union"

```
  (right-of-box i j) ∨ (left-of-box i j) ∨  (bottom-of-box i j)
  where
   right-of-box : I → I → I
   left-of-box : I → I → I
   bottom-of-box : I → I → I
```

of those three sides. Now, `i` and `j` are on the right of the box just
when `i = i1`.

```
   right-of-box i j = i
```

Similarly, `i` and `j` are in the right of the box when `i = i0`, or
in other words when `~ i = i1`.

```
   left-of-box i j = ~ i

```

Finally, `i` and `j` are in the bottom of the box when `j = i0`, or
when `~ j = i1`, so

```
   bottom-of-box i j = ~ j
```

This completes our definition of the function `open-box : I → I → I`.
There was no need to split it out, we could have simply written a
single formula

```
open-box' : I → I → I
open-box' i j = ~ i ∨ i ∨ ~ j
```

Try it yourself: describe a formula which gives the two sides of a box

        ∙         ∙
        ^         ^
        |         |          ^
        |         |        j |
        ∙         ∙          ∙ — >
                               i

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
        ∙ - - - - - - - - > .       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       . - - - - - | - - > ∙
        |     /             |     /
        |   /               |   /
        | /                 | /
        ∙ - - - - - - - - > ∙

```
exercise-shape : I → I → I → I
-- Exercise:
exercise-shape i j k = {!!}
```


## Extensibility and Composition

Just as we did for Boolean partial elements, we can ask whether a
partial element defined on some part of a cube can extend to the whole
cube. The partial element ``trueOrFalse`` above definitely cannot
extend to a whole element, since a whole element `p i : Bool` for `i :
I` for which `p i0 = true` and `p i1 = false` would be a path `true ≡
false`, something we've seen is contradictory.

However, Agda bakes in some guarantees that certain partial elements
can be extended. In short, Agda allows us to "close off open boxes"
using an operation called ``hcomp`` (which stands for
"homogeneous composition"). An open box is a part of the cube which
contains the entire bottom face and some pieces of the side walls.

::: Aside:
The types for which ``hcomp`` works are called *fibrant* types,
taking a name from homotopy theory. Every element of a type universe
`Type ℓ` is fibrant, and that encompasses every type that we use in
practice. Some of Agda's back-end plumbing types are not fibrant ---
they live in a universe called `SSet` for "strict set". We'll see an
example of one of these in a bit.
:::

Let's see an example, which implements a crucial operation on paths:
path composition. The most natural notion of homogeneous path
composition in our cubical setting is "double composition", which
composes three paths in a line:

          w ∙ ∙ ∙ > z
          ^         ^
    sym r |         | q        ^
          |         |        j |
          x — — — > y          ∙ — >
               p                 i

We can represent this open box on the left as a partial element in the
following way:

```
doubleComp-tube : {x y z w : A}
  → (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i j : I) → Partial (open-box i j) A
doubleComp-tube r p q i j (i = i0) = (sym r) j
doubleComp-tube r p q i j (i = i1) = q j
doubleComp-tube r p q i j (j = i0) = p i
```

We want to cap off this box to get a path `w ≡ z`. To do this, we need
to put it in another form which we can apply ``hcomp``. Speaking
loosely, we will have

    hcomp (the sides of the box) (the full bottom face) = (the full top face)

Here, the sides of the box are a partial path in the context of
`i j : I` which is only defined when `i` is either `i0` or `i1`.

          w         z
          ^         ^
    sym r |         | q        ^
          |         |        j |
          x         y          ∙ — >
                                 i

```
doubleComp-sides : {x y z w : A}
  → (r : x ≡ w) (q : y ≡ z)
  → (i j : I) → Partial (∂ i) A
doubleComp-sides r q i j (i = i0) = (sym r) j
doubleComp-sides r q i j (i = i1) = q j
```

The bottom of the box is exactly the path `p`. Now, we use
``hcomp`` to give us the top face of the box; this is exactly the
"double composite" of the input paths.

```
_∙∙_∙∙_ : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
(r ∙∙ p ∙∙ q) i = hcomp (doubleComp-sides r q i) (p i)
```

Writing more formally, ``hcomp`` takes in two arguments
satisfying a side-condition:

* A "partial path" of type `sides : I → Partial φ A`, which we can
  think of as the part of the box that sits over a point on the bottom
  of the box. In the above case, this `doubleComp-sides r q i : I →
  Partial (∂ i) A` is only defined when `i` is `i0` or `i1`.

* A completely defined element `bottom : A` giving a point in the
  bottom of the box, here `p i`.

* These two inputs must be equal where they are both defined. So,
  when we take the sides of the box and plug in `j = i0` (so that
  we're looking at the part of the sides which intersects the bottom),
  the partial element `sides i0 : Partial φ A` of the bottom of the
  box agrees with the completely defined element `bottom : A` we
  already specificed.

  In this case, that means that `doubleComp-sides r q i i0` (an
  element of `Partial (∂ i) A`) has to agree with `p i` when `i = i0`
  or `i = i1`. This happens just at the two lower corners of the
  square, where we did arrange for our paths to line up.

The resulting element `hcomp sides bottom : A` is the point sitting
over `bottom` on the top face of the box.

::: Aside:
We can use a pattern-matching `λ` to inline the definition of the
sides of the box when doing an ``hcomp``. This is the same as
defining the sides separately, it just avoids giving them a name.

```
doubleComp' : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
doubleComp' r p q i = hcomp (λ { j (i = i0) → (sym r) j
                               ; j (i = i1) → q j })
                            (p i)

-- Checking this is identical to the previous definition:
_ : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (r ∙∙ p ∙∙ q) ≡ (doubleComp' r p q)
_ = λ r p q → refl
```
:::

We are now ready to define composition of paths.

             p ∙ q
          x ∙ ∙ ∙ > z
          ^         ^
     refl |         | q        ^
          |         |        j |
          x — — — > y          ∙ — >
               p                 i

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
(p ∙∙ q) i = hcomp (λ { j (i = i1) → q j }) (p i)
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
       y - - - > z
       ^         ^
     p |         | q            ^
       |         |            j |
       x — — — > y              ∙ — >
            p                     i

```
diamond : (p : x ≡ y) (q : y ≡ z) → Square p q p q
```

To construct this via ``hcomp``, we need to cook up a cube (using
our third dimension `k`) with this square as the top face, and where
we know fillers for all the remaining sides.

                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       ? - - - - - | - - > ?
        |  ?  /             |     /
        |   /               |   /  ?
        | /                 | /
        ? - - - - - - - - > ?
                  ?

We can make some educated guesses about what ``Square`` will work
best as the bottom face. The bottom-left corner should be `x`, because
``refl`` is the only immediately available path that ends in `x`.
Similarly, the two bottom-middle corners should be `x` or `y`. If we
choose `x`, then two of the resulting faces will involve all of `x`,
`y` and `z`, so in the hope of keeping thing simpler we go with `y`.
Finally, if the bottom-right corner is `z`, then the bottom face is
exactly the thing we are trying to construct, so to make progress we
must go with `y`:


                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       y - - - - - | - - > y
        |  p  /             |     /
        |   /               |   /
        | /                 | /
        x - - - - - - - - > y
                  p

Now we have, in fact, seen all of these faces before! (Review the
interval section in Lecture 2-2 if necessary.)

```
diamondFaces : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) A
-- Exercise:
diamondFaces p q i j k (i = i0) = {!!}
diamondFaces p q i j k (i = i1) = {!!}
diamondFaces p q i j k (j = i0) = {!!}
diamondFaces p q i j k (j = i1) = {!!}

-- Exercise:
diamond p q i j = hcomp (diamondFaces p q i j) {!!}
```

The composition problems that result in some desired square are not
unique. Try constructing the same ``diamond`` square as above,
but using the following alternative cube:

                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
  sym p |       y - - - - - | - - > y
        |     /             |     /
        |   /               |   /
        | /                 | /
        y - - - - - - - - > y

```
diamondFacesAlt : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) A
-- Exercise:
diamondFacesAlt p q i j k (i = i0) = {!!}
diamondFacesAlt p q i j k (i = i1) = {!!}
diamondFacesAlt p q i j k (j = i0) = {!!}
diamondFacesAlt p q i j k (j = i1) = {!!}

diamondAlt : (p : x ≡ y) (q : y ≡ z) → Square p q p q
diamondAlt {y = y} p q i j = hcomp (diamondFacesAlt p q i j) y
```

A crucial application of ``hcomp`` for cubes is showing that the
composition square has a filler. That is, not only do we have the
double-composition path `r ∙∙ p ∙∙ q`, but the interior of the square
is filled in and we have an element of ``Square`` for

               q
          y - - - > z
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
                y - - - - - - - - > z
              / ^                 / ^
         p  /   |               /  r ∙∙ p ∙∙ q
          /     | sym r       /     |
        x - - - - - - - - > w       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       y - - - - - | - - > y
        |  p  /             |     /
        |   /               |   / p
        | /                 | /
        x - - - - - - - - > x

We use a trick to construct this cube. As mentioned above, if a face
is missing from the partial element then ``hcomp`` fills in the
missing face at the top with an ``hcomp`` of a lower dimension.
In the cube we are trying to construct, the ``hcomp`` of the
sides for the for the `i = i1` face is exactly the double-composite
`r ∙∙ p ∙∙ q` that we wanted as the top edge in the first place. So we
don't have to worry about giving a `i = i1` case at all. (Which is
lucky, because that's exactly the ``Square`` we are trying to
construct right now!)

```
∙∙-filler-faces : {w x y z : A}
    (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i : I) → (j : I) → I → Partial (~ i ∨ ∂ j) A
-- Exercise:
∙∙-filler-faces r p q i j k (j = i0) = {!!}
∙∙-filler-faces r p q i j k (j = i1) = {!!}
∙∙-filler-faces r p q i j k (i = i0) = {!!}

∙∙-filler : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → Square p (r ∙∙ p ∙∙ q) (sym r) q
-- Exercise:
∙∙-filler r p q i j = hcomp (∙∙-filler-faces r p q i j) {!!}
```

We also have the filler for ordinary composition, just by setting the
path `r` to ``refl``.

               q
          y - - - > z
          ^         ^
       p  |         | p ∙ q                ^
          |         |                    j |
          x — — — > x                      ∙ — >
             refl                            i

```
∙-filler : (p : x ≡ y) (q : y ≡ z) → Square p (p ∙ q) refl q
∙-filler p q = ∙∙-filler refl p q
```


## Properties of Path Composition

Let's set about proving some basic facts about path composition.

First, that ``refl`` is the unit for path composition. The fact
that ``refl`` can be cancelled on the right is exactly one of the
above filler squares.

           refl
        y - - - > z
        ^         ^
     p  |         | p ∙ refl             ^
        |         |                    j |
        x — — — > w                      ∙ — >
           refl                            i

```
rUnit : (p : x ≡ y) → p ≡ p ∙ refl
rUnit p i j = ∙-filler p refl i j
```

::: Aside:
Proving ``rUnit`` and similar justifies why we orient
``∙-filler`` the way we do: when proving an identity involving
paths, we are constructing a square whose top and bottom are
``refl``. When the right-hand side of the identity is a
composite, it is useful to have the filler oriented so that the
composite is also on the right-hand side.
:::

To cancel ``refl`` on the left, we have to build another cube.

                y - - - - - - - - > y
              / ^                 / ^
         p  /   |               /  refl ∙ p
          /     |             /     |
        x - - - - - - - - > x       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |    sym p  |       |                      i
        |       y - - - - - | - - > x
        |  p  /             |     /
        |   /               |   /
        | /                 | /
        x - - - - - - - - > x


```
lUnit-faces : {x y : A} (p : x ≡ y) → (i : I) → (j : I) → (k : I) → Partial (~ i ∨ ∂ j) A
-- Exercise:
lUnit-faces {x = x} p i j k (i = i0) = {!!} -- Constant in the `k` direction
lUnit-faces {x = x} p i j k (j = i0) = {!!} -- Completely constant
lUnit-faces {x = x} p i j k (j = i1) = {!!} -- Constructed from `p` using a connection

lUnit-base : {x y : A} (p : x ≡ y) → Square p refl refl (sym p)
-- Exercise: (Hint: Constructed from `p` using connections in a different way)
lUnit-base p i j = {!!}

lUnit : (p : x ≡ y) → p ≡ refl ∙ p
lUnit {x = x} p i j = hcomp (lUnit-faces p i j) (lUnit-base p i j)
```

Next, that composing a path with its inverse is equal to ``refl``.

                    x - - - - - - - - > x
                  / ^                 / ^
     p ∙ sym p  /   |               /
              /     |             /     |
            x - - - - - - - - > x       |
            ^       | sym p     ^       |                    ^   j
            |       |           |       |                  k | /
            |       |           |       |                    ∙ — >
            |       |    sym p  |       |                      i
            |       y - - - - - | - - > x
            |  p  /             |     /
            |   /               |   /
            | /                 | /
            x - - - - - - - - > x

Here, the face on the left is exactly the composition square for `p`
and `sym p`, so we can leave it off.

```
rCancel-faces : {x y : A} (p : x ≡ y) → (i : I) → (j : I) → (k : I) → Partial (i ∨ ∂ j) A
-- Exercise:
rCancel-faces {x = x} p i j k (i = i1) = {!!}
rCancel-faces {x = x} p i j k (j = i0) = {!!}
rCancel-faces {x = x} p i j k (j = i1) = {!!}

rCancel : (p : x ≡ y) → p ∙ sym p ≡ refl
-- Exericse: (This is the same base square as an earlier one.)
-- rCancel p i j = hcomp (rCancel-faces p i j) {!!}
rCancel p i j = hcomp (rCancel-faces p i j) (p (~ i ∧ j))

lCancel : (p : x ≡ y) → sym p ∙ p ≡ refl
-- Exercise: (Use symmetry and save work!)
lCancel p = {!!}
```

Finally, that composition is associative, via one final cube.


                      z - - - - - - - - > z
                    / ^                 / ^
     r ∙ (p ∙ q)  /   |               /  (r ∙ p) ∙ q
                /     |             /     |
              w - - - - - - - - > w       |
              ^       |           ^       | q                  ^   j
              |     q |           |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |           |       |                      i
              |       y - - - - - | - - > y
             r ∙ p  /             |     /
              |   /               |   /  r ∙ p
              | /                 | /
              w - - - - - - - - > w

```
assoc-faces : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (i : I) → (j : I) → (k : I) → Partial (∂ i ∨ ∂ j) A
-- Exercise: (Hint: a couple of cases use `∙-filler`)
assoc-faces {w = w} r p q i j k (i = i0) = {!!}
assoc-faces {w = w} r p q i j k (i = i1) = {!!}
assoc-faces {w = w} r p q i j k (j = i0) = {!!}
assoc-faces {w = w} r p q i j k (j = i1) = {!!}

assoc-base : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → Square (r ∙ p) (r ∙ p) refl refl
-- Exercise:
assoc-base r p q i j = {!!}

assoc : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → r ∙ (p ∙ q) ≡ (r ∙ p) ∙ q
assoc r p q i j = hcomp (assoc-faces r p q i j) (assoc-base r p q i j)
```


## Equational Reasoning

As should be familiar from ordinary pen-and-paper mathematics, it is
very useful to produce an equality by chaining together lots of
simpler ones. There is a common Agda pattern that is used to give this
some nice syntax.

```
infix  3 _∎
infixr 2 step-≡ _≡⟨⟩_

step-≡ : (x : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

syntax step-≡ x y p = x ≡⟨ p ⟩ y

_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_∎ : (x : A) → x ≡ x
_ ∎ = refl
```

Here's how to use it. mvrnote: 1lab hides the paths, need to switch
the default

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
    f x         ≡⟨ cong f (η x) ⟩
    f (g (f x)) ≡⟨ ε (f x) ⟩
    f x         ∎
```

Try it yourself with this little fact about path composition. Each
step will involve some lemma we've proven above concerning paths.

```
∙l-cancel : (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
-- Exercise:
∙l-cancel p q
     =  p ∙ (sym p ∙ q) ≡⟨ {!!} ⟩
       (p ∙ sym p) ∙ q  ≡⟨ {!!} ⟩
        refl ∙ q        ≡⟨ {!!} ⟩
        q ∎
```

We encourage you to use this syntax when chaining paths together, it
makes it a lot easier to understand what's going on when you can see
the intermediate points that the composite path is passing through!


## Equivalences Revisited

Now that we have path composition, we can finally prove that
equivalences compose! In fact it is not hard to prove a little more.
Equivalences satisfy the *2-out-of-3 property*, which states that
whenever two out of `f`, `g` and `g ∘ f` are equivalences, so is the
third.

There are a lot of arguments to these function, but the ideas are very
simple: we just compose the provided sections and retractions, and use
path composition to combine the provided proofs.

```
module _ (f₁ : B → C) (f₂ : A → B)  where
  ≃-2-out-of-3-comp : isEquiv f₁ → isEquiv f₂ → isEquiv (f₁ ∘ f₂)
  ≃-2-out-of-3-comp ((g₁ , s₁) , (g'₁ , r₁)) ((g₂ , s₂) , (g'₂ , r₂))
    = (g₂ ∘ g₁  , to-fro) , (g'₂ ∘ g'₁ , fro-to)
      where
        to-fro : isSection (f₁ ∘ f₂) (g₂ ∘ g₁)
        -- Exercise:
        to-fro b = f₁ (f₂ (g₂ (g₁ b))) ≡⟨ {!!} ⟩
                   f₁         (g₁ b)   ≡⟨ {!!} ⟩
                                  b    ∎

        fro-to : isRetract (f₁ ∘ f₂) (g'₂ ∘ g'₁)
        -- Exercise:
        fro-to a = g'₂ (g'₁ (f₁ (f₂ a))) ≡⟨ {!!} ⟩
                   g'₂          (f₂ a)   ≡⟨ {!!} ⟩
                                    a    ∎

  ≃-2-out-of-3-left : isEquiv f₁ → isEquiv (f₁ ∘ f₂) → isEquiv f₂
  ≃-2-out-of-3-left ((g₁ , s₁) , (g'₁ , r₁)) ((g₁₂ , s₁₂) , (g'₁₂ , r₁₂))
    = ( g₁₂ ∘ f₁  , to-fro) , (g'₁₂ ∘ f₁ , r₁₂)
      where
        to-fro : isSection f₂ (g₁₂ ∘ f₁)
        -- Exercise:
        to-fro b =          f₂ (g₁₂ (f₁ b))   ≡⟨ {!!} ⟩
                   g'₁ (f₁ (f₂ (g₁₂ (f₁ b)))) ≡⟨ {!!} ⟩
                   g'₁ (f₁              b)    ≡⟨ {!!} ⟩
                                        b     ∎

  ≃-2-out-of-3-right : isEquiv f₂ → isEquiv (f₁ ∘ f₂) → isEquiv f₁
  ≃-2-out-of-3-right ((g₁ , s₁) , (g'₁ , r₁)) ((g₁₂ , s₁₂) , (g'₁₂ , r₁₂))
    = ( f₂ ∘ g₁₂  , s₁₂) , (f₂ ∘ g'₁₂ , fro-to)
      where
        fro-to : isRetract f₁ (f₂ ∘ g'₁₂)
        -- Exercise:
        fro-to b = f₂ (g'₁₂ (f₁         b))   ≡⟨ {!!} ⟩
                   f₂ (g'₁₂ (f₁ (f₂ (g₁ b)))) ≡⟨ {!!} ⟩
                   f₂               (g₁ b)    ≡⟨ {!!} ⟩
                   b                          ∎

compEquiv : (B ≃ C) → (A ≃ B) → (A ≃ C)
compEquiv (f₁ , e₁) (f₂ , e₂) = f₁ ∘ f₂ , ≃-2-out-of-3-comp f₁ f₂ e₁ e₂
```

Composition also lets us invert equivalences. mvrnote: more txt.

```
sec≡ret : (e : A ≃ B) → (b : B) → equivSec e b ≡ equivRet e b
sec≡ret (f , (g , s) , (g' , r)) b =
         g b   ≡⟨ sym (r (g b)) ⟩
  g' (f (g b)) ≡⟨ cong g' (s b) ⟩
  g' b         ∎

invEquiv : A ≃ B → B ≃ A
invEquiv (f , (g , s) , (g' , r)) = equiv g f newIsSec s
  where newIsSec : isSection g f
        newIsSec a = g  (f a) ≡⟨ sec≡ret (f , (g , s) , (g' , r)) (f a) ⟩
                     g' (f a) ≡⟨ r a ⟩
                           a  ∎
```

mvrnote: congPathIso could be another (extended) exercise, or put in extras?


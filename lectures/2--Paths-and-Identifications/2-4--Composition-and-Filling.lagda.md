```
module 2--Paths-and-Identifications.2-4--Composition-and-Filling where
```


# Lecture 2-4: Composition and Filling

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-X--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
    x y z w : A
```
-->

Cubical Agda adds a number of primitive notions that make working with
paths between paths easier. To understand how they work, we will
really have to start putting the "cubical" in Cubical Agda.

In this lecture, we will learn about partial elements (open boxes) and
composition (filling boxes). But to understand how partial elements
work with the interval, it will be worth exploring an analogue in the
more familiar Boolean world.


## Warmup: Boolean Partial Elements

First, let's revisit our function `isTrue : Bool → Type` which
converted a Boolean into a type. Recall that we defined `isTrue true`
to be `⊤` --- with its element `tt : ⊤` proving that `true` is true
--- and we defined `isTrue false` to be `∅` --- since there should be
no way to prove that `false` is true. Let's give a special name to the
element `tt : isTrue true` to help us remember.

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
defined when `false`{.Agda} is true, i.e., never.

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

The reason that `BooleanPartial`{.Agda} is an interesting type is
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
of `halfOf n` as a partially defined element of `ℕ`{.Agda};
specifically, `halfOf n` is a partially defined natural number which
is well defined if `isEven n`{.Agda} is `true`{.Agda} - or, in other words,
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
`zeroOrOne`{.Agda} we can say the answer is yes.

```
zeroOrOneTotal : Bool → ℕ
zeroOrOneTotal true = zero
zeroOrOneTotal false = suc zero

doesItExtend : zeroOrOnePartial ≡ just ∘ zeroOrOneTotal
doesItExtend i true = just zero
doesItExtend i false = just (suc zero)
```

In the case of `halfOf`{.Agda} above, the answer is no --- not every
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
Lecture 2-2, the interval `I`{.Agda} has the structure of a De Morgan
algebra. This lets us write down logical formulas with cubical
variables, like `i ∨ (j ∧ ~ k)`. Thinking of `I`{.Agda} as the
topological unit interval $[0, 1]$, this formula is meant to represent
the function $\max(x, \min(y, 1 - z))$; thinking logically, it seems
to say "`i` or (`j` and not `k`)". It will be useful to take both
perspectives.

Similarly to the Booleans, we will say that a formula like `i ∨ (j ∧ ~
k)` is "true" when it equals `i1`. This corresponds to a subset of the
cube $[0,1]³$, namely, the set $\{ (x, y, z) ∣ \max(x, \min(y, 1 - z)) = 1 \}$.
We can therefore think of these interval formulas as
describing "subsets of cubes $I^n$" --- even though `I` isn't actually
a set that we can take subsets of.

For example, the formula `i ∨ ~ i` (which can be read "`i` or not `i`")
should correspond to the subset $\{ x ∈ [0, 1] ∣ \max(x, 1-x) = 1 \}$,
which a bit of thinking shows is the set of endpoints $\{0, 1\} ⊆ [0 , 1]$
of the unit interval. We will therefore think of the formula `i
∨ ~ i` as defining the part of the interval consisting only of the
endpoints `i0` and `i1`.

Agda has a primitive type former `Partial φ A` where `φ : I` is an
element of the interval --- but thought of as a formula --- and `A` is
a type. Thinking of `φ` as describing part of a cube, we can think of
`Partial φ A` as the functions from that piece of cube to `A`.

We can see that `i ∨ ~ i` really behaves like the endpoints of the
interval by defining a `Partial`{.Agda} element on it which sends
`i0`{.Agda} to `true`{.Agda} and `i1`{.Agda} to `false`{.Agda}:

```
trueOrFalse : (i : I) → Partial (i ∨ ~ i) Bool
trueOrFalse i (i = i0) = true
trueOrFalse i (i = i1) = false
```

We can't turn `trueOrFalse`{.Agda} into a *total* element of
`Bool`{.Agda} which is `true`{.Agda} on `i0`{.Agda} and `false`{.Agda}
on `i1`{.Agda}; there is no way to jump from `true`{.Agda} to
`false`{.Agda} as we move along the interval (as we proved in
`true≢false`{.Agda}). But because the partial element only has to be
defined on the endpoints, we can say what the values of
`trueOrFalse`{.Agda} on those endpoints are and not worry about what
happens in between.

Since `i ∨ ~ i` is a common pattern, it's reasonable to give it a
name. We call it `∂ i`, since `∂`{.Agda} typically means "boundary" in
mathematics.

```
∂ : I → I
∂ i = i ∨ ~ i
```

As a more interesting partial element, consider an open box:


        .         .
        ^         ^
        |         |          ^
        |         |        j |
        . — — — > .          ∙ — >
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

We want an expression `open-box i j : I` which equals `i1` just when
`i` and `j` are constrained to be in the open box. Now, `i` and `j`
are in the open box if they are in the left of the box, the right of
the box, or the bottom of the box. So our `φ i j` will be the "union"

```
  (left-of-box i j) ∨ (right-of-box i j) ∨ (bottom-of-box i j)
  where
   left-of-box : I → I → I
   right-of-box : I → I → I
   bottom-of-box : I → I → I
```

Now, `i` and `j` are in the left of the box just when `i = i0`, or in
other words when `~ i = i1`. So

```
   left-of-box i j = ~ i
```

Similarly, `i` and `j` are in the right of the box when `i = i1`, so

```
   right-of-box i j = i
```

Finally, `i` and `j` are in the bottom of the box when `j = i0`, or
when `~ j = i1`, so

```
   bottom-of-box i j = ~ j
```

This completes our definition of the function `open-box : I → I → I`:
`open-box i j = ~ i ∨ i ∨ ~ j`.

Try it yourself: describe a formula which gives the two sides of a box

        .         .
        ^         ^
        |         |          ^
        |         |        j |
        .         .          ∙ — >
                               i

```
sides-of-square : I → I → I
-- Exercise:
sides-of-square i j = {!!}
```

How about a three dimensional example. Come up with a formula to
describe this part of the cube consisting of the bottom face and three
of the sides.

                .                   .
              / ^                 / ^
            /   |               /   |
          /     |             /     |
        . - - - - - - - - > .       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       . - - - - - | - - > .
        |     /             |     /
        |   /               |   /
        | /                 | /
        . - - - - - - - - > .

```
exercise-shape : I → I → I → I
-- Exercise:
exercise-shape i j k = {!!}
```


## Extensibility and Composition

As with Boolean partial elements we can ask whether a partial element
defined on some part of a cube can extend to the whole cube. The
partial element `trueOrFalse`{.Agda} above definitely cannot extend to
a whole element, since a whole element `p i : Bool` for `i : I` for
which `p i0 = true` and `p i1 = false` would be a path `true ≡ false`
--- and this would give us an element of the empty type!

However, Agda bakes in some guarantees that a partial element can be extended.
In short, Agda allows us to "close off open boxes" using an operation called
`hcomp`{.Agda} (which stands for "homogeneous composition"). An open box is a
part of the cube which contains the entire bottom face.

Aside: It's worth noting that we can't extend a partial element using
`hcomp` in *any* type. The types for which `hcomp` works are called
*fibrant* types, taking a name from homotopy theory. Essentially all
the types we use in practice are fibrant; every element of a type
universe `Type ℓ` is fibrant. But some back-end plumbing types are not
fibrant --- they live in a universe called `SSet` for "strict set".
We'll see an example in a bit.

Let's see an example, which will also be an important operations on
paths: path composition. The most natural notion of homogeneous path
composition in a cubical setting is double composition which composes
three paths in a line:

          w ∙ ∙ ∙ > z
          ^         ^
    sym r |         | q        ^
          |         |        j |
          x — — — > y          ∙ — >
               p                 i

We can represent this open box on the left as a partial element in the
following way:

```
doubleComp-tube : {A : Type ℓ} {x y z w : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                   (i j : I) → Partial (open-box i j) A
doubleComp-tube r p q i j (i = i0) = (sym r) j
doubleComp-tube r p q i j (i = i1) = q j
doubleComp-tube r p q i j (j = i0) = p i
```

We want to cap off this box to get a path `w ≡ z`. To do this, we need
to put it in another form which we can apply `hcomp`{.Agda}. Speaking
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
doubleComp-sides : {x y z w : A } (r : x ≡ w) (q : y ≡ z)
                   (i j : I) → Partial (∂ i) A
doubleComp-sides r q i j (i = i0) = (sym r) j
doubleComp-sides r q i j (i = i1) = q j
```

The bottom of the box is `p`. Therefore, we can use `hcomp`{.Agda} to
close off the box. We will call the top of this particular box the
"double composite".

```
_∙∙_∙∙_ : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
(r ∙∙ p ∙∙ q) i = hcomp (doubleComp-sides r q i) (p i)
```

Here we can see what `hcomp`{.Agda} really takes as input: first, a
"partial path" of types `I → Partial φ A` which we can think of as the
side of the box that sits over a point on the bottom of the box. In
this case, this is `doubleComp-sides r q i : I → Partial (∂ i) A`
which is the side of the box (going up vertically) which sits over the
point indexed by `i` on the bottom of the box.

Second, `hcomp`{.Agda} takes a (completely defined) element of the
bottom of the box, here `p i`. Agda will check that these two inputs
match up, which means that when we take the sides of the box and plug
in `j = i0` (so that we're looking at the part of the sides which
intersects the bottom), the partial element `Partial φ A` of the
bottom of the box that we get agrees with the completely defined
element we already specificed

In this case, that means that `doubleComp-sides r q i i0` (an element
of `Partial (∂ i) A`) has to agree with `p i` on `∂ i`, which is to
say when `i = i0` or `i = i1`: the two lower corners of the square.
This obviously works in our case since `doubleComp-sides r q i i0` is
by definition `p i` --- though remember that this was `p i : Partial
(∂ i) A`, which is to say it's the partial element `p i` defined only
when `i = i0` or `i = i1`.

We can use a pattern-matching anonymous function to inline the
definition of the sides of the box when doing an `hcomp`{.Agda}. This
is the same as defining the sides separately, just without
giving them a name.

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

More formally we can see that `hcomp`{.Agda} takes in two arguments:

* A partially defined path, representing the part of the box sitting
  over a point in the bottom face. Above, this is `doubleComp-sides r
  q i : (j : I) → Partial (∂ i) A`, which is a path in `A` that is
  only defined when `i` is `i0` or `i1`.

* A element of `A` giving a point in the bottom of the box. 

The result `hcomp sides bottom` is the point sitting over `bottom` in the top of
the box.

We can produce a filler for the whole square using an additional
function called `hfill`{.Agda}. As a picture, this is giving us the
interior of the square

            r ∙∙ p ∙∙ q
          w - - - - - - > z
          ^               ^
    sym r |  ...-filler   | q        ^
          |               |        j |
          x - — — — - - > y          ∙ — >
                  p                    i

```
doubleCompPath-filler' : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                      → Square (sym r) q p (r ∙∙ p ∙∙ q)
doubleCompPath-filler' r p q i j =
  hfill (doubleComp-sides r q i) (inS (p i)) j
```

As you can see, the `hfill`{.Agda} here at first takes in the same two
arguments as the `hcomp`{.Agda} we used, and then the interval
variable in the direction we are trying to fill. But there is
something interesting in the second argument: `inS`{.Agda}. To
understand what `inS`{.Agda} is, we need to discuss extension types.

If `φ` is a formula and `u : Partial φ A` is a partial element, then
we can form the extension type `A [ φ ↦ u ]` which is the type of all
*completely defined* elements of `A` that are definitionally equal to
`u` when the formula `φ` holds. In other words, an element of `A [ φ ↦
u ]` is an element of `A` about which we know some definitional
constraints. Extension types are not *fibrant* types, meaning that we
can't use `hcomp`{.Agda} in them. They are really a part of the
back-end cubical plumbing.

We've seen types that work like this before: paths! A path `p : x ≡ y`
is a function `I → A` about which we have the additional information
that `p i0 = x` and `p i1 = y`. Using extension types, we could write
this as

```
Path-ish : ∀ {A} (endpoints : (i : I) → Partial (∂ i) A) → SSet
Path-ish {A} endpoints = (i : I) → A [ ∂ i ↦ endpoints i ]
```

Given a partial element `e : (i : I) → Partial (∂ i) A` defined only
when `i = i0` or `i = i1` --- the endpoints of our path --- we get a
"strict set" (element of `SSet`) consisting of the functions
`p : I → A" where by definition `p i0 = endpoints i0` and
`p i1 = endpoints i1`.

The actual path type isn't exactly the same thing as our
`Path-ish`{.Agda} above, for the simple reason that, due to some Agda
magic, path types *are* fibrant; we have `x ≡ y : Type` rather than `SSet`.

Now we can come to `inS`. This is the function that takes a full
element `a : A` and gives us `inS a : A [ φ ↦ (λ _ → a) ]`. In other
words, it tells us that any full element can be seen as the extension
of any partial restriction of it.

Finally, we can understand the type of `hfill`. We have, roughly speaking,

    hfill (the partially defined side of the box over a point in the base)
          (a completely defined element of the base matching the bottom of the sides)
          (an element of the interval, "pointing up")

For reasons that will become clear later, we will orient our `doubleCompPath-filler`{.Agda}
in a diagonally flipped way. 
               q
          y - - - > z
          ^         ^
       p  |         | r ∙∙ p ∙∙ q          ^
          |         |                    j |
          x — — — > w                      ∙ — >
             sym r                           i
```
doubleCompPath-filler : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                      → Square p (r ∙∙ p ∙∙ q) (sym r) q
doubleCompPath-filler r p q j i =
  hfill (doubleComp-sides r q i) (inS (p i)) j
```

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

Remark: it seems like we shouldn't really need to use the left side of
the box in this definition. The following code should be a fine way to
define the composite:

```
{- Error!
_∙∙_ : x ≡ y → y ≡ z → x ≡ z
(p ∙∙ q) i = hcomp (λ { j (i = i1) → q j }) (p i)
-}
```

The problem here is that this also has to fill in the left side of the
box, and when it does it gets `hcomp (λ ()) x` in the top left corner.
This is not by definition exactly the same as `x`, so this fails to give us a path `x ≡ z`.
This is related to the fact that transporting over `refl`{.Agda}
does not give us the identity function definitionally.

We also have the filler for composition (which is also diagonally
flipped for the same reason.)

               q
          y - - - > z
          ^         ^
       p  |         | p ∙ q                ^
          |         |                    j |
          x — — — > x                      ∙ — >
             refl                            i

```
compPath-filler : (p : x ≡ y) (q : y ≡ z) → Square p (p ∙ q) refl q
compPath-filler p q = doubleCompPath-filler refl p q
```

## Constructing Cubes

Let's do an example of a (3D) cube. Let's say we want to construct
this square:

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

To construct this via an `hcomp`{.Agda}, we need to cook up a cube
(using an extra dimension `k`) with this square as the top face, and
where we know fillers for all the remaining sides.

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

We can make some educated guesses about what will work as the bottom
face. The bottom-left corner should be `x`, because `refl` is the only
immediately available path that ends in `x`. Similarly, the two
bottom-middle corners should be `x` or `y`. If we choose `x`, then two
of the resulting faces will involve all of `x`, `y` and `z`, so in the
hope of keeping thing simpler we go with `y`. Finally, if the
bottom-right corner is `z`, then the bottom face is exactly the thing
we are trying to construct, so to make progress we must go with `y`:


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

Now we have, in fact, seen all of these faces before.

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

This is not the only way to do it! The composition problems that
result in some desired square are not unique. Try constructing the
same `diamond` square, but using the following cube:

                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | p ∙ q              ^   j
        |       | p         |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           | p     |                      i
        |       x - - - - - | - - > x
        |     /             |     /
        |   /               |   /
        | /                 | /
        x - - - - - - - - > x


```
diamondFacesAlt : {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) A
-- Exercise:
diamondFacesAlt p q i j k (i = i0) = {!!}
diamondFacesAlt p q i j k (i = i1) = {!!}
diamondFacesAlt p q i j k (j = i0) = {!!}
diamondFacesAlt p q i j k (j = i1) = {!!}

diamondAlt : (p : x ≡ y) (q : y ≡ z) → Square p q p q
diamondAlt {x = x} p q i j = hcomp (diamondFacesAlt p q i j) x
```

Let's set about proving associativity for path composition. To do
this, we will use the same trick as above and construct a cube whose
top face is the path-between-paths that we want.

                              refl
                      z - - - - - - - - > z
                    / ^                 / ^
     r ∙ (p ∙ q)  /   |               /  (r ∙ p) ∙ q
                /     | refl        /     |
              w - - - - - - - - > w       |
              ^       |           ^       | q                  ^   j
              |     q |           |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |   refl    |       |                      i
              |       y - - - - - | - - > y
             r ∙ p  /             |     /
              |   /               |   /  r ∙ p
              | /                 | /
              w - - - - - - - - > w
                      refl

```
assoc-faces : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → (i : I) → (j : I) → (k : I) → Partial (∂ i ∨ ∂ j) A
-- Exercise:
assoc-faces         r p q i j k (i = i0) = {!!}
assoc-faces         r p q i j k (i = i1) = {!!}
assoc-faces {w = w} r p q i j k (j = i0) = {!!}
assoc-faces         r p q i j k (j = i1) = {!!}

assoc-base : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → Square (r ∙ p) (r ∙ p) refl refl
-- Exercise:
assoc-base r p q i j = {!!}

assoc : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → r ∙ (p ∙ q) ≡ (r ∙ p) ∙ q
assoc r p q i j = hcomp (assoc-faces r p q i j) (assoc-base r p q i j)
```

We can also prove that `refl`{.Agda} is the unit for path composition.
The fact that `refl`{.Agda} can be cancelled on the right is exactly
one of the above filler squares.

           refl
        y - - - > z
        ^         ^
     p  |         | p ∙ refl             ^
        |         |                    j |
        x — — — > w                      ∙ — >
           refl                            i
```
rUnit : (p : x ≡ y) → p ≡ p ∙ refl
rUnit p i j = compPath-filler p refl i j
```

Proving `rUnit`{.Agda} should make it clear why we oriented
`compPath-filler`{.Agda} the way we did: when proving an identity involving
paths, we are constructing a square whose top and bottom are refl. When the
right hand side of the identity is a composite, it is useful to have our filler
oriented so that the composite is also on the right hand side.

To cancel on the left we have to build another cube.

                y - - - - - - - - > y
              / ^                 / ^
         p  /   |               /  refl ∙ p
          /     |             /     |
        x - - - - - - - - > x       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |   sym p   |       |                      i
        |       y - - - - - | - - > x
        |  p  /             |     /
        |   /               |   / refl
        | /                 | /
        x - - - - - - - - > x
                refl

The faces are straightforward to construct if you stare at the diagram.
```
lUnit-faces : {x y : A} (p : x ≡ y) → (i : I) → (j : I) → (k : I) → Partial (~ i ∨ ∂ j) A
-- Exercise:
lUnit-faces         p i j k (i = i0) = {!!} -- Constant in the `j` direction
lUnit-faces {x = x} p i j k (j = i0) = {!!} -- Completely constant
lUnit-faces         p i j k (j = i1) = {!!} -- Constructed from `p` using connections

lUnit-base : {x y : A} (p : x ≡ y) → Square p refl refl (sym p)
-- Exercise:
lUnit-base p i j = {!!}
Hint: Constructed from `p` using connections in a different way

lUnit : (p : x ≡ y) → p ≡ refl ∙ p
lUnit {x = x} p i j = hcomp (lUnit-faces p i j) (lUnit-base p i j)
```

mvrnote: copied from the cubical library
```
rCancel-filler : ∀ {x y : A} (p : x ≡ y) → (k j i : I) → A
rCancel-filler {x = x} p k j i =
  hfill (λ k → λ { (i = i0) → x
                  ; (i = i1) → p (~ k ∧ ~ j)
               -- ; (j = i0) → compPath-filler p (p ⁻¹) k i
                  ; (j = i1) → x
                  }) (inS (p (i ∧ ~ j))) k

rCancel : (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel {x = x} p j i = rCancel-filler p i1 j i

rCancel-filler' : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → (i j k : I) → A
rCancel-filler' {x = x} {y} p i j k =
  hfill
    (λ i → λ
      { (j = i1) → p (~ i ∧ k)
      ; (k = i0) → x
      ; (k = i1) → p (~ i)
      })
    (inS (p k))
    (~ i)

rCancel' : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel' p j k = rCancel-filler' p i0 j k

lCancel : (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel p = rCancel (sym p)
```

## Equivalences Revisited

mvrnote: outdated prose

```
module _ (e : A ≃ B) where
  private
    f : A → B
    f = equivFun e
  
    s : B → A
    p : (b : B) → f (s b) ≡ b
    s = fst (equivSec e)
    p = snd (equivSec e)
    
    r : B → A
    q : (a : A) → r (f a) ≡ a
    r = fst (equivRet e)
    q = snd (equivRet e)

  equivSec≡Ret : (b : B) → s b ≡ r b
  -- Exercise: mvrnote
  
  invEquiv : B ≃ A
  -- Exercise: mvrnote
```

mvrnote: missing

Isomorphisms compose like functions do, but we will prove this a
little later (`compIso`{.Agda} in Lecture 2-4).

As promised earlier, we can finally prove that isomorphisms compose.

```
compEquiv : B ≃ C → A ≃ B → A ≃ C
compEquiv (f₁ , (g₁ , s₁) , (g'₁ , r₁))
        (f₂ , (g₂ , s₂) , (g'₂ , r₂)) =
    f₁ ∘ f₂ , (g₂ ∘ g₁  , to-fro) , (g'₂ ∘ g'₁ , fro-to)
  where to-fro : isSection (f₁ ∘ f₂) (g₂ ∘ g₁)
        to-fro b = cong f₁ (s₂ (g₁ b)) ∙ s₁ b
        fro-to : isRetract (f₁ ∘ f₂) (g'₂ ∘ g'₁)
        fro-to a = cong g'₂ (r₁ (f₂ a)) ∙ r₂ a
```

mvrnote: congPathIso could be another (extended) exercise, or put in extras?

## Aside: Equational Reasoning

mvrnote: move earlier, as soon as we have composition?

We will sometimes produce a path by chaining together several simpler
ones. There is a common pattern that is used to give this process some
nice syntax.

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

Here are some examples of how to use it. mvrnote: 1lab hides the paths, need to switch the default

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

We encourage you to use this syntax when chaining paths together, it
makes it a lot easier to see what's going on!

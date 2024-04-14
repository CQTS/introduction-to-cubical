
```
module 2--Paths-and-Identifications.2-10--Higher-Types where
```

# Lecture 2-10: Higher Types

<!--
```
open import Library.Prelude
open import Library.Literals
open import Library.Univalence
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-6--Propositions
open import 2--Paths-and-Identifications.2-7--Sets
open import 2--Paths-and-Identifications.2-8--Equivalences
open import 2--Paths-and-Identifications.2-9--Univalence
```
-->

So far, we have seen a heirarchy of types of increasing complexity:
contractible types followed by propositions and then sets. But not all
types are sets. In particular, via univalence, it is easy to check
that `Type`{.Agda} is not a set.

```
not-Path : Bool ≡ Bool
not-Path = ua (isoToEquiv not-Iso)

¬isSet-Type : ¬ isSet Type
¬isSet-Type s = true≢false (λ i → transport (bad-Path i) true)
  where bad-Path : refl ≡ not-Path
        bad-Path = s Bool Bool refl not-Path
```

As an aside, the type of propositions is a set, however:

```
Prop : ∀ ℓ → Type (ℓ-suc ℓ)
Prop ℓ = Σ[ X ∈ Type ℓ ] isProp X

-- mvrnote: todo
-- isSetProp : ∀ {ℓ} → isSet (Prop ℓ)
-- isSetProp (X , pX) (Y , pY) p q = {!!}
```

## The Circle

We can also define inductive types which are not sets. This type
is called the *circle* `S¹`, since it contains a point `base`{.Agda}
and a path `loop`{.Agda} which goes from `base`{.Agda} to
`base`{.Agda}, forming a circle.

```
data S¹ : Type where
  base : S¹
  loop : base ≡ base
```

mvrnote: prose
```
S¹-rec : ∀ {ℓ} {A : Type ℓ} (a : A) (l : a ≡ a)
       → S¹ → A
S¹-rec a l base = a
S¹-rec a l (loop i) = l i

S¹-ind : ∀ {ℓ} {A : S¹ → Type ℓ} (a : A base) (l : PathP (λ i → A (loop i)) a a)
       → (s : S¹) → A s
S¹-ind a l base = a
S¹-ind a l (loop i) = l i
```

mvrnote: prose
```
loopⁿ : ℤ → base ≡ base
loopⁿ (pos zero) = refl
loopⁿ (pos (suc n)) = loopⁿ (pos n) ∙ loop
loopⁿ (negsuc zero) = sym loop
loopⁿ (negsuc (suc n)) = loopⁿ (negsuc n) ∙ sym loop
```

mvrnote: prose
```
rotLoop : (a : S¹) → a ≡ a
rotLoop base       = loop
rotLoop (loop i) j =
  hcomp (λ k → λ { (i = i0) → loop (j ∨ ~ k)
                 ; (i = i1) → loop (j ∧ k)
                 ; (j = i0) → loop (i ∨ ~ k)
                 ; (j = i1) → loop (i ∧ k)}) base

_·S¹_ : S¹ → S¹ → S¹
base     ·S¹ x = x
(loop i) ·S¹ x = rotLoop x i

infixl 30 _·S¹_
```

To show that `S¹`{.Agda} is not a set, we can define its "double
cover" --- a type family with two elements over the base point, but
for which `transport`{.Agda}ing along the `loop`{.Agda} flips those
two points. Use this to show that `S¹`{.Agda} is also not a set.

mvrnote: rip picture from hott game?

```
double-cover : S¹ → Type
double-cover base = Bool
double-cover (loop i) = not-Path i

refl≢loop : ¬ refl ≡ loop
-- Exercise:
refl≢loop = {!!}

¬isSet-S¹ : ¬ isSet S¹
-- Exercise:
¬isSet-S¹ isSet = {!!}
```

             line1
         pt  - - - > pt
          ^           ^
    line2 |           | line2    ^
          |           |        j |
         pt  — — — > pt          ∙ — >
             line1                 i
```
data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : Square line2 line2 line1 line1
```

```
t2c : Torus → S¹ × S¹
t2c point        = ( base , base )
t2c (line1 i)    = ( loop i , base )
t2c (line2 j)    = ( base , loop j )
t2c (square i j) = ( loop i , loop j )

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl
```

## Suspensions

mvrnote: prose

```
data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

Susp-func : {ℓ : Level} {X Y : Type ℓ} → (f : X → Y) → Susp X → Susp Y
Susp-func f north = north
Susp-func f south = south
Susp-func f (merid a i) = merid (f a) i
```

The simplest example is when we feed `Susp`{.Agda} the empty type
`∅`{.Agda}.

```
Susp∅≅Interval : Iso (Susp ∅) Bool
-- Exercise (trivial):
-- Susp∅≅Interval = {!!}
Iso.fun Susp∅≅Interval north = true
Iso.fun Susp∅≅Interval south = false
Iso.inv Susp∅≅Interval true = north
Iso.inv Susp∅≅Interval false = south
Iso.rightInv Susp∅≅Interval true = refl
Iso.rightInv Susp∅≅Interval false = refl
Iso.leftInv Susp∅≅Interval north = refl
Iso.leftInv Susp∅≅Interval south = refl
```

Next simplest is the unit type `⊤`{.Agda} the reuslt looks like the
following:

```
data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

Susp⊤≅Interval : Iso (Susp ⊤) Interval
-- Exercise (trivial):
-- Susp⊤≅Interval = {!!}
Iso.fun Susp⊤≅Interval north = zero
Iso.fun Susp⊤≅Interval south = one
Iso.fun Susp⊤≅Interval (merid tt i) = seg i
Iso.inv Susp⊤≅Interval zero = north
Iso.inv Susp⊤≅Interval one = south
Iso.inv Susp⊤≅Interval (seg i) = merid tt i
Iso.rightInv Susp⊤≅Interval zero = refl
Iso.rightInv Susp⊤≅Interval one = refl
Iso.rightInv Susp⊤≅Interval (seg i) = refl
Iso.leftInv Susp⊤≅Interval north = refl
Iso.leftInv Susp⊤≅Interval south = refl
Iso.leftInv Susp⊤≅Interval (merid tt i) = refl
```

This `Interval`{.Agda} is an ordinary type, in contrast to the
built-in interval `I`{.Agda}. We can therefore use it like any other
type; form functions into it, look at paths in it, and so on. It does
not contain any of the magic that `I`{.Agda} does, however, so we
can't make a corresponding `Path`{.Agda} or `hcomp`{.Agda}. In fact,
it contains no interesting information at all:

```
isContrInterval : isContr Interval
isContrInterval = (zero , contr)
  where
  contr : (x : Interval) → zero ≡ x
  contr zero      = refl
  contr one       = seg
  contr (seg i) j = connection∧ seg i j
```

Finally something interesting happens once we try `Bool`{.Agda}.

mvrnote: will this need hints?
```
SuspBool≅S¹ : Iso (Susp Bool) S¹
-- Exercise:
SuspBool≅S¹ = {!!}
```

mvrnote: Some exercises: Suspension of isContr isContr, Suspension of isProp isSet

## The fundamental group of the circle

```
helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤ-Path i

S¹-encode : (x : S¹) → base ≡ x → helix x
S¹-encode _ p = subst helix p (pos zero)
```

```
S¹-decode : (x : S¹) → helix x → base ≡ x
```

Decode is a bit of a pain. In the `loop`{.Agda} case, we will be asked to
complete the following square: (In the following diagrams, the
vertices are all `base`{.Agda}.)

                loop
            * - - - - > *
            ^           ^
    loopⁿ y |           | loopⁿ y         ^
            |           |               j |
            * — — — - > *                 ∙ — >
                refl                        i

mvrnote: crappy justification:

It might look odd to have `loopⁿ y j` on both sides. The reason is
that the integer `y` varies as `i` goes from `i0` to `i1`, going from
some `n` to `n+1`. And so the square should commute: going around
either way should be `loopⁿ (suc n) j`. The reason it is not literally
written this way is that `y` is some element of `sucℤ-Path i`, which
is some type along the path `sucℤ-Path` in the universe, and not the
type `ℤ`.

We can build this square as an `hcomp`. Here's the cube we are going
to fill, with the desired square sitting on the top.

                                      loop
                                * - - - - - - - - > *
                    loopⁿ y   / ^                 / ^
                            /   |               / loopⁿ y
                          /     | refl        /     |
                        * - - - - - - - - > *       |
                        ^       |           ^       |                    ^   j
                        |       |           |       |                  k | /
                        |       |           |       |                    ∙ — >
                        |       |    loop   |       |                      i
                        |       * - - - - - | - - > *
    loopⁿ (predℤ (suzℤ y))    /             |     /
                        |   /               |   /  loopⁿ y
                        | /                 | /
                        * - - - - - - - - > *
                                refl

Three of the sides are easy, just constant in one of the dimensions.
```
S¹-decode-faces : (i : I) → (y : sucℤ-Path i) → (j : I) → I → Partial (i ∨ ~ i ∨ j ∨ ~ j) S¹

S¹-decode-faces i y j k (i = i1) = loopⁿ y j
S¹-decode-faces i y j k (j = i0) = base
S¹-decode-faces i y j k (j = i1) = loop i
```

The `(i = i0)` face is more slightly more interesting, here it is written flat:

                loopⁿ y
            * - - - - - > *
            ^             ^
       refl |             | refl              ^
            |             |                 k |
            * — — — - - > *                   ∙ — >
         loopⁿ (predℤ (suzℤ y))                 j

For this we can combine `loopⁿ` with `sucℤ-Iso`{.Agda} in the first argument.
```
S¹-decode-faces i y j k (i = i0) = loopⁿ (Iso.leftInv sucℤ-Iso y k) j
```

All that remains is to construct the base square, and for this we have
to get our hands dirty. For every `n`, we need a square

                        loop
                    * - - - - > *
                    ^           ^
    loopⁿ (predℤ n) |           | loopⁿ n           ^
                    |           |                 j |
                    * — — — - > *                   ∙ — >
                        refl                          i

Constructing these squares will need to make reference to our actual
defintion of `predℤ`{.Agda}, so we split into the same three cases as were
used for `predℤ`: `pos zero`, `pos (suc n)` and `negsuc n`.

```
S¹-decode-base : (n : ℤ) → Square (loopⁿ (predℤ n)) (loopⁿ n) refl loop

```

The simplest case is `pos zero`:

                   loop
               * - - - - > *
               ^           ^
     sym loop  |           | refl              ^
               |           |                 j |
               * — — — - > *                   ∙ — >
                   refl                          i

and this is easy to build using a connection.

```
S¹-decode-base (pos zero) i j = loop (i ∨ ~ j)
```

Next we have `pos (suc n)`, which is exactly one of the composition
fillers we've seen already.

                        loop
                    * - - - - > *
                    ^           ^
    loopⁿ (pos n) j |           | loopⁿ (pos n) ∙ loop          ^
                    |           |                             j |
                    * — — — - > *                               ∙ — >
                        refl                                      i

```
S¹-decode-base (pos (suc n)) i j = compPath-filler (loopⁿ (pos n)) loop i j
```

And the final case for `negsuc`{.Agda} is similar.

                                    loop
                                * - - - - > *
                                ^           ^
    loopⁿ (negsuc n) ∙ sym loop |           | loopⁿ (negsuc n)              ^
                                |           |                             j |
                                * — — — - > *                               ∙ — >
                                    refl                                      i

This is actually also an instance of `compPath-filler`{.Agda}, but we have to
flip the direction of `i` because the composition is now happening at
`i = i0`.

```
S¹-decode-base (negsuc n) i j = compPath-filler (loopⁿ (negsuc n)) (sym loop) (~ i) j
```

Finally, we perform the actual `hcomp`.
```
S¹-decode base = loopⁿ
S¹-decode (loop i) y j =
  hcomp (S¹-decode-faces i y j)
        (S¹-decode-base (unglue (i ∨ ~ i) y) i j)
```

Checking that one composite is equal to the identity is easy using `J`{.Agda},
because everything computes away when the input path `p` is `refl`{.Agda}:
```
S¹-decodeEncode : (p : base ≡ base) → S¹-decode base (S¹-encode base p) ≡ p
S¹-decodeEncode p = J (λ y q → S¹-decode y (S¹-encode y q) ≡ q) (λ _ → refl) p
```

And the other way can be verified by induction on `ℤ`{.Agda}.
(Remember that `decode base` is just `loopⁿ`{.Agda} by definition, so
we don't have to worry about the complicated `hcomp`{.Agda}.)

```
S¹-encodeDecode : (n : ℤ) → S¹-encode base (S¹-decode base n) ≡ n
S¹-encodeDecode (pos zero) = refl
S¹-encodeDecode (pos (suc n)) = cong sucℤ (S¹-encodeDecode (pos n))
S¹-encodeDecode (negsuc zero) = refl
S¹-encodeDecode (negsuc (suc n)) = cong predℤ (S¹-encodeDecode (negsuc n))
```

And we're done!
```
ΩS¹Isoℤ : Iso (base ≡ base) ℤ
Iso.fun ΩS¹Isoℤ      = S¹-encode base
Iso.inv ΩS¹Isoℤ      = S¹-decode base
Iso.rightInv ΩS¹Isoℤ = S¹-encodeDecode
Iso.leftInv ΩS¹Isoℤ  = S¹-decodeEncode
```

mvrnote: yet another way of implementing `+ℤ`{.Agda}
```
_+ℤ''_ : ℤ → ℤ → ℤ
x +ℤ'' y = Iso.fun ΩS¹Isoℤ (λ i → (Iso.inv ΩS¹Isoℤ x i) ·S¹ (Iso.inv ΩS¹Isoℤ y i))
```


## Even Higher types

Egbert exercises:

Show that a type 𝑋 is a set if and only if the map
𝜆𝑥. 𝜆𝑡. 𝑥 : 𝑋 → (S1 → 𝑋)
is an equivalence.

mvrnote: exercises
(b) Construct an equivalence fib𝛿𝐴
(𝑥, 𝑦) ' (𝑥 = 𝑦) for any 𝑥, 𝑦 : 𝐴.
(c) Show that 𝐴 is (𝑘 + 1)-truncated if and only if 𝛿𝐴 : 𝐴 → 𝐴 × 𝐴 is
𝑘-truncated.

22.1 (a)

```
-- zero≢one : ¬ pos zero ≡ pos (suc zero)
-- zero≢one p = {!!}

-- -- isConnected : (X : Type) → Type
-- -- isConnected X = isContr ∥ X ∥₀

-- isConnectedS¹-path : (s : S¹) → ∥ base ≡ s ∥
-- isConnectedS¹-path base = ∣ refl ∣
-- isConnectedS¹-path (loop i) = squash ∣ (λ j → loop (i ∧ j)) ∣ ∣ (λ j → loop (i ∨ ~ j)) ∣ i

-- not-isContrS¹ : ¬ isContr S¹
-- not-isContrS¹ c = zero≢one (isContr→isProp (isContrAcrossIso (invIso ΩS¹Isoℤ) (isContrisContr≡ c base base)) (pos zero) (pos (suc zero)))

-- not-inhabited→pointed : ¬ ((A : Type) → ∥ A ∥ → A)
-- not-inhabited→pointed p = not-isContrS¹ (base , λ y → p (base ≡ y) (isConnectedS¹-path y))
```

22.2 and 22.4

```
-- degree : (f : S¹ → S¹) → (f base ≡ base) → ℤ
-- degree f = ?

-- S¹-auto : Iso (S¹ ≃ S¹) (S¹ ⊎ S¹)
-- Iso.fun S¹-auto x = {!!}
-- Iso.inv S¹-auto = {!!}
-- Iso.rightInv S¹-auto = {!!}
-- Iso.leftInv S¹-auto = {!!}
```

```
module 2--Paths-and-Identifications.2-6--Univalence where
```

# Lecture 2-6: Univalence

<!--
```
open import Library.Prelude
open import Library.Literals
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import Library.Univalence

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' B C : Type ℓ
```
-->

mvrnote: more background
An important feature of Cubical Type Theory is *univalence*. This is
the statement that paths between types are equivalent to equivalences
between those types.

Cubical Type Theory's central accomplishment over other type theories
is allowing the univalence principle to compute. This is done using
`Glue` types, whose constructor has the following signature.

    Glue : (A : Type ℓ) {φ : I}
         → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
         → Type ℓ'

The type constructor ``Glue`` takes a type `A`, a formula `φ`,
and a partial element `Te : Partial φ (Σ[ T ∈ Type ] (T ≃ A))` of
pairs of types equipped with an equivalence to `A`, defined only when
``φ`` is ``i1``.

As usual, the formula `φ` plays a crucial role. Consider the case of
`φ = ∂ i`. We can depict an element of the partial type
`Te : Partial (∂ i) (Σ[ T ∈ Type ℓ' ] T ≃ A)` as follows:

                 A i
         A i0  - - - > A i1
           ^             ^
    Te i0  (             (  Te i1                 ^
           )             )                        )
         T i0          T i1                       ∙ — >
                                                    i

where the vertical squiggly lines are equivalences rather than paths.
This looks a lot like the kind of thing we were ``hcomp``ing over
in Lecture 2-X, except that it is open on the bottom rather than the
top. (This is is a conventional choice --- the equivalences go into `A`,
rather than out of it.)

``Glue`` types enable us to "cap off" this open box of types.
That is, if `φ = ∂ i`, then `Glue A Te : Type` is the line of types
living *under* `A` in the capped off version of the above square.

``Glue`` types come with some guarantees. First, like
``hcomp``, the line we get agrees with the partial input
anywhere the formula `φ` holds. In the example, this means

* `Glue A Te = T i0` when `i = i0` and
* `Glue A Te = T i1` when `i = i1`.

Secondly, for any element of `Glue A Te` at all, we can extract the
underlying element of `A` that we started with: this operation is
called `unglue φ`, which has type `Glue A Te → A`. Because of the above computation
rule, if `φ` holds then the domain of this function is `T`. Luckily,
in this situation we have access to an equivalence `T ≃ A`, from which
we can extract the necessary function `T → A`.

To summarise, `Glue Te` is a version of `A` that has the types `T`
glued on wherever `φ` holds, using the provided equivalences `Te` to
extract an underlying element of `A` whenever asked.

The first and most important example of a ``Glue`` type gives us
univalence, building a path out of an equivalence of types.

           B
      B - - - > B
      ^         ^
    e (         ( idEquiv                ^
      )         )                        )
      A         B                        ∙ — >
                                           i

```
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B {φ = ∂ i}
  (λ { (i = i0) → (A , e)
     ; (i = i1) → (B , idEquiv B) })
```

The eliminator ``unglue`` works as expected on ``ua`` --- we
are able to get out the element of `B` no matter where we are in the
``Glue`` type `ua e i`.

```
ua-unglue : (e : A ≃ B) → (i : I) → (x : ua e i) → B
ua-unglue e i x = unglue (∂ i) x

_ : {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i0) → ua-unglue e i0 x ≡ (fst e) x
_ = λ e i x → refl

_ : {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i1) → ua-unglue e i1 x ≡ x
_ = λ e i x → refl
```

If ‵x : A` and `y : B`, then to get a `PathP` from `x` to `y` over `ua
e i` is the same as giving a path from `e x` to `y`.

```
ua-PathP→Path : (e : A ≃ B) {x : A} {y : B}
              → PathP (λ i → ua e i) x y
              → e .fst x ≡ y
ua-PathP→Path e p i = ua-unglue e i (p i)
```

When ``ua`` is appled to the identity equivalence on `A`, we get
the ``refl`` path from `A` to itself.

```
uaIdEquiv : ua (idEquiv A) ≡ refl
```

Written as a square, we are trying to construct the square of types
where on three of the sides we are constant at the type `A` and on the
remaining side we have `ua (idEquiv A)`.


                A - - - - - - - - > A
              / ^                 / ^
            /   )               /   )
          /     (             /     (
        A - - - - - - - - > A       )
        ^       (           ^       (                    ^   j
        )       )           )       )                    ) /
        (       (           (       (                    ∙ — >
        )       )           )       )                      i
        (       A - - - - - ( - - > A
        )                   )     /
        (                   (   /
        )                   ) /
        A - - - - - - - - > A

Using ``Glue`` again here with `(A , idEquiv A)` on all the
vertical faces gives us a square of types on the bottom. When `i =
i1`, `j = i0` or `j = i1`, this `Glue`-type computes away to give
exactly `A`. When `i = i0`, we are left with the line of types `Glue A
{φ = ∂ j} (λ _ → A , idEquiv A)`, but this is exactly the definition
of `ua (idEquiv A)`.

```
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , idEquiv A)
```

Nicely, Agda builds-in that transporting over `ua e` is the same as
applying the function underlying the equivalence `e`.

```
uaβ : (e : A ≃ B) → (x : A) → transport (ua e) x ≡ fst e x
uaβ e x = transport-refl (equivFun e x)
```

For concrete types this usually holds definitionally like
``transport``, but for an arbitrary equivalence `e` between
unknown types `A` and `B` we have to prove it. This is an instance of
the computation rule for ``transport`` on ``Glue`` types,
which in general is quite complicated.

```
uaβBool : (e : Bool ≃ Bool) (x : Bool) → transport (ua e) x ≡ fst e x
uaβBool e x = refl

_ : transport (ua not-≃) true ≡ false
_ = refl

uaβS¹ : (e : S¹ ≃ S¹) (x : S¹) → transport (ua e) x ≡ fst e x
uaβS¹ e x = refl
```

Finally, univalence is inverse to ``pathToEquiv``. We show one
half of this now, but will need to wait until Lecture 2-X to show the
other direction.

```
au : A ≡ B → A ≃ B
au = pathToEquiv

ua-au : (p : A ≡ B) → ua (au p) ≡ p
ua-au = J (λ _ p → ua (au p) ≡ p) path
  where path = ua (au refl)   ≡⟨ cong ua pathToEquivRefl ⟩
               ua (idEquiv _) ≡⟨ uaIdEquiv ⟩
               refl ∎
```

mvrnote: possible exercise from the HoTT book:
(i) Show that if A ≃ A' and B' ≃ B, then (A × B) ≃ (A' × B')
(ii) Give two proofs of this fact, one using univalence and one not using it, and show that the
two proofs are equal.


## Addition as Composition

Here's a fun first application: we can implement addition in
``ℤ`` as composition of paths of type `ℤ ≡ ℤ`. This leads to a
one-line proof that addition is invertible.

We showed previously that ``sucℤ`` is an equivalence, and
univalence lets us turn this into a path `ℤ ≡ ℤ`.

```
sucℤ-≡ : ℤ ≡ ℤ
sucℤ-≡ = ua sucℤ-≃
```

This is the path corresponding to the integer 1, and by iterated
composition we can produce a path for any integer. Iterated
composition works for any self-loop. For negative integers, we simply
compose with the inverse of the loop.

There are two ways you could do this, repeatedly composing on the left
or composing on the right. This choice will matter for later
definitions, so compose on the *right*.

```
iterateⁿ : {x : A} → x ≡ x → ℤ → x ≡ x
-- Exercise: (Remember to be careful with `negsuc`!)
iterateⁿ p z = {!!}

-- To make sure you composed the right way:
_ : {x : A} → (p : x ≡ x) → iterateⁿ p 2 ≡ (refl ∙ p) ∙ p
_ = λ p → refl

_ : {x : A} → (p : x ≡ x) → iterateⁿ p (-2) ≡ (sym p) ∙ sym p
_ = λ p → refl
```

Then the path for any integer is

```
add-ℤ-≡ : ℤ → ℤ ≡ ℤ
add-ℤ-≡ = iterateⁿ sucℤ-≡
```

Here's the upshot: we can define addition of integers by turning one
of them into a path in the universe, and then transporting the other
along that path. This transports the integer along the `ua sucℤ-≃`
path repeatedly, which applies ``suc`` each time.

```
_+ℤᵘ_ : ℤ → ℤ → ℤ
m +ℤᵘ n = transport (add-ℤ-≡ n) m
```

It is easy to show that this agrees with the ordinary addition
``+ℤ``, by case-splitting.

```
+ℤᵘ≡+ℤ : _+ℤᵘ_ ≡ _+ℤ_
-- Exercise:
+ℤᵘ≡+ℤ i m n = {!!}
```

Now, a nice trick. Because ``+ℤᵘ`` for a fixed `n` is defined via
``transport``, it is automatically an equivalence:

```
isEquiv-+ℤᵘ : (m : ℤ) → isEquiv (λ n → n +ℤᵘ m)
-- Exercise: (Hint: `pathToEquiv`)
isEquiv-+ℤᵘ n = {!!}
```

And because we have just shown that ``+ℤᵘ`` is equal to
``+ℤ``, we get a prove that the same is true for ``+ℤ`` with
no extra effort.

```
isEquiv-+ℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
-- Exercise:
isEquiv-+ℤ = subst {!!} {!!} {!!}
```


## The Fundamental Group of the Circle

One amazing consequences of univalence is that it grants type theory
access to a lot of higher-dimensional homotopical structure. The
primary way it does this is by letting us construct interesting type
families. Here's a first example: the "double cover" of the circle
``S¹``. This is a type family with two elements over
``base``, for which ``transport``ing along the ``loop``
flips those two points.

```
not-Path : Bool ≡ Bool
not-Path = ua not-≃

double-cover : S¹ → Type
double-cover base = Bool
double-cover (loop i) = not-Path i
```

mvrnote: rip picture from hott game?

This type family lets us show that the circle is non-trivial, which is
a fact we didn't know for sure previously!

```
refl≢loop : ¬ refl ≡ loop
-- Exercise: (Hint: `subst` in this type family.)
refl≢loop p = {!!}
```

::: Aside:
It may be surprising that without univalence or similar it is
impossible to prove that ``S¹`` is nontrivial! With the bare
constructions of type theory, it is consistent to assume that
``S¹`` is contractible.
:::

mvrnote: The total space of the double cover is equivalent to the
circle, looks tricky!
https://favonia.org/courses/hdtt2020/agda/agda-0430-setquot.agda

There's nothing special about ``Bool`` here. Rather than placing
two points over each point of the circle, we could put an entire copy
of ``ℤ``

```
helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤ-≡ i
```

mvrnote: how hard is it to prove that the total space of helix is
contractible?

In the remainder of this section we will prove a crucial fact about
``S¹``: that the space of paths from ``base`` to itself is
equivalent to the integers. That is, the following function is an
equivalence:

```
loopⁿ : ℤ → base ≡ base
loopⁿ = iterateⁿ loop
```

This will be an encode-decode proof like those in Lecture 2-3, with
some slight differences which we will discuss when we encounter them.

```
ΩS¹≃ℤ : (base ≡ base) ≃ ℤ
ΩS¹≃ℤ = equiv (encode base) (decode base) fro-to to-fro
  where
```

First, the codes for the paths. Because we are ultimately only
interseted in `base ≡ base`, we just give codes for paths of the form
`base ≡ x`. For this, we use the ``helix`` type family defined
above.

```
    code : S¹ → Type
    code = helix
```

Then ``encodeRefl`` and ``encode`` are defined as usual,
though ``encodeRefl`` is particularly simple because we only care
about ``base``.

```
    encodeRefl : code base
    encodeRefl = pos zero

    encode : (x : S¹) → base ≡ x → code x
    encode x p = J (λ y _ → code y) encodeRefl p
```

Now for ``decode``, which will take a lot more work.

```
    decode : (x : S¹) → code x → base ≡ x
```

We now case-split on `x`, so we will need to give cases for
``base`` and ``loop``. The ``base`` case is easy: we
have an element of `code base`, i.e. an integer, and we need to
produce a path `base ≡ base`. For this we have the function
``loopⁿ`` from earlier.

```
    decode base = loopⁿ
```

In the ``loop`` case, we will be asked to complete the following
square, where `y : code (loop i)`: (In the following diagrams, all the
vertices are always ``base``.)

                loop
            * - - - - > *
            ^           ^                   ^
    loopⁿ y |           | loopⁿ y         j |
            |           |                   ∙ — >
            * — — — - > *                     i
                refl

It might look odd to have `loopⁿ y j` on both sides: it seems it ought
to be impossible to fill this square, because we have `n` copies of
``loop`` going around one way and `n+1` copies going around the
other.

But the reason is that the variable `y` is not actually a fixed
integer: it varies along the type family `code (loop i)` as `i` goes
from `i0` to `i1`. By the definition of ``helix``, this is
exactly going from some `n` to `n + 1`. And so the square should
commute: going around either way should be `loopⁿ (suc n)`.

We can build this square as an ``hcomp``. Here's the cube we are
going to fill, with the desired square sitting on the top.

                                      loop
                                * - - - - - - - - > *
                    loopⁿ y   / ^                 / ^
                            /   |               / loopⁿ y
                          /     | refl        /     |
                        * - - - - - - - - > *       |
                        ^       |           ^       |              ^   j
                        |       |           |       |            k | /
                        |       |           |       |              ∙ — >
                        |       |    loop   |       |                i
                        |       * - - - - - | - - > *
    loopⁿ (predℤ (sucℤ y))    /             |     /
                        |   /               |   /  loopⁿ y
                        | /                 | /
                        * - - - - - - - - > *
                                refl

djnote: we should explain what the `unglue` is doing here.

```
    decode (loop i) y j = hcomp
      (decode-faces i y j)
      (decode-base (unglue (∂ i) y) i j)
      where
```

Three of the sides are easy, they are just square that are constant
in one of the directions.

```
      decode-faces : (i : I) → (y : sucℤ-≡ i) → (j : I) → I → Partial (∂ i ∨ ∂ j) S¹
      -- Exercise:
      decode-faces i y j k (i = i1) = {!!}
      decode-faces i y j k (j = i0) = {!!}
      decode-faces i y j k (j = i1) = {!!}
```

The `(i = i0)` face is slightly more interesting, here it is written
flat:

                loopⁿ y
            * - - - - - > *
            ^             ^                  ^
       refl |             | refl           k |
            |             |                  ∙ — >
            * — — — - - > *                    j
         loopⁿ (predℤ (sucℤ y))



A path `predℤ (sucℤ y) ≡ y` is provided by the retraction part of the
equivalence ``sucℤ-≃``, so we just have to surround it with
``loopⁿ``.

```
      -- Exercise:
      decode-faces i y j k (i = i0) = {!!}
```

All that remains is to construct the base square and for this we have
to get our hands dirty. For every `n`, we need a square

                        loop
                    * - - - - > *
                    ^           ^                 ^
    loopⁿ (predℤ n) |           | loopⁿ n       j |
                    |           |                 ∙ — >
                    * — — — - > *                   i
                        refl

```
      decode-base : (n : ℤ) → Square (loopⁿ (predℤ n)) (loopⁿ n) refl loop
```

Constructing this square will make reference to our actual defintion
of ``predℤ``, so we split into the same three cases that we used
for ``predℤ``: `pos zero`, `pos (suc n)` and `negsuc n`.

The simplest case is `pos zero`:

                   loop
               * - - - - > *
               ^           ^                  ^
     sym loop  |           | refl           j |
               |           |                  ∙ — >
               * — — — - > *                    i
                   refl

and this is easy to build using a connection.

```
      -- Exercise:
      decode-base (pos zero) i j = {!!}
```

Next we have `pos (suc n)`, which is exactly one of the composition
fillers we've seen already, ``∙-filler``.

                        loop
                    * - - - - > *
                    ^           ^                             ^
    loopⁿ (pos n) j |           | loopⁿ (pos n) ∙ loop      j |
                    |           |                             ∙ — >
                    * — — — - > *                               i
                        refl

```
      -- Exercise:
      decode-base (pos (suc n)) i j = ∙-filler {!!} {!!} {!!} {!!}
```

And the final case for ``negsuc`` is similar.

                                    loop
                                * - - - - > *
                                ^           ^                          ^
    loopⁿ (negsuc n) ∙ sym loop |           | loopⁿ (negsuc n)       j |
                                |           |                          ∙ — >
                                * — — — - > *                            i
                                    refl

This is actually also an instance of ``∙-filler``, but we
have to flip the direction of `i` because the composition is now
happening on the `i = i0` side.

```
      -- Exercise:
      decode-base (negsuc n) i j = ∙-filler {!!} {!!} {!!} {!!}
```

Checking that one composite is equal to the identity is easy using
``J`` as usual, because everything computes away to nothing when
the input path `p` is ``refl``:

```
    to-fro : isSection (decode base) (encode base)
    -- Exercise:
    to-fro p = J {!!} {!!} {!!}
```

And the other way can be verified by induction on ``ℤ``.
(Remember that `decode base` is exactly ``loopⁿ`` by definition, so
we don't have to worry about the complicated ``hcomp``.)

```
    fro-to : isRetract (decode base) (encode base)
    -- Exercise:
    fro-to n = {!!}
```

And we're done!


## Addition Yet Again

As a final demonstration in this Lecture, let's use the above proof to
define addition one final time. We now know that ``ℤ`` is
equivalent to `base ≡ base` so we can do this by finding a group
operation on `S¹`.

Geometrically, this operation is easy to describe. For any two points
on the circle, look at their angles from the basepoint and add those
angles together. Or phrased another way, consider ``S¹`` as the
unit circle in the complex plane, and combine two such complex numbers
by multiplying them.

How do we describe this in type theory? If we fix one of the points
`y` and let the other run around `loop : base ≡ base`, we should get a
loop `y ≡ y` that also runs around ``S¹``. (Like ``loop``
but starting and ending at some point other than ``base``.)

```
rotate-loop : (y : S¹) → y ≡ y
-- Exercise: (Hint: We've built this square previously!)
rotate-loop base       = loop
rotate-loop (loop i) j = {!!}
```

Now the multiplication operation. The point ``base`` of
``S¹`` lies at angle 0, so it should not move the other pont at
all. And in the ``loop`` case, the above operation
``rotate-loop`` is exactly what we need.

```
_·S¹_ : S¹ → S¹ → S¹
-- Exercise:
base   ·S¹ y = {!!}
loop i ·S¹ y = {!!}

infixl 30 _·S¹_
```

Now combine this multiplication with the ``ΩS¹≃ℤ`` equivalence:
turn `x` and `y` into loops, multiply them, and turn the resulting
loop back.

```
_+ℤᵐ_ : ℤ → ℤ → ℤ
-- Exercise:
x +ℤᵐ y = equivFun ΩS¹≃ℤ {!!}
```


mvrnote: yet another type of integers

infixl 5 _⊖_
data ΔInt : Type₀ where
  _⊖_    : ℕ → ℕ → ΔInt
  cancel : ∀ a b → a ⊖ b ≡ suc a ⊖ suc b

succ : ΔInt → ΔInt
succ (a ⊖ b) = suc a ⊖ b
succ (cancel a b i) = cancel (suc a) b i

pred : ΔInt → ΔInt
pred (a ⊖ b) = a ⊖ suc b
pred (cancel a b i) = cancel a (suc b) i

fromInt : Int → ΔInt
fromInt (pos n) = n ⊖ 0
fromInt (negsuc n) = 0 ⊖ suc n

{-
  _ℕ-_ : ℕ → ℕ → Int
  a ℕ- 0 = pos a
  0 ℕ- suc b = negsuc b
  suc a ℕ- suc b = a ℕ- b
-}
toInt : ΔInt → Int
toInt (a ⊖ b) = a ℕ- b
toInt (cancel a b i) = a ℕ- b

toInt-fromInt : ∀ n → toInt (fromInt n) ≡ n
toInt-fromInt (pos _) = refl
toInt-fromInt (negsuc _) = refl

diamond : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (λ i → p i ≡ q i) [ p ≡ q ]
diamond {y = y} p q i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → q (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → q (i ∧ k)
      }) y

triangle : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → (λ i → x ≡ p i) [ refl ≡ refl ∙ p ]
triangle {x = x} p i j = hcomp (λ k → λ { (i = i0) → x; (j = i0) → x; (j = i1) → p (i ∧ k)}) x

-- This is very difficult.
fromInt-toInt : ∀ n → fromInt (toInt n) ≡ n
fromInt-toInt (a ⊖ 0) = refl
fromInt-toInt (0 ⊖ suc b) = refl
fromInt-toInt (suc a ⊖ suc b) = fromInt-toInt (a ⊖ b) ∙ cancel a b
fromInt-toInt (cancel a 0 i) = triangle (cancel a 0) i
fromInt-toInt (cancel 0 (suc b) i) = triangle (cancel 0 (suc b)) i
fromInt-toInt (cancel (suc a) (suc b) i) =
  fromInt-toInt (cancel a b i) ∙ diamond (cancel a b) (cancel (suc a) (suc b)) i

{- Part 2 -}

equiv : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) (g : B → A) (f-g : (y : B) → f (g y) ≡ y) (g-f : (x : A) → g (f x) ≡ x) → A ≃ B
equiv f g f-g g-f = isoToEquiv (iso f g f-g g-f)

Int≡ΔInt : Int ≡ ΔInt
Int≡ΔInt = ua (equiv fromInt toInt fromInt-toInt toInt-fromInt)

{-
  _+_ : Int → Int → Int
  m + pos n = m +pos n
  m + negsuc n = m +negsuc n
-}
_Δ+_ : ΔInt → ΔInt → ΔInt
_Δ+_ = transport (λ i → Int≡ΔInt i → Int≡ΔInt i → Int≡ΔInt i) _+_

+≡Δ+ : (λ i → Int≡ΔInt i → Int≡ΔInt i → Int≡ΔInt i) [ _+_ ≡ _Δ+_ ]
+≡Δ+ = transport-filler (λ i → Int≡ΔInt i → Int≡ΔInt i → Int≡ΔInt i) _+_

{- Hints: There are already many theorems about _+_. -}
{- Check out https://github.com/agda/cubical/blob/master/Cubical/Data/Int/Properties.agda -}
Δ+-comm : ∀ x y → x Δ+ y ≡ y Δ+ x
Δ+-comm = transport (λ i → ∀ (x y : Int≡ΔInt i) → +≡Δ+ i x y ≡ +≡Δ+ i y x) +-comm

Δ+-assoc : ∀ x y z → x Δ+ (y Δ+ z) ≡ (x Δ+ y) Δ+ z
Δ+-assoc = transport (λ i → ∀ (x y z : Int≡ΔInt i) → +≡Δ+ i x (+≡Δ+ i y z) ≡ +≡Δ+ i (+≡Δ+ i x y) z) +-assoc

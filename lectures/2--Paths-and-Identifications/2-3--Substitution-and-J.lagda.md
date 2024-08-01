```
module 2--Paths-and-Identifications.2-3--Substitution-and-J where
```

# Lecture 2-3: Substitution and J

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y : A
    n : ℕ
```
-->

A fundamental principle of equality is that we may substitute equal
things for equal things. Consider a predicate like ``isEvenP``.
If `x` and `y` are natural numbers so that `x ≡ y`, and we know that
`isEvenP x`, then we should certainly be able to conclude that
`isEvenP y`.

Generally speaking, given a type family `B : A → Type`, thought of as
a predicate, and a path `p : x ≡ y` in the type `A`, then `subst B p :
B x → B y` is the function that substitutes `x` for `y` in things of
type `B x`.

```
subst : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
```

There is nothing we've seen that lets us do this, so we'll need a new
primitive notion. To see exactly what primitive notion we are missing,
consider that we haven't yet said what a path `I → Type` should be.

Taking a cue from homotopy theory, we could expect that a path between
spaces would be a continuous deformation of one space into another ---
a so-called "homotopy equivalence". In particular, then, if we have a
path `A : I → Type`, we should be able to "continuously move" an
element `a : A i0` to some element of `A i1`. This is called
"transporting" the element `a` from `A i0` to `A i1` along the path of
types `A`. Agda axiomatizes this idea with a function called
``transport``.

```
transport : A ≡ B → A → B
```

::: Aside:
Well, actually, ``transport`` is defined via a slightly more
general operation unhelpfully called ``transp``, which we will
return to in Lecture 2-5.
```
transport p a = transp (λ i → p i) i0 a
```
:::

Using ``transport``, we can define ``subst`` by transporting
in the path of types `(λ i → B (p i)) : B x ≡ B y`. We know the
endpoints of this path are correct because `p i0` computes to `x` and
`p i1` computes to `y`.

```
subst B p b = transport (λ i → B (p i)) b
```

Our first application of ``subst``, is showing that there is no
path from ``true`` to ``false`` in ``Bool``, and vice
versa.

```
true≢false : ¬ true ≡ false
true≢false p = subst (λ b → true ≡Bool b) p tt
```

Let's take a minute to make sure we understand what's going on here.

Remember that ``¬`` is defined to be simply functions into
``∅``, so ``true≢false`` is a function `true ≡ false → ∅`.
That is, to prove that ``true`` doesn't equal ``false``, we
assume it does and derive a contradiction. How do we do this?

Well, we have by definition that `true ≡Bool true` is
``⊤`` and that `true ≡Bool false` is ``∅``. If we're given a
path `p : true ≡ false`, then we could replace the second
``true`` in `true ≡Bool true` with ``false`` using
substitution, to get an element of `true ≡Bool false`, which would
finish our proof.

The family we are substituting in is therefore `(λ b → true ≡Bool b)`.
The resulting term `subst (λ b → true ≡Bool b) p` is a function `true
≡Bool true → true ≡Bool false`, so unwinding the definition of
``≡Bool``, a function `⊤ → ∅`. This we can simply feed
``tt`` to obtain an element of ``∅``, our contradiction.

Give it a try in the reverse:

```
false≢true : ¬ false ≡ true
-- Exercise:
false≢true p = {!!}
```

While we're here, we can show that the constructors for ``ℕ`` and
``⊎`` are also disjoint. These proofs all go roughly the same
way.

```
zero≢suc : ¬ zero ≡ suc n
-- Exercise:
zero≢suc p = {!!}

suc≢zero : ¬ suc n ≡ zero
-- Exercise: (Hint: use symmetry!)
suc≢zero p = {!!}

IsInl : A ⊎ B → Type
-- Exercise:
IsInl s = {!!}

inl≠inr : ¬ inl x ≡ inr y
-- Exercise:
inl≠inr path = {!!}

inr≠inl : ¬ inr x ≡ inl y
-- Exercise:
inr≠inl path = {!!}
```

mvrnote: possible exercise
```
≤ℕ-to : (x y : ℕ) → x ≤ℕ y → Σ[ z ∈ ℕ ] (x + z ≡ y)
≤ℕ-to zero zero p = zero , refl
≤ℕ-to zero (suc y) p = suc y , refl
≤ℕ-to (suc x) zero ()
≤ℕ-to (suc x) (suc y) p = fst prev , cong suc (snd prev)
  where prev : Σ[ z ∈ ℕ ] (x + z ≡ y)
        prev = ≤ℕ-to x y p

≤ℕ-fro : (x y : ℕ) → Σ[ z ∈ ℕ ] (x + z ≡ y) → x ≤ℕ y
≤ℕ-fro zero zero x₁ = tt
≤ℕ-fro zero (suc y) x₁ = tt
≤ℕ-fro (suc x) zero x₁ = suc≢zero (snd x₁)
≤ℕ-fro (suc x) (suc y) (z , p) = ≤ℕ-fro x y (z , suc-inj p)
```


## The J Rule

Combining transport with the the De Morgan structure on the interval,
we can show a fundamental but not-so-well-known principle of identity:
Martin-Löf's ``J`` rule.

Recall the ``connection∧`` connection square:

             p
         x - - - > y
         ^         ^
    refl |         | p               ^
         |         |               j |
         x — — — > x                 ∙ — >
            refl                       i

Reading this square in the `i` direction, we can see it as a path
between ``refl`` and `p` which fixes the beginning of the path
`x` but lets the end vary along `p`. We can therefore take any
property of the path `refl : x ≡ x` and transport it to any path `p :
x ≡ y` beginning with `x`. The ``J``-rule expresses this
principle.

```
JLine : (P : (y : A) → x ≡ y → Type ℓ) (p : x ≡ y)
        → P x refl ≡ P y p
-- Exercise:
JLine P p i = {!!}

J : (P : (y : A) → x ≡ y → Type ℓ) (r : P x refl)
    (p : x ≡ y) → P y p
J P r p = transport (JLine P p) r
```

If we think of the dependent type `P` as a property, then the
``J`` rule says that to prove `P y p` for all `y : A` and `p : x
≡ y`, it suffices to prove `P` just when `y` is `x` and the path `p`
is ``refl``. For this reason, the ``J`` rule is sometimes
known as "path induction" since it resembles an induction principle
like ``Bool-ind`` or ``ℕ-ind``: proving a property of all
elements of a type by proving the property for specific cases.

For comparison:

* Induction for ``Bool``: To prove `P b` for all `b : Bool`, it
  suffices to prove `P true` and `P false`.
* Induction for ``ℕ``: To prove `P n` for all `n : ℕ`, it
  suffices to prove `P zero`, and `P (suc n)` assuming that `P n`.
* Induction for ``Path``: To prove `P y p` for all elements `y`
  and paths `p`, it suffices to prove `P x refl`.

The induction principle for ``Bool`` includes a convenient
computation rule: if `f b : P b` is defined by induction from `x : P
true` and `y : P false`, then if we know `b` concretely then we get
back exactly the corresponding input we used: `f true = x` and `f
false = y` by definition. We can prove a similar fact for the ``J`` rule,
but it is only a path and not a definitional equality.

```
JRefl : (P : (y : A) → x ≡ y → Type ℓ) (r : P x refl)
      → J P r refl ≡ r
JRefl P r i = transp (λ _ → P _ refl) i r
```

Right now we don't have the tools to understand the definition of
``JRefl``, but when we cover ``transp`` in Lecture 2-5, we will
recognize the above definition as exactly ``transport-refl``.

Note that ``subst`` can be seen as a special case of the
``J`` rule where the type family ``P`` is constant.

```
substFromJ : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
substFromJ B p b = J (λ y _ → B y) b p

_ : (B : A → Type ℓ) → (p : x ≡ y) → substFromJ B p ≡ subst B p 
_ = λ B p → refl
```

There's a very subtle point here that we would like to highlight. In
the above definition, we used ``J`` to define an element of ``B
y`` given that we already had an element ``b : B x``. But
we could also have used ``J`` to define the function ``B x → B
y`` in its entirety.

```
substFromJ' : (B : A → Type ℓ) → (p : x ≡ y) → (B x → B y)
substFromJ' {x = x} B p = J (λ y p → B x → B y) (idfun (B x)) p
```

Why does this work? Well, we have to produce a function `B x → B y`
when `y` is in fact the same as `x`, but this is easy: we have
`idfun (B x)`.

This no longer computes exactly to ``subst``, but we can still
prove them to be the same using ``J`` and ``JRefl``.

djnote: this is actually kinda hard... maybe we should tease it and do it in
2.5?
djnote: it also didn't work without bringing in the metavariables

```
substFromJ'-check : {A : Type ℓ} (B : A → Type ℓ) {x y : A} → (p : x ≡ y) → substFromJ' B p ≡ subst B p
substFromJ'-check B {x = x} = J (λ _ p → substFromJ' B p ≡ subst B p) whenRefl
  where whenRefl : substFromJ' B refl ≡ subst B refl
        whenRefl i b = transport (λ _ → B x) (JRefl {x = x} (λ _ _ → B x) b i)
```


## Encode-Decode

One lingering question is what paths are in the inductive types we
have seen (``⊤``, ``∅``, ``Bool``, ``ℕ`` and
``⊎``). There is a general way these constructions go for
inductive types, known as the "encode-decode" method, originally due
to Dan Licata.

Let's take ``Bool`` as our first example. We already have a
candidate for what paths in ``Bool`` should be, that is,
``≡Bool``. We'll call this type the ``code`` for paths in
``Bool``, so that an arbitrary path in ``Bool`` can be
turned into a code for a path.

```
≡≃≡Bool : (x y : Bool) → (x ≡ y) ≃ (x ≡Bool y)
≡≃≡Bool x y = equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : Bool → Bool → Type
    code x y = x ≡Bool y
```

We need an ``encode`` function that takes paths in ``Bool``
to codes, in this case, elements of ``≡Bool``. It is easy to do
this for paths corresponding to reflexivity:

```
    encodeRefl : (x : Bool) → code x x
    encodeRefl true = tt
    encodeRefl false = tt
```

It's not strange that ``false`` is sent to ``tt``: remember
that `encodeRefl false` is supposed to encode the fact that `false ≡
false`, and this is certainly true!

And now the ``J`` rule allows us to extend this to all
paths. Specifically, we use ``J`` for the type family `code x :
(y : Bool) → Type`.

```
    encode : (x y : Bool) → x ≡ y → code x y
    encode x y = J (λ z _ → code x z) (encodeRefl x)
```

Similarly, we need a ``decode`` function that turns codes back
into ordinary paths. Looking at `x ≡Bool y`, once we split `x` and `y`
into cases we know exactly the type is and can act accordingly. Either
the endpoints are the same, in which case we have ``refl``, or
the endpoints are different, in which case `x ≡Bool y` is ``∅``
and we have a contradiction.

```
    decode : (x y : Bool) → code x y → x ≡ y
    decode true true _ = refl
    decode true false e = ∅-rec e
    decode false true e = ∅-rec e
    decode false false _ = refl
```

That this is a section is similar, after splitting into cases it's
easy:

```
    to-fro : (x y : Bool) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro p = {!!}
```

For the retract, we have to use ``J`` again. We check first that
we have the retraction property for the path ``refl``.

```
    fro-to-Refl : (x : Bool) → decode x x (encode x x refl) ≡ refl
    fro-to-Refl true = refl
    fro-to-Refl false = refl
```

And the ``J`` rule is exactly what is required to extend this to
all paths.

```
    fro-to : (x y : Bool) → isRetract (encode x y) (decode x y) 
    fro-to x y = J (λ c p → decode x c (encode x c p) ≡ p) (fro-to-Refl x)
```

This completes the equivalence!

These encode-decode proofs have a similar shape. Let's summarise what
we did, noting what was unique to ``Bool`` and what we can re-use
for an arbitrary type.

<!--
```
module EncodePattern
  (X : Type)
  (code : X → X → Type)
  (encodeRefl : (x : X) → code x x)
  (decode : (x y : X) → code x y → x ≡ y)
  (fro-to-Refl : (x : X) → decode x x (subst (λ z → code x z) refl (encodeRefl x)) ≡ refl)
  where
```
-->

We start with a type `X` with the goal of characterising paths `x ≡ y`
in `X`. We make a guess at the answer as a type family `code : X → X →
Type` with the idea that `code x y` will be equivalent to `x ≡ y`.
Choosing `code` will involve some creativity or luck, but it can
usually be intuited from the definition of `X`. As a rule of thumb,
the path types of inductive types should also be describable as
inductive types themselves; we want `code x y` to be an inductive
type.

For our guess to pass the smell test, we should at least be able to
define a function `encodeRefl : (x : X) → code x x` corresponding to
reflexivity. Without knowing anything else, we can make the general
definition

```
  encode : (x y : X) → x ≡ y → code x y
  encode x y p = J (λ z _ → code x z) (encodeRefl x) p
```

Next we need a decoding map `decode : (x y : X) → code x y → x ≡ y`.
So long as we choose ``code`` so that it has a nice mapping-out
property --- for example, when it is an inductive type --- this should
be easy. The proof there is a ``section`` should be similarly
easy, because it also involves mapping out of ``code``.

All that remains is to prove we have a ``retract``. in this case,
we need a function with type
  `fro-to : (x y : X) → decode x y (encode x y p) ≡ p`.
If `p` happens to be ``refl`` this is easy, because
``encode`` is defined in terms of ``encodeRefl``, so suppose
we have `fro-to-Refl : (x : X) → decode x x (encode x x refl) ≡ refl)`.
The ``J`` rule extends this to a general path.

```
  fro-to : (x y : X) → isRetract (encode x y) (decode x y) 
  fro-to x y = J (λ c p → decode x c (encode x c p) ≡ p) (fro-to-Refl x)
```

Try characterising the paths in ``⊤``. This should essentially be
the same as the proof for ``Bool``, but with half of the cases
deleted.

```
≡≃≡⊤ : (x y : ⊤) → (x ≡ y) ≃ ⊤
≡≃≡⊤ x y = equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : ⊤ → ⊤ → Type
    code x y = ⊤

    encodeRefl : (x : ⊤) → code x x
    -- Exercise:
    encodeRefl x = {!!}

    encode : (x y : ⊤) → x ≡ y → code x y
    encode x y p = J (λ z _ → code x z) (encodeRefl x) p

    decode : (x y : ⊤) → code x y → x ≡ y
    -- Exercise:
    decode x y c = {!!}

    to-fro : (x y : ⊤) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro x y c = {!!}

    fro-to-Refl : (x : ⊤) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    fro-to-Refl x = {!!}

    fro-to : (x y : ⊤) → isRetract (encode x y) (decode x y) 
    fro-to x y p = J (λ c p → decode x c (encode x c p) ≡ p) (fro-to-Refl x) p
```

::: Aside:
In `code` above, we *don't* case-split on `x` and `y`, because we want
to show that `(x ≡ y) ≃ ⊤` regardless of what `x` and `y` are. If we
case split and write `code tt tt = ⊤` then the types no longer line
up, because Agda doesn't automatically know that every element of ``⊤``
is ``tt``.
:::

For ``ℕ``, we already have a candidate for `code`: ``≡ℕ``.

```
≡≃≡ℕ : (x y : ℕ) → (x ≡ y) ≃ (x ≡ℕ y)
≡≃≡ℕ x y = equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : ℕ → ℕ → Type
    code x y = x ≡ℕ y

    encodeRefl : (x : ℕ) → code x x
    -- Exercise:
    encodeRefl x = {!!}

    encode : (x y : ℕ) → x ≡ y → code x y
    encode x y p = J (λ z _ → code x z) (encodeRefl x) p

    decode : (x y : ℕ) → code x y → x ≡ y
    -- Exercise:
    decode x y c = {!!}

    to-fro : (x y : ℕ) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro x y p = {!!}

    fro-to-Refl : (x : ℕ) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    fro-to-Refl x = {!!}

    fro-to : (x y : ℕ) → isRetract (encode x y) (decode x y) 
    fro-to x y p = J (λ z q → decode x z (encode x z q) ≡ q) (fro-to-Refl x) p
```

And one final application: disjoint unions. We didn't define a
candidate ``≡⊎`` for the paths to be equal to back in Lecture 1-3
as we did with the others, but it's not hard to guess what it should
be. After all, the two sides are supposed to be *disjoint*, and so
there should be no paths between any ``inl`` and ``inr``.

```
_≡⊎_ : {A B : Type} (x y : A ⊎ B) → Type
inl a1 ≡⊎ inl a2 = a1 ≡ a2
inl a ≡⊎ inr b = ∅
inr b ≡⊎ inl a = ∅
inr b1 ≡⊎ inr b2 = b1 ≡ b2
```

::: Aside:
This is not the most general definition of ``≡⊎`` possible: we
make the definition only for `A` and `B` lying in the lowest universe
level. To do this right, we would have to land in `Type (ℓ-max ℓ ℓ')`,
and ``Lift`` the types in the definition to that level. This
doesn't change anything substantial about the encode-decode proof, so
we omit it here to cut down on noise.
:::

For this particular proof, it is more convenient to define `encode`
manually by patterx yatching, rather than using ``J``.

```
≡≃≡⊎ : {A B : Type} (x y : A ⊎ B) → (x ≡ y) ≃ (x ≡⊎ y)
≡≃≡⊎ {A = A} {B = B} x y = equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : (x y : A ⊎ B) → Type
    code x y = x ≡⊎ y

    encode : (x y : A ⊎ B) → x ≡ y → code x y
    encode (inl x) (inl y) p = inl-inj p
    encode (inl x) (inr y) p = ∅-rec (inl≠inr p)
    encode (inr x) (inl y) p = ∅-rec (inr≠inl p)
    encode (inr x) (inr y) p = inr-inj p

    decode : (x y : A ⊎ B) → code x y → x ≡ y
--  Exercise:
    decode x y = {!!}

    to-fro : (x y : A ⊎ B) → isSection (encode x y) (decode x y)
--  Exercise:
    to-fro x y = {!!}

    fro-to-Refl : (x : A ⊎ B) → decode x x (encode x x refl) ≡ refl
--  Exercise:
    fro-to-Refl x = {!!}

    fro-to : (x y : A ⊎ B) → isRetract (encode x y) (decode x y) 
--  Exercise:
    fro-to x y = {!!}
```

Alternatively, you can define `encode` via ``J`` as in the
previous proofs, but you will need to use the ``encodeOnRefl``
helper to get `to-fro` and `fro-to-Refl` going.

```
≡≃≡⊎' : {A B : Type} (x y : A ⊎ B) → (x ≡ y) ≃ (x ≡⊎ y)
≡≃≡⊎' {A = A} {B = B} x y = equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : (x y : A ⊎ B) → Type
    code x y = x ≡⊎ y

    encodeRefl : (c : A ⊎ B) → code c c
--  Exercise:
    encodeRefl c = {!!}

    encode : (x y : A ⊎ B) → x ≡ y → code x y
    encode x y = J (λ k _ → code x k) (encodeRefl x)

    encodeOnRefl : (c : A ⊎ B)  → encode c c refl ≡ encodeRefl c
    encodeOnRefl c = JRefl (λ k _ → code c k) (encodeRefl c)

    decode : (x y : A ⊎ B) → code x y → x ≡ y
--  Exercise:
    decode x y = {!!}

    to-fro : (x y : A ⊎ B) → isSection (encode x y) (decode x y)
--  Exercise: (Hint: split into cases and use `J` on `encodeOnRefl (inl a)`, etc.)
    to-fro x y = {!!}

    fro-to-Refl : (x : A ⊎ B) → decode x x (encode x x refl) ≡ refl
--  Exercise:
    fro-to-Refl x = {!!}

    fro-to : (x y : A ⊎ B) → isRetract (encode x y) (decode x y)
--  Exercise:
    fro-to x y = {!!}
```

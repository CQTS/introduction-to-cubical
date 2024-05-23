```
module 2--Paths-and-Identifications.2-3--Transport-and-J where
```

# Lecture 2-3: Transport and J

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y : A
```
-->

A fundamental principle of equality is that we may substitute equal
things for equal things. Written out, substitution should have this
type signature:

```
subst : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
```

The idea is that if `p : x ≡ y`, then `subst B p : B x → B y` is the
function that substitutes `x` for `y` in things of type `B x`. Think
of `B` as a predicate of some kind, like `isEvenP`{.Agda}. If `x ≡ y`
as elements of `ℕ`{.Agda} and we know that `isEvenP x`, then we should
certainly be able to conclude that `isEvenP y`. There is nothing we've
seen yet that lets us do this, so we'll need a new primitive notion.

To see what we are missing, consider that we haven't said what a path
`I → Type` should be. Taking a cue from homotopy theory, we could
expect that a path between spaces would be a continuous deformation of
one space into another --- a so-called "homotopy equivalence". In
particular, then, if we have a path `A : I → Type`, we should be able
to "continuously move" an element `a : A i0` to some element of `A
i1`. This is called "transporting" the element `a` from `A i0` to `A
i1` along the path of types `A`.

Agda axiomatizes this idea with a function called
`transport`{.Agda}. (Well, actually, `transport`{.Agda} is defined via
a slightly more general operation unhelpfully called `transp`{.Agda},
which we will return to in Lecture 2-4.)

```
transport : {A B : Type ℓ} → A ≡ B → A → B
```
<!--
```
transport p a = transp (λ i → p i) i0 a
```
-->

Using `transport`{.Agda}, we can define `subst`{.Agda} by transporting
in the path of types `(λ i → B (p i)) : B x ≡ B y`. We know the
endpoints of this path are correct because `p i0 = x` and `p i1 = y`.

```
subst B p b = transport (λ i → B (p i)) b
```

As our first application of `subst`{.Agda}, we can show that there is
no path from `true`{.Agda} to `false`{.Agda} in `Bool`{.Agda}, and
vice versa.

```
true≢false : ¬ true ≡ false
true≢false p = subst (λ b → true ≡Bool b) p tt
```

Let's take a minute to make sure we really understand what's going on
here.

Remember that `¬`{.Agda} is simply functions into `∅`{.Agda},
so `true≢false`{.Agda} is a function `true ≡ false → ∅` --- to prove
that `true`{.Agda} doesn't equal `false`{.Agda}, we assume it does and
derive a contradiction. How do we do this?

Well, we have by definition that `true ≡Bool true`{.Agda} is
`⊤`{.Agda} and that `true ≡Bool false` is `∅`{.Agda}. If we're given a
path `p : true ≡ false`, then we could replace the second
`true`{.Agda} in `true ≡Bool true` with `false`{.Agda} using
substitution, to get an element of `true ≡Bool false`, which would
finish our proof. The family we are substituting in is therefore `(λ b
→ true ≡Bool b)`, and so we get `subst (λ b → true ≡Bool b) p` is a
function `true f ≡Bool true → true ≡Bool false`, i.e., a function `⊤ →
∅`. This we can simply feed `tt`{.Agda} to obtain our contradiction.

Give it a try in the reverse:

```
false≢true : ¬ false ≡ true
-- Exercise:
false≢true p = ?
```

## The J Rule

Combining transport with the the De Morgan structure on the interval,
we can define a fundamental but not-so-well-known principle of
identity: Martin-Löf's `J`{.Agda} rule.

```
J : (P : ∀ y → x ≡ y → Type ℓ) (r : P x refl)
    (p : x ≡ y) → P y p
J P r p = transport (λ i → P (p i) (λ j → p (i ∧ j))) r
```

If we think of the dependent type `P` as a property, then the
`J`{.Agda} rule says that to prove `P y p` for all `y : A` and `p : x
≡ y`, it suffices to prove `P` just when `y` is `x` and the path `p`
is `refl`{.Agda}. For this reason, the `J`{.Agda} rule is sometimes
known as "path induction" since it resembles an induction principle:
proving a property of all elements of a type by proving the property
for specific cases.

For comparison:

* Induction for `Bool`{.Agda}: To prove `P b` for all `b : Bool`, it suffices
  to prove `P true` and `P false`.
* Induction for `ℕ`{.Agda}: To prove `P n` for all `n : ℕ`, it suffices to
  prove `P zero`, and `P (suc n)` assuming that `P n`.
* Induction for `Path`{.Agda}: To prove `P y p` for all elements `y`
  and paths `p`, it suffices to prove `P x refl`.

The induction principle for `Bool`{.Agda} includes a convenient
computation rule: if `f b : P b` is defined by induction from `x : P
true` and `y : P false`, then if we know `b` concretely then we get
back exactly the corresponding input we used: `f true = x` and `f
false = y` by definition. We can prove a similar fact for the `J`{.Agda} rule,
but it is only a path and not a definitional equality.

mvrnote: this definition is exactly `transport-refl`{.Agda}, explained in Lecture 2-4
```
JRefl : (P : ∀ y → x ≡ y → Type ℓ) (r : P x refl)
      → J P r refl ≡ r
JRefl P r i = transp (λ _ → P _ refl) i r
```

mvrnote: examples

```
substFromJ : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
substFromJ {x = x} B p b = (J (λ y p → B x → B y) (idfun (B x)) p) b

substFromJ' : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
substFromJ' B p b = J (λ y _ → B y) b p

_ : (B : A → Type ℓ) → (p : x ≡ y) → subst B p ≡ substFromJ' B p
_ = λ B p → refl
```

## Encode-Decode

One lingering question is what paths are in the inductive types we
have seen (`⊤`{.Agda}, `∅`{.Agda}, `Bool`{.Agda}, `ℕ`{.Agda} and
`⊎`{.Agda}). There is a general way these constructions go for
inductive types, known as the "encode-decode" method, originally due
to Dan Licata. mvrnote: link

Let's take `Bool`{.Agda} as our first example. We already have a
candidate for what paths in `Bool`{.Agda} should be, that is,
`≡Bool`{.Agda}. We'll call this type the `code` for paths in
`Bool`{.Agda}.

```
≡Iso≡Bool : (x y : Bool) → Iso (x ≡ y) (x ≡Bool y)
≡Iso≡Bool x y = iso (encode x y) (decode x y) (sec x y) (ret x y)
  where
    code : Bool → Bool → Type
    code x y = x ≡Bool y
```

First we need an `encode`{.Agda} function. It is easy to produce
elements of `code`{.Agda} corresponding to reflexivity:

```
    encodeRefl : (x : Bool) → code x x
    encodeRefl true = tt
    encodeRefl false = tt
```

And now `subst`{.Agda} allows us to extend this to all paths in
`Bool`{.Agda}. mvrnote: or we could phrase it in terms of J?

```
    encode : (x y : Bool) → x ≡ y → code x y
    encode x y p = subst (λ z → code x z) p (encodeRefl x)
```

A `decode`{.Agda} function is not too hard. Once we split `x` and `y`
into cases, we know exactly what type `x ≡Bool y` is and can act
accordingly: either the endpoints are the same, in which case we have
`refl`{.Agda}, or the endpoints are different, in which case `x ≡Bool
y` is empty and we have a contradiction.

```
    decode : (x y : Bool) → code x y → x ≡ y
    decode true true _ = refl
    decode true false e = ∅-rec e
    decode false true e = ∅-rec e
    decode false false _ = refl
```

That this is a section is similar, after splitting into cases:

```
    sec : (x y : Bool) → section (encode x y) (decode x y)
    -- Exercise:
    section p = ?
```

For the retract, we have another trick. The proof is easy if we are
working with the path `refl`{.Agda}, because `encode`{.Agda} is
specified in terms of what it does on `refl`{.Agda}.

```
    retRefl : (x : Bool) → decode x x (encode x x refl) ≡ refl
    retRefl true = refl
    retRefl false = refl
```

And the `J`{.Agda} rule is exactly what is required to extend this to
all paths.

```
    ret : (x y : Bool) → retract (encode x y) (decode x y)
    ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

This completes the isomorphism!

<!--
```
module EncodePattern
  (X : Type)
  (code : X → X → Type)
  (encodeRefl : (x : X) → code x x)
  (decode : (x y : X) → code x y → x ≡ y)
  (retRefl : (x : X) → decode x x (subst (λ z → code x z) refl (encodeRefl x)) ≡ refl)
  where
```
-->

Let's summarise what we did, noting what was unique to `Bool`{.Agda}
and what we can re-use for an arbitrary type.

We start with a type `X` and we want to characterise paths `x ≡ y` in
`X`. We make a guess at the answer as a type family `code : X → X →
Type` with the idea that `code x y` is isomorphic to `x ≡ y`; choosing
`code` will involve some creativity or uck. We should at least be able
to define a function `encodeRefl : (x : X) → code x x` corresponding
to reflexivity.

Without knowing anything else, we can make the general definition

```
  encode : (x y : X) → x ≡ y → code x y
  encode x y p = subst (λ z → code x z) p (encodeRefl x)
```

Next we need a decoding map `decode : (x y : X) → code x y → x ≡ y`.
So long as we choose `code`{.Agda} so that it has a nice mapping-out
property --- for example, when it is an inductive type --- this should
be easy. The proof there is a `section`{.Agda} should be similarly
easy, because it also involves mapping out of `code`{.Agda}.

All that remains is to prove we have a `retract`{.Agda}, in this case,
a we need a function with type `ret : (x y : X) → decode x y (encode x
y p) ≡ p`. If `p` happens to be `refl`{.Agda} this is easy, because
`encode`{.Agda} is defined in terms of `encodeRefl`{.Agda}, so suppose
we have `retRefl : (x : X) → decode x x (encode x x refl) ≡ refl)`.
The `J`{.Agda} rule is exactly what we need to extend this to a
general path.

```
  ret : (x y : X) → retract (encode x y) (decode x y)
  ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

Try characterising the paths in `⊤`{.Agda}. This should essentially be
the same as the proof for `Bool`{.Agda}, but with half of the cases
deleted.

```
≡Iso≡⊤ : (n m : ⊤) → Iso (n ≡ m) ⊤
≡Iso≡⊤ n m = iso (encode n m) (decode n m) (sec n m) (ret n m)
  where
    code : ⊤ → ⊤ → Type
    -- Exercise:
    code x y = ?

    encodeRefl : (x : ⊤) → code x x
    -- Exercise:
    encodeRefl x = ?

    encode : (x y : ⊤) → x ≡ y → code x y
    encode x y p = subst (λ z → code x z) p (encodeRefl x)

    decode : (x y : ⊤) → code x y → x ≡ y
    -- Exercise:
    decode x y c = ?

    sec : (x y : ⊤) → section (encode x y) (decode x y)
    -- Exercise:
    sec x y c = ?

    retRefl : (x : ⊤) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    retRefl x = ?

    ret : (x y : ⊤) → retract (encode x y) (decode x y)
    ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

And try the same for `∅`{.Agda}. (There is also a much shorter way to
prove this isomorphism!) mvrnote: this might be too silly to include

```
≡Iso≡∅ : (X : Type) (n m : ∅) → Iso (n ≡ m) X
-- Exercise:
≡Iso≡∅ X m n = ?
≡Iso≡∅ X () lol baited
≡Iso≡∅' : (X : Type) (n m : ∅) → Iso (n ≡ m) X You can do it the long way of course

    encodeRefl : (x : ∅) → code x x
    encodeRefl ()

    encode : (x y : ∅) → x ≡ y → code x y
    encode x y p = subst (λ z → code x z) p (encodeRefl x)

    decode : (x y : ∅) → code x y → x ≡ y
    decode ()

    sec : (x y : ∅) → section (encode x y) (decode x y)
    sec ()

    retRefl : (x : ∅) → decode x x (encode x x refl) ≡ refl
    retRefl ()

    ret : (x y : ∅) → retract (encode x y) (decode x y)
    ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

For `ℕ`{.Agda}, we also already have a candidate for `code`, that is,
`≡ℕ`{.Agda}.

```
≡Iso≡ℕ : (n m : ℕ) → Iso (n ≡ m) (n ≡ℕ m)
≡Iso≡ℕ n m = iso (encode n m) (decode n m) (sec n m) (ret n m)
  where
    code : ℕ → ℕ → Type
    code n m = n ≡ℕ m

    encodeRefl : (n : ℕ) → code n n
    -- Exercise:
    encodeRefl n = ?

    encode : (n m : ℕ) → n ≡ m → code n m
    encode n m p = subst (λ z → code n z) p (encodeRefl n)

    decode : (n m : ℕ) → code n m → n ≡ m
    -- Exercise:
    decode n m c = ?

    sec : (x y : ℕ) → section (encode x y) (decode x y)
    -- Exercise:
    sec x y p = ?

    retRefl : (x : ℕ) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    retRefl x = ?

    ret : (x y : ℕ) → retract (encode x y) (decode x y)
    -- Exercise:
    ret x y p = ?
```

And one final application: disjoint unions. We haven't yet got a
candidate `≡⊎`{.Agda} for the paths to be equal to, but it's not hard
to guess what it should be. After all, the two sides are supposed to
be *disjoint*, and so there should be no paths between an `inl`{.Agda}
and and `inr`{.Agda}.

mvrnote: Adding universe levels means lifting `∅` unfortunately. should we just do it?

```
_≡⊎_ : {A B : Type} (x y : A ⊎ B) → Type
inl a1 ≡⊎ inl a2 = a1 ≡ a2
inl a ≡⊎ inr b = ∅
inr b ≡⊎ inl a = ∅
inr b1 ≡⊎ inr b2 = b1 ≡ b2
```

For the proof, it is more convenient to define `encode` manually rather
than via `subst`{.Agda}.

```
≡Iso≡⊎ : {A B : Type} (x y : A ⊎ B) → Iso (x ≡ y) (x ≡⊎ y)
≡Iso≡⊎ {A = A} {B = B} x y = iso (encode x y) (decode x y) (sec x y) (ret x y)
  where
    code : (x y : A ⊎ B) → Type
    code x y = x ≡⊎ y

    encodeRefl : (c : A ⊎ B) → code c c
--  Exercise:
--  encodeRefl c = ?
    encodeRefl (inl a) = refl
    encodeRefl (inr b) = refl

    encode : (x y : A ⊎ B) → x ≡ y → code x y
    encode x y p = J (λ k _ → code x k) (encodeRefl x) p

    decode : (x y : A ⊎ B) → code x y → x ≡ y
--  Exercise:
--  decode x y = ?
    decode (inl _) (inl _) = cong inl
    decode (inr _) (inr _) = cong inr

    encodeOnRefl : (c : A ⊎ B)  → encode c c refl ≡ encodeRefl c
    encodeOnRefl c = JRefl (λ c' _ → code c c') (encodeRefl c)

    sec : (x y : A ⊎ B) → section (encode x y) (decode x y)
--  Exercise:
--  sec x y = ?
    sec (inl a) (inl _) = J (λ a' p → encode (inl a) (inl a') (cong inl p) ≡ p) (encodeOnRefl (inl a))
    sec (inr b) (inr _) = J (λ b' p → encode (inr b) (inr b') (cong inr p) ≡ p) (encodeOnRefl (inr b))

    retRefl : (x : A ⊎ B) → decode x x (encode x x refl) ≡ refl
--  Exercise:
--  retRefl x = ?
    retRefl (inl x) = cong (cong inl) (encodeOnRefl (inl x))
    retRefl (inr x) = cong (cong inr) (encodeOnRefl (inr x))

    ret : (x y : A ⊎ B) → retract (encode x y) (decode x y)
--  Exercise:
--  ret x y = ?
    ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

mvrnote: an alternative that avoids `encodeOnRefl`. Which is better?

```
inl-inj : {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inl-inj {A = A} {x = x} path = cong f path where
  f : A ⊎ B → A
  f (inl x) = x
  f (inr _) = x

inr-inj : {A : Type ℓ} {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inr-inj {B = B} {x = x} path = cong f path where
  f : A ⊎ B → B
  f (inl _) = x
  f (inr x) = x

inl≠inr : {A : Type ℓ} {B : Type ℓ'} {x : A} {y : B} → ¬ inl x ≡ inr y
inl≠inr path = subst (λ { (inl x) → ⊤ ; (inr x) → ∅ }) path tt

inr≠inl : {A : Type ℓ} {B : Type ℓ'} {x : A} {y : B} → ¬ inr x ≡ inl y
inr≠inl path = inl≠inr (sym path)

≡Iso≡⊎' : {A B : Type} (x y : A ⊎ B) → Iso (x ≡ y) (x ≡⊎ y)
≡Iso≡⊎' {A = A} {B = B} x y = iso (encode x y) (decode x y) (sec x y) (ret x y)
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
--  decode x y = ?
    decode (inl _) (inl _) = cong inl
    decode (inr _) (inr _) = cong inr

    sec : (x y : A ⊎ B) → section (encode x y) (decode x y)
--  Exercise:
--  sec x y = ?
    sec (inl x) (inl y) c = refl
    sec (inr x) (inr y) c = refl

    retRefl : (x : A ⊎ B) → decode x x (encode x x refl) ≡ refl
--  Exercise:
--  retRefl x = ?
    retRefl (inl x) = refl
    retRefl (inr x) = refl

    ret : (x y : A ⊎ B) → retract (encode x y) (decode x y)
--  Exercise:
--  ret x y = ?
    ret x y = J (λ c p → decode x c (encode x c p) ≡ p) (retRefl x)
```

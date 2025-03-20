<!--
```
module 3--Topics.3-1--Structure-Identity-Principle where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types
open import 2--Paths-and-Identifications.2-9--Contractible-Maps

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level -- mvrnote: standardise
    ℓ₁ ℓ₂ ℓ₁' ℓ₂' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
```
-->


# Lecture 3-1: The Structure Identity Principle

mvrnote: a lot of the definition names in this file could be improved.

In Lecture 2-X we saw how univalence can be used to show that paths
between types the same as equivalences between those types. But what
if our types have extra structure, like algebraic operations or
axioms? In this Lecture, we extend univalence to the *Structure
Identity Principle*, which shows that paths between structured types
are equivalent to structure-preserving equivalences between those
types.

We'll be following the paper [Internalizing representation
independence with univalence], by Angiuli, Cavallo, Mörtberg and
Zeuner.

[Internalizing representation independence with univalence]: https://dl.acm.org/doi/10.1145/3434293 

What exactly is "structure"? A structure on a type is some collection
of functions involving that type and axioms that those functions have
to satisfy. To describe that collection, we will simply use a function
from types to types: the input type is the "carrier" type of the
structure, and the output type is the extra data that that is
necessary to equip the carrier with the specified structure.

```
StrNotion : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
StrNotion ℓ ℓ' = Type ℓ → Type ℓ'
``` 

Among the simplest notions of structure is the structure of a "magma",
which is a binary operation that need not satisfy any special
properties at all.

```
Magma-Str : StrNotion ℓ ℓ
Magma-Str X = X → X → X
```

So, to say that a type `X` is a magma, that is, `X` has a magma
structure, we have to equip it with an element of `Magma-Str X`. The
type of all magmas (with a fixed universe level) is then:

```
record Magmaʳ (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor Magma-data
  field
    type : Type ℓ
    str : Magma-Str type

open Magmaʳ
```

So for example, the natural numbers form a ``Magma``.

```
ℕ-Magmaʳ : Magmaʳ ℓ-zero
ℕ-Magmaʳ .type = ℕ 
ℕ-Magmaʳ .str = _+ℕ_
```

Show that the booleans form a ``Magma`` under ``and``.

```
Bool-and-Magmaʳ : Magmaʳ ℓ-zero
-- Exercise:
Bool-and-Magmaʳ = {!!}
```

A single type can support many non-equal versions of the same
structure. The type ``Bool`` can just as well be equipped with the
structure of a magma that uses ``or``.

We usually want to know that our operations obey some axioms. For
example, a "semigroup" is a type with an *associative* binary
operation.

```
Semigroup-Str : StrNotion ℓ ℓ
Semigroup-Str X = 
  Σ[ _·_ ∈ (X → X → X) ] 
  ((x y z : X) → x · (y · z) ≡ (x · y) · z)

record Semigroupʳ (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor Semigroup-data
  field
    type : Type ℓ
    str : Semigroup-Str type

open Semigroupʳ
```

And if there's an identity element for the operation, we have a
monoid:

```
Monoid-Str : StrNotion ℓ ℓ
Monoid-Str X =
  Σ[ e ∈ X ]
  Σ[ _·_ ∈ (X → X → X) ]
  ((x y z : X) → x · (y · z) ≡ (x · y) · z)
  × ((x : X) → e · x ≡ x)
  × ((x : X) → x · e ≡ x)

record Monoidʳ (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor Monoid-data
  field
    type : Type ℓ
    str : Monoid-Str type

open Monoidʳ
```

We have already seen that addition of natural numbers is associative
and unital, so we can pack those proofs together to so this shows that
``ℕ`` is also a monoid:

```
ℕ-Monoid : Monoidʳ ℓ-zero
ℕ-Monoid .type = ℕ 
ℕ-Monoid .str = zero , _+ℕ_ , +ℕ-assoc , +ℕ-idl , +ℕ-idr
```

Notions of structure like this are what we are going to generalise.
Given a notion of structure `S : Type ℓ → Type ℓ'`, an `S`-structured
type is an element of

```
record Type-with (ℓ : Level) (S : StrNotion ℓ ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
  constructor Type-with-data
  field
    type : Type ℓ
    str : S type

open Type-with

explode-Type-with : {ℓ : Level} {S : StrNotion ℓ ℓ'} 
  → Type-with ℓ S ≃ (Σ[ X ∈ Type ℓ ] S X)
explode-Type-with 
  = inv→equiv (λ t → t .type , t .str) 
              (λ p → Type-with-data (p .fst) (p .snd)) 
              (λ _ → refl) 
              (λ _ → refl)
```

So, we reconstruct our ``Magma`` and ``Monoid`` types as

```
Magma : (ℓ : Level) → Type (ℓ-suc ℓ)
Magma ℓ = Type-with ℓ Magma-Str

Monoid : (ℓ : Level) → Type (ℓ-suc ℓ)
Monoid ℓ = Type-with ℓ Monoid-Str

ℕ-Magma : Magma ℓ-zero
ℕ-Magma .type = ℕ
ℕ-Magma .str = _+ℕ_

Bool-and-Magma : Magma ℓ-zero
Bool-and-Magma .type = Bool 
Bool-and-Magma .str = _and_
```

::: Caution:
The definitions of ``Magma`` and ``Monoid`` above should more properly
be called `∞-Magma` and `∞-Monoid`, because we have not made sure that
the underlying types `X` are sets. General types have
higher-dimensional paths, of course, and to be well behaved a notion of
structure typically has to 1) kill the higher paths or 2) add
equations explaining how the operations interact with paths. Here's
how option 1) looks for ``Monoids``.

```
Monoid-Set-Str : StrNotion ℓ ℓ
Monoid-Set-Str X =   Σ[ e ∈ X ]
  Σ[ _·_ ∈ (X → X → X) ]
  ((x y z : X) → x · (y · z) ≡ (x · y) · z)
  × ((x : X) → e · x ≡ x)
  × ((x : X) → x · e ≡ x)
  × isSet X

Monoid-Set : (ℓ : Level) → Type (ℓ-suc ℓ)
Monoid-Set ℓ = Σ[ X ∈ Type ℓ ] Monoid-Set-Str X

ℕ-Monoid-Set : Monoid-Set ℓ-zero
ℕ-Monoid-Set = ℕ , zero , _+ℕ_ , +ℕ-assoc , +ℕ-idl , +ℕ-idr , isSet-ℕ
```
:::


## Structured Equivalences

Not all functions between structured types respect the structure that
the types come with. For magmas, semigroups, monoids, groups and so
on, we are only interested in *homomorphisms*: those functions that
respect the underlying binary operation. This is easy to describe as a
type.

```
isMagmaHom : (A B : Magma ℓ) → (A .type → B .type) → Type ℓ
isMagmaHom (Type-with-data A _·A_) (Type-with-data B _·B_) f
  = (a₁ a₂ : A) → f (a₁ ·A a₂) ≡ (f a₁) ·B (f a₂)
```

The function `isZero : ℕ → Bool` is a homomorphism, as long as we
choose the right ``Magma`` structure on both sides.

```
isZero-isHom : isMagmaHom ℕ-Magma Bool-and-Magma isZero
-- Exercise:
isZero-isHom a a' = {!!}
```

An equivalence *of magmas* is an ordinary equivalence between types so
that the underlying function is a homomorphism in this above sense.
(``isZero`` is of course not an equivalence.)

```
_≃[Magma]_ : (A B : Magma ℓ) → Type ℓ
A ≃[Magma] B = Σ[ e ∈ A .type ≃ B .type ] (isMagmaHom A B (e .map))
```

Again, this situation is what we want to generalise to other notions
of structure. Let us define a "notion of structured equivalence" to be
the extra information that an equivalence needs in order to respect
the structures on the types at either end. In the magma case, this is
the ``isMagmaHom`` type. A structured equivalence is then an
equivalence together with an instance of this information.

```
StrEquivNotion : (S : StrNotion ℓ ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrEquivNotion S ℓ' = (A B : Type-with _ S) → A .type ≃ B .type → Type ℓ'

record StrEquiv {S : StrNotion ℓ ℓ'} (ι : StrEquivNotion S ℓ'') (A : Type-with ℓ S) (B : Type-with ℓ S) : Type (ℓ-max ℓ ℓ'') where
  constructor StrEquiv-data
  field
    eq : A .type ≃ B .type
    proof : ι A B eq

open StrEquiv

explode-StrEquiv : {S : StrNotion ℓ ℓ'} {ι : StrEquivNotion S ℓ''} {A : Type-with ℓ S} {B : Type-with ℓ S}
  → StrEquiv ι A B ≃ (Σ[ e ∈ A .type ≃ B .type ]  ι A B e)
explode-StrEquiv 
  = inv→equiv (λ t → t .eq , t .proof)
              (λ p → StrEquiv-data (p .fst) (p .snd))
              (λ _ → refl)
              (λ _ → refl)
```

To make this easier to read, we'll add some nicer syntax for these
structured equivalences.

```
_≃[_]_ : {S : StrNotion ℓ ℓ'} → (A : Type-with ℓ S) (ι : StrEquivNotion S ℓ'') (B : Type-with ℓ S) → Type (ℓ-max ℓ ℓ'')
A ≃[ ι ] B = StrEquiv ι A B

Magma-EquivNotion : StrEquivNotion Magma-Str ℓ
Magma-EquivNotion A B e = isMagmaHom A B (e .map)
```

How do we know when we've chosen the right notion of structure for our
equivalences? Well, the crucial feature of equivalences is univalence;
that equivalences between types can be turned into paths in the
universe. We will use this as a guide for our structured equivalences.
Whatever the notion of structured equivalence is, it should be
possible to turn it into a path between the structures, as a path-over
the path between types given by univalence. That is, we will seek to
inhabit the following type.

```
StrEquivNotion-univalent : (S : StrNotion ℓ ℓ') (ι : StrEquivNotion S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
StrEquivNotion-univalent S ι =
  {A B : Type-with _ S} (e : A .type ≃ B .type)
  → ι A B e ≃ PathP (λ i → S (ua e i)) (A .str) (B .str)
```

For our ``Magma-EquivNotion``, this is:

```
≃[Magma]-univalent : {A B : Magma ℓ} (e : A .type ≃ B .type)  →
  isMagmaHom A B (e .map) ≃ PathP (λ i → Magma-Str (ua e i)) (A .str) (B .str)
```

We can indeed prove this, by gluing together lots of equivalences that
we've already shown in previous lectures. It's boring and fiddly, so
we'll just do it for you.

<!--
```
funexthalf-≃ : {A : Type ℓ} {B : I → Type ℓ'}
  {f : A → B i0} {g : A → B i1}
  → ((x₀ : A) (x₁ : A) → Path A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A → B i) f g
funexthalf-≃ {A = A} {B = B} {f = f} {g = g} =
  ((x₀ x₁ : A) → Path A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃⟨ Π-map-cod≃ (λ x₀ → J-ump-≃ (λ y _ → PathP B (f x₀) (g y))) ⟩
  ((x : A) → PathP B (f x) (g x))
  ≃⟨ funextP-≃ ⟩
  PathP (λ i → A → B i) f g ∎e

funextP-ump-≃ : {A : I → Type ℓ} {B : I → Type ℓ'}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x₀ : A i0) (x₁ : A i1) → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g
funextP-ump-≃ {A = A} {B = B} {f = f} {g = g} =
  J
  (λ A1 A → {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x₀ : A i0) (x₁ : A i1) → PathP (λ i → A i) x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g)
  funexthalf-≃ (λ i → A i)

≃[Magma]-univalent {A = A} {B = B} e = step1 ∘e step2 ∘e invEquiv step3
  where
  step1 : {A : I → Type ℓ} {B : I → Type ℓ'} {C : I → Type ℓ''}
    {f : A i0 → B i0 → C i0} {g : A i1 → B i1 → C i1}
    → ((x₀ : A i0) (x₁ : A i1) → PathP A x₀ x₁ → (x₀' : B i0) (x₁' : B i1) → PathP B x₀' x₁' → PathP C (f x₀ x₀') (g x₁ x₁'))
    ≃ PathP (λ i → A i → B i → C i) f g
  step1 = funextP-ump-≃ ∘e Π-map-cod≃ (λ _ → Π-map-cod≃ (λ _ → Π-map-cod≃ (λ _ → funextP-ump-≃)))

  step2 : ((x₀ : A .type) → (x₁ : B .type)
           → e .map x₀ ≡ x₁
           → (x₀' : A .type) → (x₁' : B .type)
           → e .map x₀' ≡ x₁'
           → e .map (str A x₀ x₀') ≡ (str B x₁ x₁'))
        ≃ ((x₀ : A .type) → (x₁ : B .type)
           → PathP (λ z → ua e z) x₀ x₁
           → (x₀' : A .type) → (x₁' : B .type)
           → PathP (λ z → ua e z) x₀' x₁'
           → PathP (λ z → ua e z) (str A x₀ x₀') (str B x₁ x₁'))
  step2 = Π-map-cod≃ λ x₀ → Π-map-cod≃ λ x₁ → →-map-≃ (invEquiv (Path≃ua-PathP e)) (Π-map-cod≃ λ x₀' → Π-map-cod≃ λ x₁' → →-map-≃ (invEquiv (Path≃ua-PathP e)) (Path≃ua-PathP e))

  step3 : ((x₀ : A .type) (x₁ : B .type)
           → e .map x₀ ≡ x₁
           → (x₀' : A .type) (x₁' : B .type)
           → e .map x₀' ≡ x₁'
           → e .map (str A x₀ x₀') ≡ (str B x₁ x₁'))
    ≃ isMagmaHom A B (e .map)
  step3 = Π-map-cod≃ λ x₀ → ((Π-map-cod≃ λ x₀' → J-ump-≃ _) ∘e J-ump-≃ _)
```
-->

The upshot of knowing ``≃[Magma]-univalent`` is that we can upgrade
univalence to something that works on entire magmas and not just
their underlying types. This is what we call the *structure identity
principle*.

```
SIP-Magma : {A B : Magma ℓ} → (A ≃[ Magma-EquivNotion ] B) ≃ (A ≡ B)
SIP-Magma {A = A} {B = B} =
  (A ≃[ Magma-EquivNotion ] B)
    ≃⟨ explode-StrEquiv ⟩
  Σ[ e ∈ (A .type ≃ B .type) ] Magma-EquivNotion A B e
    ≃⟨ Σ-map-≃ (invEquiv univalence) ≃[Magma]-univalent ⟩
  Σ[ p ∈ (A .type ≡ B .type) ] PathP (λ i → Magma-Str (p i)) (A .str) (B .str)
    ≃⟨ ΣPath≃PathΣ ⟩
  (A .type , A .str) ≡ (B .type , B .str)
    ≃⟨ ap-≃ (invEquiv explode-Type-with) ⟩
  (A ≡ B)
    ∎e
```

This works completely generically, using the abstract setup we have
been developing so far. Try putting the pieces together!

```

module _ {S : StrNotion ℓ ℓ'} {ι : StrEquivNotion S ℓ'}
  (θ : StrEquivNotion-univalent S ι) (A B : Type-with ℓ S)
  where

  SIP : (A ≃[ ι ] B) ≃ (A ≡ B)
  -- Exercise:
  SIP = {!!}

  sip : (A ≃[ ι ] B) → A ≡ B
  sip = SIP .map
```


## Transferring Proofs

Alright, that was a lot of set-up, so let's try and get some payoff.
Once we have paths between structures, we can attempt to transfer
proofs between those structures.

First, an easy warmup. ``Bool`` is also a magma under ``or``, and in
fact the function ``not`` is a structured equivalence between these
two versions of ``Bool`` as a magma.

```
Bool-or-Magma : Magma ℓ-zero
Bool-or-Magma .type = Bool 
Bool-or-Magma .str = _or_

not-isMagmaHom : (a a' : Bool) → not (a or a') ≡ (not a and not a')
not-isMagmaHom true true = refl
not-isMagmaHom true false = refl
not-isMagmaHom false true = refl
not-isMagmaHom false false = refl

not-[Magma]≃ : Bool-or-Magma ≃[ Magma-EquivNotion ] Bool-and-Magma
not-[Magma]≃ .eq = not-≃ 
not-[Magma]≃ .proof = not-isMagmaHom

Bool-or≡Bool-and : Bool-or-Magma ≡ Bool-and-Magma
Bool-or≡Bool-and = sip ≃[Magma]-univalent Bool-or-Magma Bool-and-Magma not-[Magma]≃
```

Way back in Lecture 2-X, we showed that ``or`` is an associative
operation. We can use this path that we just proved to transfer this
proof over to ``and``.

```
or≡and : PathP (λ i → Magma-Str (Bool-or≡Bool-and i .type)) 
  _or_
  _and_
or≡and i = Bool-or≡Bool-and i .str

and-assoc : (m n o : Bool) → m and (n and o) ≡ (m and n) and o
and-assoc = transport (λ i → (m n o : Bool-or≡Bool-and i .type) → 
                         or≡and i m (or≡and i n o) ≡ or≡and i (or≡and i m n) o)
            or-assoc
```

This wasn't too impressive, because ``and-assoc`` would have been easy
enough to prove by hand. But this works for equivalences of any
complexity. For a more interesting example, let's look at a binary
representation of the natural numbers.

We can think of a binary number as being built up from left to right,
one digit at a time. Starting with the empty string ` ` corresponding
to zero, each additional digit doubles the value of all the previous
digits, and then decides whether or not to add 1. For `1101` say, we have

* ` `    corresponds to $0$
* `1`    corresponds to $1 + (2 × 0) = 1$
* `11`   corresponds to $1 + (2 × 1) = 3$
* `110`  corresponds to $0 + (2 × 3) = 6$
* `1101` corresponds to $1 + (2 × 6) = 13$

This is what we want to capture as an inductive data-type, with a
catch: we don't want our binary strings to be allowed to begin with a
string of pointless `0`s. To avoid this, we will replace the "just
multiply by two" option with an "add one and multiply by two" option,
so that we no longer have many different ways to represent zero.

In all, we have partitioned the natural numbers into three categories:
zero, non-zero even (so $n = 2×(1+k)$), or odd (so $n = 1+(2×k)$).

::: Aside:
We've pilfered this encoding from the [redtt] project.

[redtt]: https://github.com/RedPRL/redtt/blob/master/library/cool/nats.red
:::

```
data ℕᵇ : Type where
  zeroᵇ   : ℕᵇ
  2×[1+_] : ℕᵇ → ℕᵇ    -- n → 2 × (1+n) = nonzero even numbers
  1+[2×_] : ℕᵇ → ℕᵇ    -- n → 1 + (2×n) = odd numbers
```

These can be easily converted from and to regular natural numbers. In
one direction by ordinary induction and ``sucᵇ``:

```
sucᵇ : ℕᵇ → ℕᵇ
sucᵇ zeroᵇ     = 1+[2× zeroᵇ ]
sucᵇ 2×[1+ b ] = 1+[2× (sucᵇ b) ]
sucᵇ 1+[2× b ] = 2×[1+ b ]

ℕ→ℕᵇ : ℕ → ℕᵇ
ℕ→ℕᵇ zero = zeroᵇ
ℕ→ℕᵇ (suc n) = sucᵇ (ℕ→ℕᵇ n)
```

In the other direction, by turning the constructors of ``ℕᵇ`` into the
corresponding operations on ``ℕ``.

```
ℕᵇ→ℕ : ℕᵇ → ℕ
-- Exercise: (Use `doubleℕ`!)
ℕᵇ→ℕ b = {!!}
```

These functions are components of an equivalence.

```
ℕᵇ→ℕ-suc : (n : ℕᵇ) → ℕᵇ→ℕ (sucᵇ n) ≡ suc (ℕᵇ→ℕ n)
ℕᵇ→ℕ-suc zeroᵇ       = refl
ℕᵇ→ℕ-suc 2×[1+ b ] i = suc (doubleℕ (ℕᵇ→ℕ-suc b i))
ℕᵇ→ℕ-suc 1+[2× b ]   = refl

ℕᵇ≃ℕ : ℕᵇ ≃ ℕ
ℕᵇ≃ℕ = inv→equiv ℕᵇ→ℕ ℕ→ℕᵇ to-fro fro-to
  where
    to-fro : isSection ℕᵇ→ℕ ℕ→ℕᵇ
    to-fro zero = refl
    to-fro (suc n) =
      ℕᵇ→ℕ (sucᵇ (ℕ→ℕᵇ n)) ≡⟨ ℕᵇ→ℕ-suc (ℕ→ℕᵇ n) ⟩
      suc (ℕᵇ→ℕ (ℕ→ℕᵇ n)) ≡⟨ ap suc (to-fro n) ⟩
      suc n ∎

    sucᵇ-to-doubleℕ : (n : ℕ) → sucᵇ (ℕ→ℕᵇ (doubleℕ n)) ≡ 1+[2× (ℕ→ℕᵇ n)]
    sucᵇ-to-doubleℕ zero      = refl
    sucᵇ-to-doubleℕ (suc n) i = sucᵇ (sucᵇ (sucᵇ-to-doubleℕ n i))

    fro-to : isRetract ℕᵇ→ℕ ℕ→ℕᵇ
    fro-to zeroᵇ = refl
    fro-to 2×[1+ b ] =
      sucᵇ (sucᵇ (ℕ→ℕᵇ (doubleℕ (ℕᵇ→ℕ b)))) ≡⟨ ap sucᵇ (sucᵇ-to-doubleℕ (ℕᵇ→ℕ b)) ⟩
      2×[1+ ℕ→ℕᵇ (ℕᵇ→ℕ b) ]                 ≡⟨ ap 2×[1+_] (fro-to b) ⟩
      2×[1+ b ]                             ∎
    fro-to 1+[2× b ] =
      sucᵇ (ℕ→ℕᵇ (doubleℕ (ℕᵇ→ℕ b))) ≡⟨ sucᵇ-to-doubleℕ (ℕᵇ→ℕ b) ⟩
      1+[2× ℕ→ℕᵇ (ℕᵇ→ℕ b) ]          ≡⟨ ap 1+[2×_] (fro-to b) ⟩
      1+[2× b ]                      ∎

ℕᵇ≡ℕ : ℕᵇ ≡ ℕ
ℕᵇ≡ℕ = ua ℕᵇ≃ℕ
```

Now ``ℕᵇ`` also supports an inductive addition operation, so we can
give it a ``Magma`` structure.

```
_+ℕᵇ_ : ℕᵇ → ℕᵇ → ℕᵇ
zeroᵇ    +ℕᵇ y          = y
2×[1+ b ] +ℕᵇ zeroᵇ     = 2×[1+ b ]
2×[1+ b ] +ℕᵇ 2×[1+ c ] = 2×[1+ sucᵇ (b +ℕᵇ c) ]
2×[1+ b ] +ℕᵇ 1+[2× c ] = sucᵇ 2×[1+ (b +ℕᵇ c) ]
1+[2× b ] +ℕᵇ zeroᵇ     = 1+[2× b ]
1+[2× b ] +ℕᵇ 2×[1+ c ] = sucᵇ 2×[1+ (b +ℕᵇ c) ]
1+[2× b ] +ℕᵇ 1+[2× c ] = sucᵇ 1+[2× (b +ℕᵇ c) ]

infixl 6 _+ℕᵇ_

ℕᵇ-Magma : Magma ℓ-zero
ℕᵇ-Magma .type = ℕᵇ 
ℕᵇ-Magma .str = _+ℕᵇ_
```

The last thing to do is verify that the ``ℕᵇ→ℕ`` function respects
this ``Magma`` strucutre. This involves some pain, but we've done most
of it for you.

```
doubleℕ-+ℕ : (n m : ℕ) → doubleℕ (n +ℕ m) ≡ doubleℕ n +ℕ doubleℕ m
doubleℕ-+ℕ zero m = refl
doubleℕ-+ℕ (suc n) m i = suc (suc (doubleℕ-+ℕ n m i))

ℕᵇ→ℕ-hom : (b c : ℕᵇ) → ℕᵇ→ℕ (b +ℕᵇ c) ≡ (ℕᵇ→ℕ b) +ℕ (ℕᵇ→ℕ c)
ℕᵇ→ℕ-hom zeroᵇ c = refl
ℕᵇ→ℕ-hom 2×[1+ b ] zeroᵇ = ap (suc ∘ suc) (sym (+ℕ-idr (doubleℕ (ℕᵇ→ℕ b))))
ℕᵇ→ℕ-hom 2×[1+ b ] 2×[1+ c ] =
  ℕᵇ→ℕ (2×[1+ b ] +ℕᵇ 2×[1+ c ])                         ≡⟨ refl ⟩
  ℕᵇ→ℕ (2×[1+ sucᵇ (b +ℕᵇ c) ])                          ≡⟨ refl ⟩
  doubleℕ (suc (ℕᵇ→ℕ (sucᵇ (b +ℕᵇ c))))                  ≡⟨ ap (doubleℕ ∘ suc) (ℕᵇ→ℕ-suc (b +ℕᵇ c)) ⟩
  doubleℕ (suc (suc (ℕᵇ→ℕ (b +ℕᵇ c))))                   ≡⟨ ap (doubleℕ ∘ suc ∘ suc) (ℕᵇ→ℕ-hom b c) ⟩
  doubleℕ (suc (suc (ℕᵇ→ℕ b +ℕ ℕᵇ→ℕ c)))                 ≡⟨ ap (doubleℕ ∘ suc) (sym (+ℕ-comm-helper (ℕᵇ→ℕ b) (ℕᵇ→ℕ c))) ⟩
  doubleℕ (suc (ℕᵇ→ℕ b) +ℕ suc (ℕᵇ→ℕ c))                 ≡⟨ doubleℕ-+ℕ (suc (ℕᵇ→ℕ b)) (suc (ℕᵇ→ℕ c)) ⟩
  doubleℕ (suc (ℕᵇ→ℕ b)) +ℕ doubleℕ (suc (ℕᵇ→ℕ c))       ≡⟨ refl ⟩
  ℕᵇ→ℕ (2×[1+ b ]) +ℕ ℕᵇ→ℕ (2×[1+ c ])                   ∎

ℕᵇ→ℕ-hom 2×[1+ b ] 1+[2× c ] =
  ℕᵇ→ℕ (2×[1+ b ] +ℕᵇ 1+[2× c ])                         ≡⟨ refl ⟩
  ℕᵇ→ℕ 1+[2× sucᵇ (b +ℕᵇ c) ]                            ≡⟨ refl ⟩
  suc (doubleℕ (ℕᵇ→ℕ (sucᵇ (b +ℕᵇ c))))                  ≡⟨ ap (suc ∘ doubleℕ) (ℕᵇ→ℕ-suc (b +ℕᵇ c)) ⟩
  suc (doubleℕ (suc (ℕᵇ→ℕ (b +ℕᵇ c))))                   ≡⟨ ap (suc ∘ doubleℕ ∘ suc) (ℕᵇ→ℕ-hom b c) ⟩
  suc (doubleℕ (suc (ℕᵇ→ℕ b +ℕ ℕᵇ→ℕ c)))                 ≡⟨ ap (suc ∘ suc ∘ suc) (doubleℕ-+ℕ (ℕᵇ→ℕ b)(ℕᵇ→ℕ c)) ⟩
  suc (suc (suc (doubleℕ (ℕᵇ→ℕ b) +ℕ doubleℕ (ℕᵇ→ℕ c)))) ≡⟨ ap (suc ∘ suc) (sym (+ℕ-comm-helper (doubleℕ (ℕᵇ→ℕ b)) (doubleℕ (ℕᵇ→ℕ c))))  ⟩
  suc (suc (doubleℕ (ℕᵇ→ℕ b) +ℕ suc (doubleℕ (ℕᵇ→ℕ c)))) ≡⟨ refl ⟩
  (doubleℕ (suc (ℕᵇ→ℕ b)) +ℕ suc (doubleℕ (ℕᵇ→ℕ c)))     ≡⟨ refl ⟩
  ℕᵇ→ℕ (2×[1+ b ]) +ℕ ℕᵇ→ℕ (1+[2× c ])                   ∎

ℕᵇ→ℕ-hom 1+[2× b ] zeroᵇ = ap suc (sym (+ℕ-idr (doubleℕ (ℕᵇ→ℕ b))))

ℕᵇ→ℕ-hom 1+[2× b ] 2×[1+ c ] =
  -- Exercise:
  ℕᵇ→ℕ (1+[2× b ] +ℕᵇ 2×[1+ c ])                         ≡⟨ {!!} ⟩
  ℕᵇ→ℕ 1+[2× sucᵇ (b +ℕᵇ c) ]                            ≡⟨ {!!} ⟩
  suc (doubleℕ (ℕᵇ→ℕ (sucᵇ (b +ℕᵇ c))))                  ≡⟨ {!!} ⟩
  suc (doubleℕ (suc (ℕᵇ→ℕ (b +ℕᵇ c))))                   ≡⟨ {!!} ⟩
  suc (doubleℕ (suc (ℕᵇ→ℕ b +ℕ ℕᵇ→ℕ c)))                 ≡⟨ {!!} ⟩
  suc (doubleℕ (ℕᵇ→ℕ b +ℕ suc (ℕᵇ→ℕ c)))                 ≡⟨ {!!} ⟩
  suc (doubleℕ (ℕᵇ→ℕ b) +ℕ doubleℕ (suc (ℕᵇ→ℕ c)))       ≡⟨ {!!} ⟩
  (suc (doubleℕ (ℕᵇ→ℕ b)) +ℕ (doubleℕ (suc (ℕᵇ→ℕ c))))   ≡⟨ {!!} ⟩
  ℕᵇ→ℕ (1+[2× b ]) +ℕ ℕᵇ→ℕ (2×[1+ c ])                   ∎

ℕᵇ→ℕ-hom 1+[2× b ] 1+[2× c ] =
  -- Exercise:
  ℕᵇ→ℕ (1+[2× b ] +ℕᵇ 1+[2× c ])                         ≡⟨ {!!} ⟩
  ℕᵇ→ℕ 2×[1+ b +ℕᵇ c ]                                   ≡⟨ {!!} ⟩
  (doubleℕ (suc (ℕᵇ→ℕ (b +ℕᵇ c))))                       ≡⟨ {!!} ⟩
  (doubleℕ (suc (ℕᵇ→ℕ b +ℕ ℕᵇ→ℕ c)))                     ≡⟨ {!!} ⟩
  suc (suc (doubleℕ (ℕᵇ→ℕ b +ℕ ℕᵇ→ℕ c)))                 ≡⟨ {!!} ⟩
  suc (suc (doubleℕ (ℕᵇ→ℕ b) +ℕ doubleℕ (ℕᵇ→ℕ c)))       ≡⟨ {!!} ⟩
  (suc (doubleℕ (ℕᵇ→ℕ b))) +ℕ (suc (doubleℕ (ℕᵇ→ℕ c)))   ≡⟨ {!!} ⟩
  (ℕᵇ→ℕ 1+[2× b ]) +ℕ (ℕᵇ→ℕ 1+[2× c ])                   ∎

ℕᵇ≃[Magma]ℕ : ℕᵇ-Magma ≃[ Magma-EquivNotion ] ℕ-Magma
ℕᵇ≃[Magma]ℕ .eq = ℕᵇ≃ℕ
ℕᵇ≃[Magma]ℕ .proof = ℕᵇ→ℕ-hom

ℕᵇ-Magma≡ℕ-Magma : ℕᵇ-Magma ≡ ℕ-Magma
ℕᵇ-Magma≡ℕ-Magma = sip ≃[Magma]-univalent ℕᵇ-Magma ℕ-Magma ℕᵇ≃[Magma]ℕ
```

Now we can transfer proofs about ``ℕ`` to proofs about ``ℕᵇ`` with
essentially no effort. Showing ``+ℕᵇ-assoc`` by hand would be painful!

```
+ℕ≡+ℕᵇ : PathP (λ i → ℕᵇ≡ℕ (~ i) → ℕᵇ≡ℕ (~ i) → ℕᵇ≡ℕ (~ i)) _+ℕ_ _+ℕᵇ_
+ℕ≡+ℕᵇ i = ℕᵇ-Magma≡ℕ-Magma (~ i) .str

+ℕᵇ-assoc : (m n o : ℕᵇ) → m +ℕᵇ (n +ℕᵇ o) ≡ (m +ℕᵇ n) +ℕᵇ o
+ℕᵇ-assoc = 
  transport (λ i → (m n o : ℕᵇ≡ℕ (~ i)) → +ℕ≡+ℕᵇ i m (+ℕ≡+ℕᵇ i n o) 
                                        ≡ +ℕ≡+ℕᵇ i (+ℕ≡+ℕᵇ i m n) o)
  +ℕ-assoc
```

Thank goodness!


## Queues

Let's do an example that points towards some applications in computer
science. Here's a structure we could use for a first-in, first-out
queue:

```
Maybe : Type ℓ → Type ℓ
Maybe A = ⊤ ⊎ A

Queue-Str : Type → StrNotion ℓ ℓ
Queue-Str A X = X × (A → X → X) × (X → Maybe (X × A))
```

There are three components, with the following interpretation:

* `emp`, the empty queue,
* `enq`, which "enqueues" a new element onto the back of the queue,
* `deq`, which "dequeues" an element off the front of the queue,
  either giving back the new queue and the removed element, or giving
  back nothing if the queue is empty.

These are just the raw operations that we would expect a queue to
have, but nothing actually forces it to behave reasonably. (For
example, we could define a ``Queue-Str`` that is just ``⊤`` always,
regardless of what the type `A` is.)

To force the queues to actually do something, we'll want them to
satisfy at least the following axioms:

```
return-or-enq : (Q : Type-with ℓ (Queue-Str A)) → A → Maybe (Q .type × A) → Q .type × A
return-or-enq (Type-with-data Q (emp , enq , deq)) a (inl tt) = emp , a
return-or-enq (Type-with-data Q (emp , enq , deq)) a (inr (q , b)) = enq a q , b

Queue-Axioms : Type-with ℓ (Queue-Str A) → Type ℓ
Queue-Axioms {A = A} (Type-with-data Q (emp , enq , deq)) = 
     (deq emp ≡ inl tt)
   × ((a : A) (q : Q) → deq (enq a q) ≡ inr (return-or-enq (Type-with-data Q (emp , enq , deq)) a (deq q)))
   × ((a a' : A) → (q q' : Q) → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q'))
   × ((q q' : Q) → deq q ≡ deq q' → q ≡ q')
```

In words, these say:

* There's nothing on the front of the empty queue,
* Enqueueing then dequeueing is the same as dequeuing and enqueueing
  (taking care when the queue starts empty)
* Enqueueing is an injective operation
* Dequeueing is an injective operation (when you include the element
  that gets dequeued)

Let's see our first queue implementation: a simple list, where
elements are enqueued onto to the front of the list, and dequeued from
the back of the list.

```
SlowQueue : Type → Type
SlowQueue A = List A

empˢ : SlowQueue A
empˢ = []

enqˢ : A → SlowQueue A → SlowQueue A
enqˢ x xs = x :: xs

deq-func : {X Y : Type ℓ} → (X → Y) → Maybe (X × A) → Maybe (Y × A)
deq-func f = ⊎-map idfun (λ (x , a) → (f x , a))

deqˢ : SlowQueue A → Maybe (SlowQueue A × A)
deqˢ [] = inl tt
deqˢ (x :: []) = inr ([] , x)
deqˢ (x :: x' :: xs) = deq-func (enqˢ x) (deqˢ (x' :: xs))

SlowQueue-model : (A : Type) → Type-with ℓ-zero (Queue-Str A)
SlowQueue-model A .type = SlowQueue A 
SlowQueue-model A .str = empˢ , enqˢ , deqˢ
```

It's pretty easy to show that this model satisfies the properties we
expected.

```
SlowQueue-Axioms : Queue-Axioms (SlowQueue-model A)
SlowQueue-Axioms {A = A} = deq-emp , deq-enq , enq≡enq , deq≡deq
  where 
  deq-emp = refl

  deq-enq : (a : A) (q : SlowQueue A) → deqˢ (enqˢ a q) ≡ inr (return-or-enq (SlowQueue-model A) a (deqˢ q))
  deq-enq a [] = refl
  deq-enq a (x :: []) = refl
  deq-enq a (x :: x' :: q) = 
    deqˢ (enqˢ a (x :: x' :: q)) 
      ≡⟨ ap (λ t → deq-func (enqˢ a) (deq-func (enqˢ x) t)) (deq-enq x' q) ⟩
    deq-func (enqˢ a) (deq-func (enqˢ x) (inr (return-or-enq (SlowQueue-model A) x' (deqˢ q)))) 
      ≡⟨ ap (λ t → inr (return-or-enq (SlowQueue-model A) a (deq-func (enqˢ x) t))) (sym (deq-enq x' q)) ⟩
    inr (return-or-enq (SlowQueue-model A) a (deqˢ (x :: x' :: q))) ∎

  -- You would have had to prove these lemmas when defining `≡≃≡List` in Lecture 2-3!
  head-inj : {x y : A} → {xs ys : List A} → (x :: xs) ≡ (y :: ys) → x ≡ y
  head-inj {x = x} p = ap head p
    where
      head : List A → A
      head [] = x
      head (h :: hs) = h

  tail-inj : {x y : A} → {xs ys : List A} → (x :: xs) ≡ (y :: ys) → xs ≡ ys
  tail-inj {xs = xs} p = ap tail p
    where
      tail : List A → List A
      tail [] = xs
      tail (h :: hs) = hs

  IsHead : List A → Type
  IsHead [] = ⊤
  IsHead (_ :: _) = ∅

  []≢:: : {x : A} → {xs : List A} → ¬ [] ≡ (x :: xs)
  []≢:: p = subst IsHead p tt

  enq≡enq : (a a' : A) (q q' : SlowQueue A) → enqˢ a q ≡ enqˢ a' q' → (a ≡ a') × (q ≡ q')
  enq≡enq a a' q q' r = head-inj r , tail-inj r

  return-or-enq≡return-or-enq : {x x' : A} → {m m' : Maybe (List A × A)}
     → return-or-enq (SlowQueue-model A) x m ≡ return-or-enq (SlowQueue-model A) x' m'
     → (x ≡ x') × (m ≡ m')
  return-or-enq≡return-or-enq {m = inl tt} {inl tt} p = ap snd p , refl
  return-or-enq≡return-or-enq {m = inl tt} {inr x₂} p = ∅-rec ([]≢:: (ap fst p))
  return-or-enq≡return-or-enq {m = inr x₁} {inl tt} p = ∅-rec ([]≢:: (ap fst (sym p)))
  return-or-enq≡return-or-enq {m = inr x₁} {inr x₂} p = head-inj (ap fst p) , ap inr (×≡→≡× (tail-inj (ap fst p) , ap snd p))

  deq≡deq : (q q' : SlowQueue A) → deqˢ q ≡ deqˢ q' → q ≡ q'
  deq≡deq []       [] p           = refl
  deq≡deq []       (x :: q') p    = ∅-rec (inl≢inr (p ∙ deq-enq x q'))
  deq≡deq (x :: q) [] p           = ∅-rec (inr≢inl (sym (deq-enq x q) ∙ p))
  deq≡deq (x :: q) (x' :: q') p i = fst t i :: deq≡deq q q' (snd t) i
    where t = return-or-enq≡return-or-enq (inr-inj (sym (deq-enq x q) ∙∙ p ∙∙ deq-enq x' q'))
```

What makes this "slow"? Well, every time we dequeue, we walk through
the whole list to get to the end element, and reconstruct a new list
that has that element removed.

There is a famous solution to this problem, which replaces the single
list by a pair of lists, one representing the back of the queue and
one representing the front. Elements are enqueued by adding them to
the back list and dequeued by removing them from the front list.
Whenever this front list is empty, we replace it with the *reverse* of
the back list, so that we indeed end up with a first-in, first-out
queue. The cost of using recursion to reach the back queue to deque is
replaced by an occasional "batch" operation which does the work once.

::: Aside:
This kind of "batched" queue
mvrnote: reference "amortised cost"
:::

In the double-list scheme, our functions look like this:

```
enqᵈ : A → List A × List A → List A × List A
enqᵈ x (xs , ys) = (x :: xs , ys)

deqᵈ : List A × List A → Maybe ((List A × List A) × A)
deqᵈ (xs , y :: ys) = inr ((xs , ys) , y)
deqᵈ (xs , []) = flush (reverse xs)
  where flush : List A → Maybe ((List A × List A) × A)
        flush [] = inl tt
        flush (x :: xs) = inr (([] , xs ) , x)
```

Enqueueing is easy enough, we just add `x` to the back list. When
dequeuing, there are two possibilities. If the front list is
non-empty, we can just take the first element as our result. If it's
empty, it must be time to do the batch reverse operation, after which
we can just take the first element of the result.

So, a pair of lists as above represents the same queue as the list
given by:

```
Pair→Queue : List A × List A → SlowQueue A
Pair→Queue (xs , ys) = xs ++ reverse ys
```

The pairs "represent the same queue", in the sense that they are
indistinguishable as long as we only use the functions ``enqᵈ`` and
``deqᵈ``. This works when using the pair of lists as a data structure
in practice, but as defined it doesn't actually satisfy the axioms
we demanded. For example,

```
_ = test-identical
    (deqᵈ ([] , true :: []))
    (deqᵈ (true :: [] , []))
```

The standard solution here is to quotient the type `List A × List A`
by an appropriate equivalence relation, the one that makes pairs of
queues `q₁` and `q₂`equal whenever `Pair→Queue q₁ ≡ Pair→Queue q₂`. In
cubical type theory we can do this nicely by building the notion of
equality we want directly into the type:

```
data FastQueue (A : Type) : Type where
  FQ⟨_,_⟩ : (xs : List A) → (ys : List A) → FastQueue A
  tilt : (xs ys : List A) → (z : A) → FQ⟨ xs ++ [ z ] , ys ⟩ ≡ FQ⟨ xs , ys ++ [ z ] ⟩
  trunc : isSet (FastQueue A)
```

The first constructor gives us our pair of lists. The second
constructor ensures that adding an element to the end of the back list
is the same as adding it to the end of the front list; you can check
that under `Pair→Queue` these two sides end up the same. And the final
constructor truncates our ``FastQueue`` to always be a set.

The empty ``FastQueue`` starts with both lists empty.

```
empᶠ : FastQueue A
empᶠ = FQ⟨ [] , [] ⟩
```

To enqueue, we add to the back list as before, but now we also have to
prove that enqueuing respects the ``tilt`` relation. (The definition
for the ``trunc`` constructor is easy, because we are defining a
function into a type we know is a set.)

```
enqᶠ : A → FastQueue A → FastQueue A
enqᶠ a FQ⟨ xs , ys ⟩ = FQ⟨ a :: xs , ys ⟩
enqᶠ a (tilt xs ys z i) = tilt (a :: xs) ys z i
enqᶠ a (trunc q q' α β i j) =
  trunc _ _ (λ i → enqᶠ a (α i)) (λ i → enqᶠ a (β i)) i j
```

Dequeueing is a little more difficult, and we'll need some basic facts
about lists. Let's do them them all now to get them out of the way.

```
++-unit-l : (xs : List A) → [] ++ xs ≡ xs
++-unit-l xs = refl

++-unit-r : (xs : List A) → xs ++ [] ≡ xs
++-unit-r [] = refl
++-unit-r (x :: xs) = ap (_::_ x) (++-unit-r xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = ap (_::_ x) (++-assoc xs ys zs)

reverse-++ : (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys = sym (++-unit-r (reverse ys))
reverse-++ (x :: xs) ys =
  reverse ((x :: xs) ++ ys)
    ≡⟨ ap (λ zs → zs ++ [ x ]) (reverse-++ xs ys) ⟩
  (reverse ys ++ reverse xs) ++ [ x ]
    ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
  reverse ys ++ reverse (x :: xs) 
    ∎

reverse-snoc : (xs : List A) (y : A) → reverse (xs ++ [ y ]) ≡ y :: reverse xs
reverse-snoc [] y = refl
reverse-snoc (x :: xs) y = ap (_++ [ x ]) (reverse-snoc xs y)

reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] = refl
reverse-reverse (x :: xs) = 
  reverse (reverse (x :: xs)) ≡⟨ reverse-snoc (reverse xs) x ⟩
  x :: reverse (reverse xs)   ≡⟨ ap (x ::_) (reverse-reverse xs) ⟩
  x :: xs ∎

isProp-≡List : isSet A → (xs ys : List A) → isProp (xs ≡List ys)
isProp-≡List sA [] [] = isProp-⊤
isProp-≡List sA [] (y :: ys) = isProp-∅
isProp-≡List sA (x :: xs) [] = isProp-∅
isProp-≡List sA (x :: xs) (y :: ys) = isProp-× (sA x y) (isProp-≡List sA xs ys)

isSet-List : isSet A → isSet (List A)
isSet-List sA xs ys = isProp-equiv (≡≃≡List xs ys) (isProp-≡List sA xs ys)
```

The first step is to generalise ``tilt`` to move entire sub-lists from
one side of ``FQ⟨_,_⟩`` to the other.

```
multitilt : (xs ys zs : List A) → FQ⟨ xs ++ reverse zs , ys ⟩ ≡ FQ⟨ xs , ys ++ zs ⟩
-- Exercise:
multitilt xs ys [] = {!!}
multitilt xs ys (z :: zs) =
     FQ⟨ xs ++ reverse (z :: zs) , ys ⟩     ≡⟨ {!!} ⟩
     FQ⟨ (xs ++ reverse zs) ++ [ z ] , ys ⟩ ≡⟨ {!!} ⟩
     FQ⟨ xs ++ reverse zs , ys ++ [ z ] ⟩   ≡⟨ {!!} ⟩
     FQ⟨ xs , (ys ++ [ z ]) ++ zs ⟩         ≡⟨ {!!} ⟩
     FQ⟨ xs , ys ++ z :: zs ⟩               ∎
```

Then dequeueing works similarly to how it did for the pair of lists.
Again, the only tricky part is showing that dequeueing respects the
tilt relation.

```
deqʳ-flush : List A → Maybe (FastQueue A × A)
deqʳ-flush [] = inl tt
deqʳ-flush (x :: xs) = inr (FQ⟨ [] , xs ⟩ , x)

deqᶠ : isSet A → FastQueue A → Maybe (FastQueue A × A)
-- Exercise:
deqᶠ sA FQ⟨ xs , y :: ys ⟩ = {!!}
deqᶠ sA FQ⟨ xs , [] ⟩ = {!!}
deqᶠ sA (tilt xs (y :: ys) z i) = {!!}
deqᶠ sA (tilt xs [] z i) = path i
     where
     path = deqʳ-flush (reverse (xs ++ [ z ]))              ≡⟨ {!!} ⟩
            inr (FQ⟨ [] , [] ++ reverse xs ⟩ , z)           ≡⟨ {!!} ⟩
            inr (FQ⟨ [] ++ reverse (reverse xs) , [] ⟩ , z) ≡⟨ {!!} ⟩
            inr (FQ⟨ xs , [] ⟩ , z)                         ∎

deqᶠ sA (trunc q q' α β i j) = isSet-⊎ isSet-⊤ (isSet-× trunc sA) (deqᶠ sA q) (deqᶠ sA q') (λ k → deqᶠ sA (α k)) (λ k → deqᶠ sA (β k)) i j
```

And we have our model!

```
FastQueue-model : (A : Type) → isSet A → Type-with ℓ-zero (Queue-Str A)
FastQueue-model A sA .type = FastQueue A 
FastQueue-model A sA .str = empᶠ , enqᶠ , deqᶠ sA
```

It's easy to define functions converting between slow queues and fast
queues. From slow to fast, we just use the provided list as the back
list of the pair.

```
SlowQueue→FastQueue : SlowQueue A → FastQueue A
SlowQueue→FastQueue xs = FQ⟨ xs , [] ⟩
```

And the other way, we use the same definition as in ``Pair→Queue``,
but now have to show that the function respects the ``tilt`` relation.

```
FastQueue→SlowQueue : isSet A → FastQueue A → SlowQueue A
FastQueue→SlowQueue sA FQ⟨ xs , ys ⟩ = xs ++ reverse ys
FastQueue→SlowQueue sA (tilt xs ys z i) = path i
  where
    path =
      (xs ++ [ z ]) ++ reverse ys   ≡⟨ ++-assoc xs [ z ] (reverse ys) ⟩
      xs ++ z :: reverse ys         ≡⟨ ap (_++_ xs) (sym (reverse-++ ys [ z ])) ⟩
      xs ++ reverse (ys ++ z :: []) ∎
FastQueue→SlowQueue sA (trunc q q' α β i j) 
  = isSet-List sA (FastQueue→SlowQueue sA q) 
                  (FastQueue→SlowQueue sA q') 
                  (λ k → FastQueue→SlowQueue sA (α k)) 
                  (λ k → FastQueue→SlowQueue sA (β k)) i j
```

To complete the equivalence, only the ``FQ⟨_,_⟩`` case is interesting.
The ``tilt`` and ``trunc`` constructors are fiddly but not very
interesting: we just use the fact that we are defining a function into
paths in a set, i.e., a proposition.

```
SlowQueue≃FastQueue : isSet A → SlowQueue A ≃ FastQueue A
SlowQueue≃FastQueue {A = A} sA = inv→equiv SlowQueue→FastQueue (FastQueue→SlowQueue sA) to-fro fro-to 
  where
    -- Exercise:
    fro-to = {!!}

    to-fro : isSection SlowQueue→FastQueue (FastQueue→SlowQueue sA)
    -- Exercise:
    to-fro FQ⟨ xs , ys ⟩ = {!!}

    to-fro (tilt xs ys z i) j =
      isSet→Square trunc
      (λ i → SlowQueue→FastQueue (FastQueue→SlowQueue sA (tilt xs ys z i)))
      (tilt xs ys z)
      (multitilt (xs ++ [ z ]) [] ys)
      (multitilt xs [] (ys ++ [ z ]))
      i j
    to-fro (trunc q q' α β i j) =
      toPathP
      {A = λ i → PathP (λ j → SlowQueue→FastQueue (FastQueue→SlowQueue sA (trunc q q' α β i j)) ≡ trunc q q' α β i j) (to-fro q) (to-fro q')}
      {a₀ = λ k → to-fro (α k)}
      {a₁ = λ k → to-fro (β k)}
      (isProp-equiv (PathP≃Path _) (isProp→isSet (trunc (SlowQueue→FastQueue (FastQueue→SlowQueue sA q')) q') _ _) _ _)
      i j
```

Now if you have any sense, you are dreading the prospect of coming up
with the notion of structured equivalence for ``Queue-Str`` and
proving that it is univalent. Luckily, there is a better way.


## Structure, Compositionally

Here's the idea. We define a collection of *combinators* for building
univalent structures, so that the notion of structured equivalence
(and the proof it is univalent) is built up gradually. All three
things are packaged toether as follows:

```
record UnivalentNotion (ℓ ℓ' ℓ'' : Level) : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
  constructor UnivalentNotion-data
  field
    str-for : StrNotion ℓ ℓ'
    is-str-preserving : StrEquivNotion str-for ℓ''
    is-univalent : StrEquivNotion-univalent str-for is-str-preserving

open UnivalentNotion
```

Here's one of the base cases: the structure of having a point. This
will be used, for example, to say that the structure of monoid chooses
a distinguished point: the unit element.

```
Pointed-UStr : UnivalentNotion ℓ ℓ ℓ
Pointed-UStr .str-for X = X
Pointed-UStr .is-str-preserving A B f = f .map (str A) ≡ str B
Pointed-UStr .is-univalent f = Path≃ua-PathP f
```

So, the structure of a point on a type `X` is an element of `X`. An
equivalence `A ≃ B` preserves this structure when the underlying map
sends the chosen element `a : A` to the chosen element `b : B`. And
it's univalent, because a path of this kind is equivalent to a
path-over `PathP (λ i → ua f i) a b` between those elements.

The other base case is the structure of the choice of a constant from
some type `A`. A model of this structure will always be an element of
the type `A` and not depend on the actual type underlying the model.

```
Constant-UStr : (A : Type ℓ') → UnivalentNotion ℓ ℓ' ℓ'
Constant-UStr A .str-for X = A
Constant-UStr A .is-str-preserving X₁ X₂ _ = X₁ .str ≡ X₂ .str
Constant-UStr A .is-univalent e = idEquiv _
```

This time, an equivalence is structure preserving when the same
constant is chosen for both models, in fact, the actual equivalence
does not get used at all. If two models choose different constants,
there is no way to consider those models equivalent.

Now, the actual combinators that let us build new structures from old.

mvrnote:

```
ProductStr-fst : {S₁ : StrNotion ℓ ℓ₁} → {S₂ : StrNotion ℓ ℓ₂} → Type-with ℓ (λ X → S₁ X × S₂ X) → Type-with ℓ S₁
ProductStr-fst X .type = X .type
ProductStr-fst X .str = X .str .fst

ProductStr-snd : {S₁ : StrNotion ℓ ℓ₁} → {S₂ : StrNotion ℓ ℓ₂} → Type-with ℓ (λ X → S₁ X × S₂ X) → Type-with ℓ S₂
ProductStr-snd X .type = X .type
ProductStr-snd X .str = X .str .snd
```

```
Product-UStr : (S₁ : UnivalentNotion ℓ ℓ₁ ℓ₁') → (S₂ : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁' ℓ₂')
Product-UStr S₁ S₂ .str-for X = S₁ .str-for X × S₂ .str-for X
Product-UStr S₁ S₂ .is-str-preserving X₁ X₂ f 
  = (S₁ .is-str-preserving (ProductStr-fst X₁) (ProductStr-fst X₂) f) 
  × (S₂ .is-str-preserving (ProductStr-snd X₁) (ProductStr-snd X₂) f) 
Product-UStr S₁ S₂ .is-univalent e = ΣPath≃PathΣ ∘e (×-map-≃ (S₁ .is-univalent e) (S₂ .is-univalent e))
```


```
Function-app : {S₁ : StrNotion ℓ ℓ₁} → {S₂ : StrNotion ℓ ℓ₂} → (X : Type-with ℓ (λ X → S₁ X → S₂ X)) → S₁ (X .type) → Type-with ℓ S₂
Function-app X s₁ .type = X .type
Function-app X s₁ .str = X .str s₁

Function-UStr : (S : UnivalentNotion ℓ ℓ₁ ℓ₁') → (T : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max (ℓ-max ℓ₁ ℓ₁') ℓ₂')
Function-UStr S T .str-for X = S .str-for X → T .str-for X
Function-UStr S T .is-str-preserving X₁ X₂ e = 
  (s₁ : S .str-for (X₁ .type)) (s₂ : S .str-for (X₂ .type)) 
  → S .is-str-preserving (Type-with-data (X₁ .type) s₁) (Type-with-data (X₂ .type) s₂) e 
  → T .is-str-preserving (Function-app X₁ s₁) (Function-app X₂ s₂) e
Function-UStr S T .is-univalent e = funextP-ump-≃ ∘e Π-map-cod≃ (λ s → Π-map-cod≃ (λ t → →-map-≃ (invEquiv (S .is-univalent e)) (T .is-univalent e)))

-- mvrnote: rename
ProductStr-fst' : {S₁ : StrNotion ℓ ℓ₁} → {S₂ : (X : Type ℓ) → S₁ X → Type ℓ₂} → Type-with ℓ (λ X → Σ[ s₁ ∈ S₁ X ] S₂ X s₁) → Type-with ℓ S₁
ProductStr-fst' X .type = X .type
ProductStr-fst' X .str = X .str .fst

Axioms-Str : {ℓa : Level} → (S : UnivalentNotion ℓ ℓ' ℓ'') → (axioms : (X : Type ℓ) → S .str-for X → Type ℓa) → (axioms-are-Props : (X : Type ℓ) (s : S .str-for X) → isProp (axioms X s))→ UnivalentNotion ℓ (ℓ-max ℓ' ℓa) ℓ''
Axioms-Str S ax isP .str-for X = Σ[ s ∈ S .str-for X ] (ax X s)
Axioms-Str S ax isP .is-str-preserving X₁ X₂ e = S .is-str-preserving (ProductStr-fst' X₁) (ProductStr-fst' X₂) e
Axioms-Str S ax isP .is-univalent {X₁} {X₂} e =
  S .is-str-preserving (ProductStr-fst' X₁) (ProductStr-fst' X₂) e
    ≃⟨ S .is-univalent e ⟩
  PathP (λ i → S .str-for (ua e i)) (X₁ .str .fst) (X₂ .str .fst)
    ≃⟨ invEquiv (Σ-fst-≃ λ _ → isContr-retract (equiv→retract (PathP≃Path _)) (isProp→isContr≡ (isP _ _) _ _)) ⟩
  Σ[ p ∈ PathP (λ i → S .str-for (ua e i)) (X₁ .str .fst) (X₂ .str .fst) ] PathP (λ i → ax (ua e i) (p i)) (X₁ .str .snd) (X₂ .str .snd)
    ≃⟨ ΣPath≃PathΣ ⟩
  PathP (λ i → Axioms-Str S ax isP .str-for (ua e i)) (X₁ .str .fst , X₁ .str .snd) (X₂ .str .fst , X₂ .str .snd)
    ∎e
```

mvrnote: Re-do magma

Let's reconstruct the Magma example using these new combinators.

```
Magma-Strᵥ₂ : UnivalentNotion ℓ ℓ ℓ
Magma-Strᵥ₂ = Function-UStr Pointed-UStr (Function-UStr Pointed-UStr Pointed-UStr)

Magmaᵥ₂ : (ℓ : Level) → Type (ℓ-suc ℓ)
Magmaᵥ₂ ℓ = Type-with ℓ (Magma-Strᵥ₂ .str-for)
```

That was certainly much less work, but did we get the right thing out?
Not quite. The structure itself is correct:

```
_ = λ {ℓ : Level} 
  → test-identical
    (Magma-Str {ℓ})
    (Magma-Strᵥ₂ {ℓ} .str-for)
```

But the notion of homomorphism is not, instead of reconstructing
``isMagmaHom``, instead we get the following equivalent but more
annoying type.

```
isMagmaHomᵥ₂ : (A B : Magmaᵥ₂ ℓ) → (A .type → B .type) → Type ℓ
isMagmaHomᵥ₂ A B f
  = (a₁ : A .type) → (b₁ : B .type) → f a₁ ≡ b₁
  → (a₂ : A .type) → (b₂ : B .type) → f a₂ ≡ b₂
  → f (a₁ ·A a₂) ≡ b₁ ·B b₂
  where _·A_ = A .str
        _·B_ = B .str
  
_ = λ {ℓ : Level} (A B : Type-with ℓ (Magma-Strᵥ₂ .str-for)) (e : A .type ≃ B .type)
  → test-identical 
    (Magma-Strᵥ₂ .is-str-preserving A B e) 
    (isMagmaHomᵥ₂ A B (e .map))
```


## Transport Structures

Let's spend some time trying to work around this.

```
record TransportNotion (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor UnivalentNotion-data
  field
    str-for : StrNotion ℓ ℓ'
    equivAction : {X Y : Type ℓ} → X ≃ Y → str-for X ≃ str-for Y
    transportStr : {X Y : Type ℓ} (e : X ≃ Y) (s : str-for X) → equivAction e .map s ≡ subst str-for (ua e) s
open TransportNotion

TransportNotion→UnivalentNotion : TransportNotion ℓ ℓ' → UnivalentNotion ℓ ℓ' ℓ'
TransportNotion→UnivalentNotion T .str-for = T .str-for
TransportNotion→UnivalentNotion T .is-str-preserving X Y e = T .equivAction e .map (X .str) ≡ (Y .str)
TransportNotion→UnivalentNotion T .is-univalent {X} {Y} e =
  T .equivAction e .map (X .str) ≡ (Y .str)
    ≃⟨ path→equiv (ap (_≡ (Y .str)) (T .transportStr e (X .str))) ⟩
  subst (T .str-for) (ua e) (X .str) ≡ (Y .str)
    ≃⟨ invEquiv (PathP≃Path _) ⟩
  PathP (λ i → T .str-for (ua e i)) (X .str) (Y .str)
  ∎e

Constant-TrStr : (A : Type ℓ') → TransportNotion ℓ ℓ'
Constant-TrStr A .str-for _ = A
Constant-TrStr A .equivAction _ = idEquiv _
Constant-TrStr A .transportStr e _ = sym (transport-refl _)

Pointed-TrStr : TransportNotion ℓ ℓ
Pointed-TrStr .str-for X = X
Pointed-TrStr .equivAction e = e
Pointed-TrStr .transportStr e _ = sym (transport-refl _)

Product-TrStr : (S₁ : TransportNotion ℓ ℓ₁) → (S₂ : TransportNotion ℓ ℓ₂) → TransportNotion ℓ (ℓ-max ℓ₁ ℓ₂)
Product-TrStr S₁ S₂ .str-for X = S₁ .str-for X × S₂ .str-for X
Product-TrStr S₁ S₂ .equivAction e = ×-map-≃ (S₁ .equivAction e) (S₂ .equivAction e)
Product-TrStr S₁ S₂ .transportStr e (s₁ , s₂) i = (S₁ .transportStr e s₁ i , S₂ .transportStr e s₂ i)

Function-UStr+ : (S : TransportNotion ℓ ℓ₁) → (T : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ ℓ₂')
Function-UStr+ S T .str-for X = S .str-for X → T .str-for X
Function-UStr+ S T .is-str-preserving X Y e =
   (s : S .str-for (X .type)) → T .is-str-preserving (Type-with-data (X .type) (X .str s)) (Type-with-data (Y .type) (Y .str (S .equivAction e .map s))) e
Function-UStr+ S T .is-univalent {X} {Y} e =
  ((x : S .str-for (X .type)) → T .is-str-preserving (Type-with-data (X .type) (X .str x)) (Type-with-data (Y .type) (Y .str (S .equivAction e .map x))) e)
    ≃⟨ Π-map-cod≃ (λ x → T .is-univalent e) ⟩
  ((s : S .str-for (X .type)) → PathP (λ i → T .str-for (ua e i)) (X .str s) (Y .str (S .equivAction e .map s)))
    ≃⟨ path→equiv (λ i → ((s : S .str-for (X .type)) → PathP (λ i → T .str-for (ua e i)) (X .str s) (Y .str (S .transportStr e s i)))) ⟩
  ((s : S .str-for (X .type)) → PathP (λ i → T .str-for (ua e i)) (X .str s) (Y .str (subst (S .str-for) (ua e) s)))
    ≃⟨ Π-map-cod≃ (λ _ → path→equiv (PathP≡Path' _ _ _) ) ⟩
  ((x : S .str-for (X .type)) → X .str x ≡ transport (λ i → T .str-for (ua e (~ i))) (Y .str (subst (S .str-for) (ua e) x)))
    ≃⟨ funext-≃ ⟩
  X .str ≡ (λ z → transport (λ i → T .str-for (ua e (~ i))) (Y .str (subst (S .str-for) (ua e) z)))
    ≃⟨ invEquiv (path→equiv (PathP≡Path' _ (X .str) (Y .str)))  ⟩
  PathP (λ i → S .str-for (ua e i) → T .str-for (ua e i)) (X .str) (Y .str)
    ∎e

Magma-Strᵥ₃ : UnivalentNotion ℓ ℓ ℓ
Magma-Strᵥ₃ = Function-UStr+ Pointed-TrStr (Function-UStr+ Pointed-TrStr Pointed-UStr)

_ = λ (ℓ : Level) (A B : Type-with ℓ Magma-Str) (e : A .type ≃ B .type)
  → test-identical 
    (Magma-Strᵥ₃ .is-str-preserving A B e) 
    (isMagmaHom A B (e .map))
```


## Queues again


```
Maybe-Str : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
Maybe-Str S X = Maybe (S X)

Maybe-TrStr : TransportNotion ℓ ℓ' → TransportNotion ℓ ℓ'
Maybe-TrStr S .str-for X = Maybe (S .str-for X)
Maybe-TrStr S .equivAction e = ⊎-map-≃ (idEquiv ⊤) (S .equivAction e)
Maybe-TrStr S .transportStr e (inl x) = refl
Maybe-TrStr S .transportStr e (inr x) = ap inr (S .transportStr e x)
```

```
Queue-UStr : (A : Type) → UnivalentNotion ℓ ℓ ℓ
Queue-UStr A = Product-UStr
  Pointed-UStr
  (Product-UStr (Function-UStr+ (Constant-TrStr A) (Function-UStr+ Pointed-TrStr Pointed-UStr))
                          (Function-UStr+ Pointed-TrStr (TransportNotion→UnivalentNotion (Maybe-TrStr (Product-TrStr Pointed-TrStr (Constant-TrStr A))))))
```


```
deq-func-∘ : {B C D : Type ℓ}
 (g : C → D) (f : B → C)
 → ∀ r → deq-func {A = A} g (deq-func f r) ≡ deq-func (g ∘ f) r
deq-func-∘ g f (inl _) = refl
deq-func-∘ g f (inr (b , a)) = refl

SlowQueue→FastQueue-emp : SlowQueue→FastQueue {A = A} empˢ ≡ empᶠ
SlowQueue→FastQueue-emp = refl

SlowQueue→FastQueue-enq : (x : A) → (xs : SlowQueue A) → SlowQueue→FastQueue (enqˢ x xs) ≡ enqᶠ x (SlowQueue→FastQueue xs)
SlowQueue→FastQueue-enq x xs = refl

SlowQueue→FastQueue-deq : (sA : isSet A) → (xs : SlowQueue A) → deq-func SlowQueue→FastQueue (deqˢ xs) ≡ deqᶠ sA (SlowQueue→FastQueue xs)
SlowQueue→FastQueue-deq sA [] = refl
SlowQueue→FastQueue-deq sA (x :: []) = refl
SlowQueue→FastQueue-deq sA (x :: x' :: xs) = 
  deq-func SlowQueue→FastQueue (deqˢ (x :: x' :: xs))              ≡⟨ deq-func-∘ SlowQueue→FastQueue (enqˢ x) (deqˢ (x' :: xs)) ⟩
  deq-func (SlowQueue→FastQueue ∘ enqˢ x) (deqˢ (x' :: xs))        ≡⟨ sym (deq-func-∘ (enqᶠ x) SlowQueue→FastQueue (deqˢ (x' :: xs))) ⟩
  deq-func (enqᶠ x) (deq-func SlowQueue→FastQueue (deqˢ (x' :: xs))) ≡⟨ ap (deq-func (enqᶠ x)) (SlowQueue→FastQueue-deq sA (x' :: xs)) ⟩
  deq-func (enqᶠ x) (deqᶠ sA (SlowQueue→FastQueue (x' :: xs)))     ≡⟨ lemma x x' (reverse xs) ⟩
  deqᶠ sA (SlowQueue→FastQueue (x :: x' :: xs))                  ∎
  where
  lemma : ∀ x x' ys → deq-func (enqᶠ x) (deqʳ-flush (ys ++ [ x' ])) ≡ deqʳ-flush ((ys ++ [ x' ]) ++ [ x ])
  lemma x x' [] i        = inr (tilt [] [] x i , x')
  lemma x x' (y :: ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)

SlowQueue→FastQueue-hom : (sA : isSet A) → Queue-UStr A .is-str-preserving (SlowQueue-model A) (FastQueue-model A sA) (SlowQueue≃FastQueue sA)
SlowQueue→FastQueue-hom sA = SlowQueue→FastQueue-emp , SlowQueue→FastQueue-enq , SlowQueue→FastQueue-deq sA

SlowQueue≃[Queue]FastQueue : (sA : isSet A) → SlowQueue-model A ≃[ Queue-UStr A .is-str-preserving ] (FastQueue-model A sA)
SlowQueue≃[Queue]FastQueue sA .eq = SlowQueue≃FastQueue sA
SlowQueue≃[Queue]FastQueue sA .proof = SlowQueue→FastQueue-hom sA

SlowQueue≡FastQueue : (sA : isSet A) → (SlowQueue-model A) ≡ (FastQueue-model A sA)
SlowQueue≡FastQueue {A = A} sA = sip (Queue-UStr A .is-univalent) (SlowQueue-model A) (FastQueue-model A sA) (SlowQueue≃[Queue]FastQueue sA)
```

Let's get some payoff, and transfer the proofs of all the axioms.

```
FastQueue-Axioms : (sA : isSet A) → Queue-Axioms (FastQueue-model A sA)
FastQueue-Axioms sA = subst Queue-Axioms (SlowQueue≡FastQueue sA) SlowQueue-Axioms
```

It's as simple as that.

## mvrnote: Project ideas?



## References and Further Reading

mvrnote:
https://1lab.dev/1Lab.Univalence.SIP.html
Internalizing Representation Independence with Univalence https://arxiv.org/abs/2009.05547
https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda
https://staff.math.su.se/anders.mortberg/slides/PalmgrenMemorial2020.pdf
https://dl.acm.org/doi/abs/10.1145/3373718.3394755

Okasaki 1999 for the batched queue



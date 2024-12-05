<!--
```
module 3--Structures.3-1--Structure-Identity-Principle where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets
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

mvrnote: rename Semigroup to ∞Semigroup and reserve the former for sets?
mvrnote: call a homomorphism φ everywhere, standardise e vs ε
mvrnote: inferring universe levels is still dodgy, causing unpleasantly slow type checking somewhere
mvrnote: credit sources up top
mvrnote: simplify universe levels, just do everything at one level?

In Lecture 2-X we saw how univalence can be used to show that paths
between types the same as equivalences between those types. But what
if our types have extra structure, like algebraic operations or
axioms? In this Lecture, we extend univalence to the Structure
Identity Principle, which shows that paths between structured types
are equivalent to structure-preserving equivalences between those
types.

What exactly is "structure"? A structure on a type is some collection
of functions involving that type and axioms that those functions have
to satisfy. To describe that collection, we will simply use a function
from types to types: the input type is the "carrier" type of the
structure, and the output type is the extra data that that is
necessary to equip the carrier with the specified structure.

```
StrNotion : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
StrNotion ℓ ℓ' = Type ℓ → Type ℓ'
``` 

Almost the simplest example of a structure we can give is that of a
"magma", which is simply a binary operation that need not satisfy any
additional properties.

```
Magma-Str : StrNotion ℓ ℓ
Magma-Str X = X → X → X
```

::: Aside:
This might more properly be called an "∞-Magma", because we are not
going to assume that the carrier type is a set necessearily.
:::


So, to say that a type `X` is a magma, that is, `X` has a magma
structure, we have to equip it with an element of `MagmaStr X`. The
type of all magmas with a fixed universe level is then:

```
Magma : (ℓ : Level) → Type (ℓ-suc ℓ)
Magma ℓ = Σ[ X ∈ Type ℓ ] Magma-Str X
```

So for example, the natural numbers form a magma.

```
ℕ-Magma : Magma ℓ-zero
ℕ-Magma = ℕ , _+ℕ_
```

Show that the booleans form a semigroup under ``and``.

```
Bool-and-Magma : Magma ℓ-zero
-- Exercise:
Bool-and-Magma = {!!}
```

We usually want to know that our operations obey some axioms. For
example, a "semigroup" is a type with an *associative* binary
operation.

```
Semigroup-Str : StrNotion ℓ ℓ
Semigroup-Str X = Σ[ _·_ ∈ (X → X → X) ] ((x y z : X) → x · (y · z) ≡ (x · y) · z)

Semigroup : (ℓ : Level) → Type (ℓ-suc ℓ)
Semigroup ℓ = Σ[ X ∈ Type ℓ ] Semigroup-Str X
```

We have already seen that addition of natural numbers is associative,
so this shows that ``ℕ`` is also a semigroup:

```
ℕ-Semigroup : Semigroup ℓ-zero
ℕ-Semigroup = ℕ , _+ℕ_ , +ℕ-assoc
```

A single type can support many non-equal versions of the same
structure. We could have done just the same with ``Bool`` and ``and``.

mvrnote: remove?
We typically want to assume that the underlying type of a structured
type is a set rather than an arbitrary type. This can be achieved by
adding yet more to the structure on `X`: a proof that `isSet X`.

```
SemigroupSet-Str : StrNotion ℓ ℓ
SemigroupSet-Str X = Σ[ _·_ ∈ (X → X → X) ] ((x y z : X) → x · (y · z) ≡ (x · y) · z) × isSet X

SemigroupSet : (ℓ : Level) → Type (ℓ-suc ℓ)
SemigroupSet ℓ = Σ[ X ∈ Type ℓ ] SemigroupSet-Str X

ℕ-SemigroupSet : SemigroupSet ℓ-zero
ℕ-SemigroupSet = ℕ , _+ℕ_ , +ℕ-assoc , isSetℕ
```

These situations are what we are going to generalise. Given a notion
of structure `S : Type ℓ → Type ℓ'`, an `S`-structured type is an
element of

```
Type-with : (ℓ : Level) → (S : StrNotion ℓ ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
Type-with ℓ S = Σ[ X ∈ Type ℓ ] S X
```

The helper functions ``typ`` and ``str`` extract the underlying type
and associated structure from such a ``Type-with``.

```
typ : {S : StrNotion ℓ ℓ'} → Type-with ℓ S → Type ℓ
typ = fst

str : {S : StrNotion ℓ ℓ'} →  (A : Type-with ℓ S) → S (typ A)
str = snd
```


## Structured Equivalences

Not all functions between structured types respect the structure that
the types come with. For magmas, semigroups, monoids, groups and so
on, we are only interested in *homomorphisms*: those functions that
respect the underlying binary operation. This is easy to describe as a
type.

```
isMagmaHom : (A B : Magma ℓ) → (typ A → typ B) → Type ℓ
isMagmaHom (A , _·A_) (B , _·B_) f
  = (a₁ a₂ : A) → f (a₁ ·A a₂) ≡ (f a₁) ·B (f a₂)
```

We have a function `isZero : ℕ → Bool`, and in fact this function is a
homomorphism as long as we choose are using the right structure on
both sides.

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
A ≃[Magma] B = Σ[ e ∈ typ A ≃ typ B ] (isMagmaHom A B (e .map))
```

Again, this situation is what we want to generalise to arbitrary
notions of structure. Let us say define a "notion of structured
equivalence" to be the extra information that an equivalence between
structured types needs in order to respect that structure. In the
magma case, this is the ``isMagmaHom`` type. A structured equivalence
is then an equivalence paired together with an instance of this
information.

```
StrEquivNotion : (S : StrNotion ℓ ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrEquivNotion S ℓ' = (A B : Type-with _ S) → typ A ≃ typ B → Type ℓ'

StrEquiv : {S : StrNotion ℓ ℓ'} → (ι : StrEquivNotion S ℓ'') (A : Type-with ℓ S)  (B : Type-with ℓ S) → Type (ℓ-max ℓ ℓ'')
StrEquiv ι A B = Σ[ e ∈ typ A ≃ typ B ] (ι A B e)
```

To make this easier to read, we'll add some nicer syntax for these
structured equivalences.

```
_≃[_]_ : {S : StrNotion ℓ ℓ'} → (A : Type-with ℓ S) (ι : StrEquivNotion S ℓ'') (B : Type-with ℓ S) → Type (ℓ-max ℓ ℓ'')
A ≃[ ι ] B = StrEquiv ι A B

Magma-EquivNotion : StrEquivNotion (Magma-Str {ℓ}) ℓ
Magma-EquivNotion A B e = isMagmaHom A B (e .map)

_ : (A B : Magma ℓ) → A ≃[ Magma-EquivNotion ] B ≡ A ≃[Magma] B
_ = λ A B → refl
```

How do we know when we've chosen the right notion of structure for our
equivalences? Well, the crucial feature of equivalences is univalence;
that equivalences between types can be turned into paths in the
universe. We will use this as a guide for our structured equivalences:
whatever the notion of structured equivalence is, it should be
possible to turn it into a path between the structures, over the path
between types given by univalence. That is, we will seek to inhabit
the following type.

```
-- mvrnote: rename
UnivalentStr : (S : StrNotion ℓ ℓ') (ι : StrEquivNotion S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
UnivalentStr S ι =
  {A B : Type-with _ S} (e : typ A ≃ typ B)
  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)
```

```
funexthalf-≃' : {A : Type ℓ} {B : Type ℓ'}
  {f : A → B} {g : A → B}
  → ((x₀ : A) → (x₁ : A) → (x₀ ≡ x₁) → (f x₀ ≡ g x₁))
  ≃ (f ≡ g)
funexthalf-≃' {A = A} {B = B} {f = f} {g = g} =
  ((x₀ x₁ : A) → x₀ ≡ x₁ → (f x₀ ≡ g x₁))
  ≃⟨ Π-map-cod≃ (λ x₀ → J-ump-≃ (λ y _ → (f x₀ ≡ g y))) ⟩
  ((x : A) → (f x ≡ g x))
  ≃⟨ funextP-≃ ⟩
  (f ≡ g) ∎e

funextP-ump-≃' : {A : I → Type ℓ} {B : I → Type ℓ'}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x₀ : A i0) (x₁ : A i1) → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g
funextP-ump-≃' {A = A} {B = B} {f = f} {g = g} =
  J
  (λ A1 A → {f : _} {g : _} → ((x₀ : A i0) (x₁ : A i1) → PathP (λ i → A i) x₀ x₁ → PathP B (f x₀) (g x₁)) ≃ PathP (λ i → A i → B i) f g)
  (J (λ B1 B → {f : _} {g : _} → ((x₀ : A i0) (x₁ : A i0) → Path (A i0) x₀ x₁ → PathP (λ i → B i) (f x₀) (g x₁)) ≃ PathP (λ i → A i0 → B i) f g) funexthalf-≃' (λ i → B i))
  (λ i → A i)

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
```

For our ``Magma-EquivNotion``, this is:

```
≃[Magma]-univalent : {A B : Magma ℓ} (e : typ A ≃ typ B)  →
  isMagmaHom A B (e .map) ≃ PathP (λ i → Magma-Str (ua e i)) (str A) (str B)
≃[Magma]-univalent {A = A} {B = B} e = step1 ∘e step2 ∘e invEquiv step3
```

This can indeed be done, by gluing together lots of little
equivalences that we've already shown in previous lectures. It's a bit
boring and fiddly, so we'll just do it for you:

```
  where
  step1 : {A : I → Type ℓ} {B : I → Type ℓ'} {C : I → Type ℓ''}
    {f : A i0 → B i0 → C i0} {g : A i1 → B i1 → C i1}
    → ((x₀ : A i0) (x₁ : A i1) → PathP A x₀ x₁ → (x₀' : B i0) (x₁' : B i1) → PathP B x₀' x₁' → PathP C (f x₀ x₀') (g x₁ x₁'))
    ≃ PathP (λ i → A i → B i → C i) f g
  step1 = funextP-ump-≃ ∘e Π-map-cod≃ (λ _ → Π-map-cod≃ (λ _ → Π-map-cod≃ (λ _ → funextP-ump-≃)))

  step2 : ((x₀ : typ A) → (x₁ : typ B)
           → e .map x₀ ≡ x₁
           → (x₀' : typ A) → (x₁' : typ B)
           → e .map x₀' ≡ x₁'
           → e .map (str A x₀ x₀') ≡ (str B x₁ x₁'))
    ≃     ((x₀ : typ A) → (x₁ : typ B)
           → PathP (λ z → ua e z) x₀ x₁
           → (x₀' : typ A) → (x₁' : typ B)
           → PathP (λ z → ua e z) x₀' x₁'
           → PathP (λ z → ua e z) (str A x₀ x₀') (str B x₁ x₁'))
  step2 = Π-map-cod≃ λ x₀ → Π-map-cod≃ λ x₁ → →-map-≃ (invEquiv (Path≃ua-PathP e)) (Π-map-cod≃ λ x₀' → Π-map-cod≃ λ x₁' → →-map-≃ (invEquiv (Path≃ua-PathP e)) (Path≃ua-PathP e))

  step3 : ((x₀ : typ A) (x₁ : typ B)
           → e .map x₀ ≡ x₁
           → (x₀' : typ A) (x₁' : typ B)
           → e .map x₀' ≡ x₁'
           → e .map (str A x₀ x₀') ≡ (str B x₁ x₁'))
    ≃ isMagmaHom A B (e .map)
  step3 = Π-map-cod≃ λ x₀ → ((Π-map-cod≃ λ x₀' → J-ump-≃ _) ∘e J-ump-≃ _)
```

The upshot of knowing ``≃[Magma]-univalent`` is that we can upgrade
univalence to something that works on entire magmas, not just their
underlying types. This is what we call

```
SIP-Magma : {A B : Magma ℓ} → (A ≃[ Magma-EquivNotion ] B) ≃ (A ≡ B)
SIP-Magma = ΣPath≃PathΣ ∘e (Σ-map-≃ (invEquiv univalence) ≃[Magma]-univalent)
```

This works totally generically using the abstract setup we have been
developing so far. Try putting the pieces together!

```
module _ {S : StrNotion ℓ ℓ'} {ι : StrEquivNotion S ℓ'}
  (θ : UnivalentStr S ι) (A B : Type-with ℓ S)
  where

  SIP : (A ≃[ ι ] B) ≃ (A ≡ B)
  -- Exercise:
  SIP = {!!}

  sip : (A ≃[ ι ] B) → A ≡ B
  -- Exercise:
  sip = {!!}

  sipInv : A ≡ B → A ≃[ ι ] B
  -- Exercise:
  sipInv = {!!}
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
Bool-or-Magma = Bool , _or_

not-isMagmaHom : (a a' : Bool) → not (a or a') ≡ (not a and not a')
not-isMagmaHom true true = refl
not-isMagmaHom true false = refl
not-isMagmaHom false true = refl
not-isMagmaHom false false = refl

not-[Magma]≃ : Bool-or-Magma ≃[ Magma-EquivNotion ] Bool-and-Magma
not-[Magma]≃ = not-≃ , not-isMagmaHom

Bool-or≡Bool-and : Bool-or-Magma ≡ Bool-and-Magma
Bool-or≡Bool-and = sip ≃[Magma]-univalent Bool-or-Magma Bool-and-Magma not-[Magma]≃
```

Way back in Lecture 2-X, we showed that ``or`` is an associative
operation. We can use this path that we just proved to transfer this
proof over to ``and``.

```
or≡and : PathP (λ i → fst (Bool-or≡Bool-and i) → fst (Bool-or≡Bool-and i) → fst (Bool-or≡Bool-and i)) _or_ _and_
or≡and i = snd (Bool-or≡Bool-and i)

and-assoc : (m n o : Bool) → m and (n and o) ≡ (m and n) and o
and-assoc = transport (λ i → (m n o : fst (Bool-or≡Bool-and i)) → or≡and i m (or≡and i n o) ≡ or≡and i (or≡and i m n) o) or-assoc
```

This wasn't too impressive, because ``and-assoc`` would have been easy
enough to prove by hand. But this works for equivalences of any
complexity. For a more interesting example, let's look at a binary
representation of the natural numbers.

We can think of a binary number as being built up from left to right,
one digit at a time. Starting with the empty string ` ` corresponding
to zero, each additional digit doubles the value of all the previous
digits, and then decides whether or not to add 1. For `1101` say, we have

* ` ` corresponding to $0$
* `1` corresponding to $1 + (2 × 0) = 1$
* `11` corresponding to $1 + (2 × 1) = 3$
* `110` corresponding to $0 + (2 × 3) = 6$
* `1101` corresponding to $1 + (2 × 6) = 13$

This idea is what we will capture in a data-type, with a catch: we
don't want our binary strings to be allowed to begin with a string of
pointless `0`s. To avoid this, we will replace the "just multiply by
two" option with an "add one and multiply by two" option, so that we
no longer have many different ways to represent zero. We have
partitioned the natural numbers into three categories: zero, non-zero
even (so $n = 2×(1+k)$), or odd (so $n = 1+(2×k)$).

mvrnote: cite where this trick is from

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
ℕᵇ-Magma = ℕᵇ , _+ℕᵇ_
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
ℕᵇ≃[Magma]ℕ = ℕᵇ≃ℕ , ℕᵇ→ℕ-hom

ℕᵇ-Magma≡ℕ-Magma : ℕᵇ-Magma ≡ ℕ-Magma
ℕᵇ-Magma≡ℕ-Magma = sip ≃[Magma]-univalent ℕᵇ-Magma ℕ-Magma ℕᵇ≃[Magma]ℕ
```

Now we can transfer proofs about ``ℕ`` to proofs about ``ℕᵇ`` with
essentially no effort. Showing ``+ℕᵇ-assoc`` by hand would be a nightmare!

```
+ℕ≡+ℕᵇ : PathP (λ i → ℕᵇ≡ℕ (~ i) → ℕᵇ≡ℕ (~ i) → ℕᵇ≡ℕ (~ i)) _+ℕ_ _+ℕᵇ_
+ℕ≡+ℕᵇ i = snd (ℕᵇ-Magma≡ℕ-Magma (~ i))

+ℕᵇ-assoc : (m n o : ℕᵇ) → m +ℕᵇ (n +ℕᵇ o) ≡ (m +ℕᵇ n) +ℕᵇ o
+ℕᵇ-assoc = transport (λ i → (m n o : ℕᵇ≡ℕ (~ i)) → +ℕ≡+ℕᵇ i m (+ℕ≡+ℕᵇ i n o) ≡ +ℕ≡+ℕᵇ i (+ℕ≡+ℕᵇ i m n) o) +ℕ-assoc
```

Thank goodness!


## Queues

mvrnote: put in module

```
Maybe : Type ℓ → Type ℓ
Maybe A = ⊤ ⊎ A

Queue-Str : Type → StrNotion ℓ-zero ℓ-zero
Queue-Str A X = X × (A → X → X) × (X → Maybe (X × A))

++-unit-r : (xs : List A) → xs ++ [] ≡ xs
++-unit-r [] = refl
++-unit-r (x :: xs) = ap (_::_ x) (++-unit-r xs)

++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = ap (_::_ x) (++-assoc xs ys zs)

reverse-++ : (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys = sym (++-unit-r (reverse ys))
reverse-++ (x :: xs) ys =
  ap (λ zs → zs ++ [ x ]) (reverse-++ xs ys)
  ∙ ++-assoc (reverse ys) (reverse xs) [ x ]

reverse-snoc : (xs : List A) (y : A) → reverse (xs ++ [ y ]) ≡ y :: reverse xs
reverse-snoc [] y = refl
reverse-snoc (x :: xs) y = ap (_++ [ x ]) (reverse-snoc xs y)

reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] = refl
reverse-reverse (x :: xs) = reverse-snoc (reverse xs) x ∙ ap (_::_ x) (reverse-reverse xs)

SlowQueue : Type → Type
SlowQueue A = List A

empˢ : SlowQueue A
empˢ = []

enqˢ : A → SlowQueue A → SlowQueue A
enqˢ = _::_

deqMap : {X Y : Type ℓ} → (X → Y) → Maybe (X × A) → Maybe (Y × A)
deqMap f = ⊎-map idfun (λ (x , a) → (f x , a))

deqMap-∘ : {B C D : Type ℓ}
 (g : C → D) (f : B → C)
 → ∀ r → deqMap {A = A} g (deqMap f r) ≡ deqMap (g ∘ f) r
deqMap-∘ g f (inl _) = refl
deqMap-∘ g f (inr (b , a)) = refl

deqˢ : SlowQueue A → Maybe (SlowQueue A × A)
deqˢ [] = inl tt
deqˢ (x :: []) = inr ([] , x)
deqˢ (x :: x' :: xs) = deqMap (enqˢ x) (deqˢ (x' :: xs))

SlowQueue-model : (A : Type) → Type-with ℓ-zero (Queue-Str A)
SlowQueue-model A = (SlowQueue A , empˢ , enqˢ , deqˢ)
```

```
data FastQueue (A : Type) : Type where
  FQ⟨_,_⟩ : (xs ys : List A) → FastQueue A
  tilt : ∀ xs ys z → FQ⟨ xs ++ [ z ] , ys ⟩ ≡ FQ⟨ xs , ys ++ [ z ] ⟩
  trunc : isSet (FastQueue A)

multitilt : (xs ys zs : List A) → FQ⟨ xs ++ reverse zs , ys ⟩ ≡ FQ⟨ xs , ys ++ zs ⟩
multitilt xs ys [] = λ i → FQ⟨  (++-unit-r xs i) , (sym (++-unit-r ys) i) ⟩
multitilt xs ys (z :: zs) =
  ap (λ ws → FQ⟨ ws , ys ⟩) (sym (++-assoc xs (reverse zs) [ z ]))
  ∙ tilt (xs ++ reverse zs) ys z
  ∙ multitilt xs (ys ++ [ z ]) zs
  ∙ ap (λ ws → FQ⟨ xs , ws ⟩) (++-assoc ys [ z ] zs)

empᶠ : FastQueue A
empᶠ = FQ⟨ [] , [] ⟩

enqᶠ : A → FastQueue A → FastQueue A
enqᶠ a FQ⟨ xs , ys ⟩ = FQ⟨ a :: xs , ys ⟩
enqᶠ a (tilt xs ys z i) = tilt (a :: xs) ys z i
enqᶠ a (trunc q q' α β i j) =
  trunc _ _ (λ i → enqᶠ a (α i)) (λ i → enqᶠ a (β i)) i j

deqFlush : List A → Maybe (FastQueue A × A)
deqFlush [] = inl tt
deqFlush (x :: xs) = inr (FQ⟨ [] , xs ⟩ , x)

deqᶠ : isSet A → FastQueue A → Maybe (FastQueue A × A)
deqᶠ Aset FQ⟨ xs , [] ⟩ = deqFlush (reverse xs)
deqᶠ Aset FQ⟨ xs , y :: ys ⟩ = inr (FQ⟨ xs , ys ⟩ , y)
deqᶠ Aset (tilt xs [] z i) = path i
  where
  path : deqFlush (reverse (xs ++ [ z ])) ≡ inr (FQ⟨ xs , [] ⟩ , z)
  path =
    ap deqFlush (reverse-++ xs [ z ])
    ∙ ap (λ q → inr (q , z)) (sym (multitilt [] [] (reverse xs)))
    ∙ ap (λ ys → inr (FQ⟨ ys , [] ⟩ , z)) (reverse-reverse xs)
deqᶠ Aset (tilt xs (y :: ys) z i) = inr (tilt xs ys z i , y)
deqᶠ Aset (trunc q q' α β i j) = isSet⊎ isSet⊤ (isSet× trunc Aset) (deqᶠ Aset q) (deqᶠ Aset q') (λ k → deqᶠ Aset (α k)) (λ k → deqᶠ Aset (β k)) i j

FastQueue-model : (A : Type) → isSet A → Type-with ℓ-zero (Queue-Str A)
FastQueue-model A Aset = (FastQueue A , empᶠ , enqᶠ , deqᶠ Aset)
```

```
postulate
  -- mvrnote: either prove in Lectures 2-3 and 2-8, or quickly do it here
  isSet-List : isSet A → isSet (List A)

-- mvrnote: rename to slow→fast etc or something
quot : {A : Type} → SlowQueue A → FastQueue A
quot xs = FQ⟨ xs , [] ⟩

eval : {A : Type} → isSet A → FastQueue A → SlowQueue A
eval isSetA FQ⟨ xs , ys ⟩ = xs ++ reverse ys
eval isSetA (tilt xs ys z i) = path i -- mvrnote: cleanup into equational reasoning
  where
  path : (xs ++ [ z ]) ++ reverse ys ≡ xs ++ reverse (ys ++ [ z ])
  path =
    ++-assoc xs [ z ] (reverse ys)
    ∙ ap (_++_ xs) (sym (reverse-++ ys [ z ]))
eval isSetA (trunc q q' α β i j) = isSet-List isSetA (eval isSetA q) (eval isSetA q') (λ k → eval isSetA (α k)) (λ k → eval isSetA (β k)) i j

isOfHLevelPathP'' : {A : I → Type ℓ}
                   → isProp (A i1)
                   → (x : A i0) (y : A i1) → PathP A x y
isOfHLevelPathP'' {A = A} h x y = transport (sym (PathP≡Path _ _ _)) (h _ _)

isOfHLevelPathP' : {A : I → Type ℓ}
                   → isSet (A i1)
                   → (x : A i0) (y : A i1) → isProp (PathP A x y)
isOfHLevelPathP' {A = A} h x y =
  subst isProp (sym (PathP≡Path _ _ _)) (h _ _)

quot∘eval : {A : Type} → (isSetA : isSet A) → isRetract (eval {A = A} isSetA) quot
quot∘eval isSetA FQ⟨ xs , ys ⟩ = multitilt xs [] ys
quot∘eval isSetA (tilt xs ys z i) j = 
  isSet→SquareP (λ _ _ → trunc)
  (λ i → quot (eval isSetA (tilt xs ys z i)))
  (tilt xs ys z)
  (multitilt (xs ++ [ z ]) [] ys)
  (multitilt xs [] (ys ++ [ z ]))
  i j
quot∘eval isSetA (trunc q q' α β i j) = isOfHLevelPathP''
  {A = λ i → PathP (λ j → quot (eval isSetA (trunc q q' α β i j)) ≡ trunc q q' α β i j) (quot∘eval isSetA q) (quot∘eval isSetA q')}
  (isOfHLevelPathP' (isProp→isSet (trunc (quot (eval isSetA q')) q')) (quot∘eval isSetA q) (quot∘eval isSetA q')) (λ k → quot∘eval isSetA (α k)) (λ k → quot∘eval isSetA (β k)) i j

eval∘quot : {A : Type} → (isSetA : isSet A) → isSection (eval {A = A} isSetA) quot
eval∘quot isSetA = ++-unit-r

-- We get our desired equivalence
quotEquiv : isSet A → SlowQueue A ≃ FastQueue A
quotEquiv isSetA = inv→equiv quot (eval isSetA) (quot∘eval isSetA) (eval∘quot isSetA)
```

mvrnote:
Now if you have any sense, you are dreading the prospect of coming up with the notion
of structured equivalence for ``Queue-Str`` and proving that it is univalent.


## Univalent Notions of Structure Compositionally

mvrnote: prose

Constant structure
```
record UnivalentNotion (ℓ ℓ' ℓ'' : Level) : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
  constructor univalentNotionData
  field
    notion : StrNotion ℓ ℓ' -- "structureFor"?
    equivNotion : StrEquivNotion notion ℓ'' -- "isStructurePreserving"
    univalenceNotion : UnivalentStr notion equivNotion -- "isUnivalent"
open UnivalentNotion

ConstantUnivalentNotion : (A : Type ℓ') → UnivalentNotion ℓ ℓ' ℓ'
ConstantUnivalentNotion A .notion _ = A
ConstantUnivalentNotion A .equivNotion (_ , a) (_ , a') _ = a ≡ a'
ConstantUnivalentNotion A .univalenceNotion e = idEquiv _

PointedUnivalentNotion : UnivalentNotion ℓ ℓ ℓ
PointedUnivalentNotion .notion X = X
PointedUnivalentNotion .equivNotion A B f = f .map (str A) ≡ str B
PointedUnivalentNotion .univalenceNotion f = Path≃ua-PathP f

ProductUnivalentNotion : (S₁ : UnivalentNotion ℓ ℓ₁ ℓ₁') → (S₂ : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁' ℓ₂')
ProductUnivalentNotion S₁ S₂ .notion X = S₁ .notion X × S₂ .notion X
ProductUnivalentNotion S₁ S₂ .equivNotion (X , s₁ , s₂) (Y , t₁ , t₂) f = (S₁ .equivNotion  (X , s₁) (Y , t₁) f) × (S₂ .equivNotion (X , s₂) (Y , t₂) f)
ProductUnivalentNotion S₁ S₂ .univalenceNotion e = ΣPath≃PathΣ ∘e (×-map-≃ (S₁ .univalenceNotion e) (S₂ .univalenceNotion e))

FunctionUnivalentNotion : (S : UnivalentNotion ℓ ℓ₁ ℓ₁') → (T : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max (ℓ-max ℓ₁ ℓ₁') ℓ₂')
FunctionUnivalentNotion S T .notion X = S .notion X → T .notion X
FunctionUnivalentNotion S T .equivNotion (X , f₁) (Y , f₂) e =  (s : S .notion X) (t : S .notion Y) → S .equivNotion (X , s) (Y , t) e → T .equivNotion (X , f₁ s) (Y , f₂ t) e
FunctionUnivalentNotion S T .univalenceNotion e = funextP-ump-≃ ∘e Π-map-cod≃ (λ s → Π-map-cod≃ (λ t → →-map-≃ (invEquiv (S .univalenceNotion e)) (T .univalenceNotion e)))

AxiomsUnivalentNotion : {ℓa : Level} → (S : UnivalentNotion ℓ ℓ' ℓ'') → (axioms : (X : Type ℓ) → S .notion X → Type ℓa) → (axioms-are-Props : (X : Type ℓ) (s : S .notion X) → isProp (axioms X s))→ UnivalentNotion ℓ (ℓ-max ℓ' ℓa) ℓ''
AxiomsUnivalentNotion S ax isP .notion X = Σ[ s ∈ S .notion X ] (ax X s)
AxiomsUnivalentNotion S ax isP .equivNotion (X , (s , a)) (Y , (t , b)) e = S .equivNotion (X , s) (Y , t) e
AxiomsUnivalentNotion S ax isP .univalenceNotion {X , s , a} {Y , t , b} e =
  S .equivNotion (X , s) (Y , t) e
    ≃⟨ S .univalenceNotion e ⟩
  PathP (λ i → S .notion (ua e i)) s t
    ≃⟨ invEquiv (Σ-fst-≃ λ _ → isContr-retract (equiv→retract (PathP≃Path _ _ _)) (isProp→isContr≡ (isP _ _) _ _)) ⟩
  Σ[ p ∈ PathP (λ i → S .notion (ua e i)) s t ] PathP (λ i → ax (ua e i) (p i)) a b
    ≃⟨ ΣPath≃PathΣ ⟩
  PathP (λ i → AxiomsUnivalentNotion S ax isP .notion (ua e i)) (s , a) (t , b)
    ∎e
```

mvrnote: Re-do magma

Let's reconstruct the Magma example using these new combinators.

```
Magma-UnivalentNotionᵥ₂ : UnivalentNotion ℓ ℓ ℓ
Magma-UnivalentNotionᵥ₂ = FunctionUnivalentNotion PointedUnivalentNotion (FunctionUnivalentNotion PointedUnivalentNotion PointedUnivalentNotion)

Magmaᵥ₂ : (ℓ : Level) → Type (ℓ-suc ℓ)
Magmaᵥ₂ ℓ = Type-with ℓ (Magma-UnivalentNotionᵥ₂ .notion)
```

That was certainly much less work, but did we get the right thing out?
Not quite. The structure itself is correct:

```
_ : Magma-Str {ℓ} ≡ Magma-UnivalentNotionᵥ₂ {ℓ} .notion
_ = refl
```

But the notion of homomorphism is not, instead of reconstructing
``isMagmaHom``, instead we get the following equivalent, but more
annoying type.

```
isMagmaHomᵥ₂ : (A B : Magmaᵥ₂ ℓ) → (typ A → typ B) → Type ℓ
isMagmaHomᵥ₂ (A , _·A_) (B , _·B_) f
  = (a₁ : A) → (b₁ : B) → f a₁ ≡ b₁
  → (a₂ : A) → (b₂ : B) → f a₂ ≡ b₂
  → f (a₁ ·A a₂) ≡ b₁ ·B b₂

_ : (A B : Type-with ℓ (Magma-UnivalentNotionᵥ₂ .notion)) (e : _)
  → Magma-UnivalentNotionᵥ₂ .equivNotion A B e ≡ isMagmaHomᵥ₂ A B (e .map)
_ = λ A B e → refl
```


## Transport Structures

Let's spend some time trying to work around this.

```
record TransportNotion (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor univalentNotionData
  field
    notion : StrNotion ℓ ℓ'
    equivAction : {X Y : Type ℓ} → X ≃ Y → notion X ≃ notion Y
    transportStr : {X Y : Type ℓ} (e : X ≃ Y) (s : notion X) → equivAction e .map s ≡ subst notion (ua e) s
open TransportNotion

TransportNotion→UnivalentNotion : TransportNotion ℓ ℓ' → UnivalentNotion ℓ ℓ' ℓ'
TransportNotion→UnivalentNotion T .notion = T .notion
TransportNotion→UnivalentNotion T .equivNotion (X , s) (Y , t) e = T .equivAction e .map s ≡ t
TransportNotion→UnivalentNotion T .univalenceNotion {X , s} {Y , t} e =
  T .equivAction e .map s ≡ t
    ≃⟨ path→equiv (ap (_≡ t) (T .transportStr e s)) ⟩
  subst (T .notion) (ua e) s ≡ t
    ≃⟨ invEquiv (PathP≃Path _ _ _) ⟩
  PathP (λ i → T .notion (ua e i)) s t
  ∎e

ConstantTransportNotion : (A : Type ℓ') → TransportNotion ℓ ℓ'
ConstantTransportNotion A .notion _ = A
ConstantTransportNotion A .equivAction _ = idEquiv _
ConstantTransportNotion A .transportStr e _ = sym (transport-refl _)

PointedTransportNotion : TransportNotion ℓ ℓ
PointedTransportNotion .notion X = X
PointedTransportNotion .equivAction e = e
PointedTransportNotion .transportStr e _ = sym (transport-refl _)

ProductTransportNotion : (S₁ : TransportNotion ℓ ℓ₁) → (S₂ : TransportNotion ℓ ℓ₂) → TransportNotion ℓ (ℓ-max ℓ₁ ℓ₂)
ProductTransportNotion S₁ S₂ .notion X = S₁ .notion X × S₂ .notion X
ProductTransportNotion S₁ S₂ .equivAction e = ×-map-≃ (S₁ .equivAction e) (S₂ .equivAction e)
ProductTransportNotion S₁ S₂ .transportStr e (s₁ , s₂) i = (S₁ .transportStr e s₁ i , S₂ .transportStr e s₂ i)

FunctionUnivalentNotion+ : (S : TransportNotion ℓ ℓ₁) → (T : UnivalentNotion ℓ ℓ₂ ℓ₂') → UnivalentNotion ℓ (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₁ ℓ₂')
FunctionUnivalentNotion+ S T .notion X = S .notion X → T .notion X
FunctionUnivalentNotion+ S T .equivNotion (X , f) (Y , g) e =
   (s : S .notion X) → T .equivNotion (X , f s) (Y , g (S .equivAction e .map s)) e
FunctionUnivalentNotion+ S T .univalenceNotion {X , f} {Y , g} e =
  ((x : S .notion X) → T .equivNotion (X , f x) (Y , g (S .equivAction e .map x)) e)
    ≃⟨ Π-map-cod≃ (λ x → T .univalenceNotion e) ⟩
  ((s : S .notion X) → PathP (λ i → T .notion (ua e i)) (f s) (g (S .equivAction e .map s)))
    ≃⟨ path→equiv (λ i → ((s : S .notion X) → PathP (λ i → T .notion (ua e i)) (f s) (g (S .transportStr e s i)))) ⟩
  ((s : S .notion X) → PathP (λ i → T .notion (ua e i)) (f s) (g (subst (S .notion) (ua e) s)))
    ≃⟨ Π-map-cod≃ (λ _ → path→equiv (PathP≡Path' _ _ _) ) ⟩
  ((x : S .notion X) → f x ≡ transport (λ i → T .notion (ua e (~ i))) (g (subst (S .notion) (ua e) x)))
    ≃⟨ funext-≃ ⟩
  f ≡ (λ z → transport (λ i → T .notion (ua e (~ i))) (g (subst (S .notion) (ua e) z)))
    ≃⟨ invEquiv (path→equiv (PathP≡Path' _ f g))  ⟩
  PathP (λ i → S .notion (ua e i) → T .notion (ua e i)) f g
    ∎e

Magma-UnivalentStructure : UnivalentNotion ℓ ℓ ℓ
Magma-UnivalentStructure = FunctionUnivalentNotion+ PointedTransportNotion (FunctionUnivalentNotion+ PointedTransportNotion PointedUnivalentNotion)

_ : (A B : Type-with ℓ Magma-Str) (e : _)
  → Magma-UnivalentStructure .equivNotion A B e ≡ isMagmaHom A B (e .map)
_ = λ A B e → refl
```


## Queues again


```
MaybeStructure : (S : Type ℓ → Type ℓ₁) → Type ℓ → Type ℓ₁
MaybeStructure S X = Maybe (S X)

MaybeTransportNotion : TransportNotion ℓ ℓ' → TransportNotion ℓ ℓ'
MaybeTransportNotion S .notion X = Maybe (S .notion X)
MaybeTransportNotion S .equivAction e = ⊎-map-≃ (idEquiv ⊤) (S .equivAction e)
MaybeTransportNotion S .transportStr e (inl x) = refl
MaybeTransportNotion S .transportStr e (inr x) = ap inr (S .transportStr e x)
```

```
Queue-UnivalentStructure : (A : Type) → UnivalentNotion ℓ ℓ ℓ
Queue-UnivalentStructure A = ProductUnivalentNotion
  PointedUnivalentNotion
  (ProductUnivalentNotion (FunctionUnivalentNotion+ (ConstantTransportNotion A) (FunctionUnivalentNotion+ PointedTransportNotion PointedUnivalentNotion))
                          (FunctionUnivalentNotion+ PointedTransportNotion (TransportNotion→UnivalentNotion (MaybeTransportNotion (ProductTransportNotion PointedTransportNotion (ConstantTransportNotion A))))))
```


```
-- Now it only remains to prove that this is an equivalence of queue structures
quot∘emp : quot {A = A} empˢ ≡ empᶠ
quot∘emp = refl

quot∘enq : (x : A) → (xs : SlowQueue A) → quot (enqˢ x xs) ≡ enqᶠ x (quot xs)
quot∘enq x xs = refl

quot∘deq : (isSetA : isSet A) → (xs : SlowQueue A) → deqMap quot (deqˢ xs) ≡ deqᶠ isSetA (quot xs)
quot∘deq isSetA [] = refl
quot∘deq isSetA (x :: []) = refl
quot∘deq isSetA (x :: x' :: xs) =
  deqMap-∘ quot (enqˢ x) (deqˢ (x' :: xs))
  ∙ sym (deqMap-∘ (enqᶠ x) quot (deqˢ (x' :: xs)))
  ∙ ap (deqMap (enqᶠ x)) (quot∘deq isSetA (x' :: xs))
  ∙ lemma x x' (reverse xs)
  where
  lemma : ∀ x x' ys → deqMap (enqᶠ x) (deqFlush (ys ++ [ x' ])) ≡ deqFlush ((ys ++ [ x' ]) ++ [ x ])
  lemma x x' [] i        = inr (tilt [] [] x i , x')
  lemma x x' (y :: ys) i = inr (tilt [] (ys ++ [ x' ]) x i , y)

quotEquivHasQueueEquivStr : (A : Type) → (isSetA : isSet A) → Queue-UnivalentStructure A .equivNotion (SlowQueue-model A) (FastQueue-model A isSetA) (quotEquiv isSetA)
quotEquivHasQueueEquivStr A isSetA = quot∘emp , quot∘enq , quot∘deq isSetA
```

Let's get some payoff. There are lots of things we might like to be
true about queues, and they are easy to prove about our ``SlowQueue``.

```
returnOrEnq : (Q : Type-with ℓ-zero (Queue-Str A)) → A → Maybe (typ Q × A) → typ Q × A
returnOrEnq (Q , emp , enq , deq) a (inl tt) = emp , a
returnOrEnq (Q , emp , enq , deq) a (inr (q , b)) = enq a q , b

QueueAxioms : Type-with ℓ-zero (Queue-Str A) → Type ℓ-zero
QueueAxioms Q@(A , emp , enq , deq) = (deq emp ≡ inl tt)
   × (∀ a q → deq (enq a q) ≡ inr (returnOrEnq Q a (deq q)))
   × (∀ a a' q q' → enq a q ≡ enq a' q' → (a ≡ a') × (q ≡ q'))
   × (∀ q q' → deq q ≡ deq q' → q ≡ q')
```


## mvrnote: Project ideas?



## References and Further Reading

mvrnote:
https://1lab.dev/1Lab.Univalence.SIP.html
Internalizing Representation Independence with Univalence https://arxiv.org/abs/2009.05547
https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda
https://staff.math.su.se/anders.mortberg/slides/PalmgrenMemorial2020.pdf
https://dl.acm.org/doi/abs/10.1145/3373718.3394755



## Old
mvrnote: to be sorted/deleted

We will now revisit the previous simplified monoid structure to show how
we can construct it as a univalent structure.

Notice how we only used the raw monoid structure to define the univalent
structure above! We did that because there is a need to carefully separate
the raw structure of a type from its axioms. The reason for that is that we
need to show that every axiom on a structure is also a proposition.


We define an axiom structure as follows:

We can now use our new axiom structure to extend the raw monoid structure
to a full monoid with all of its axioms.

```
-- RawMonoidStructure : StrNotion ℓ ℓ
-- RawMonoidStructure = ProductStr PointedStr (FunctionStr PointedStr (FunctionStr PointedStr PointedStr))

-- RawMonoidEquivStr : StrEquivNotion RawMonoidStructure ℓ
-- RawMonoidEquivStr = ProductEquivStr PointedEquivStr (FunctionEquivStr PointedEquivStr (FunctionEquivStr PointedEquivStr PointedEquivStr))

-- RawMonoid : (ℓ : Level) → Type (ℓ-suc ℓ)
-- RawMonoid ℓ = Type-with ℓ RawMonoidStructure


-- ≃[Monoid]-univalent : UnivalentStr (RawMonoidStructure {ℓ}) (RawMonoidEquivStr {ℓ})
-- ≃[Monoid]-univalent = productUnivalentStr
--   {S₁ = PointedStr} pointedUnivalentStr
--   {S₂ = FunctionStr PointedStr (FunctionStr PointedStr PointedStr)} (functionUnivalentStr {T = FunctionStr PointedStr PointedStr} pointedUnivalentStr (functionUnivalentStr {T = PointedStr} pointedUnivalentStr pointedUnivalentStr))

-- RawMonoidEquivStr : StrEquivNotion RawMonoidStructure ℓ
-- RawMonoidEquivStr (A , (εA , _·A_)) (B , (εB , _·B_)) (φ , t) =
--   (φ εA ≡ εB) × ((a a' : A) → φ (a ·A a') ≡ φ a ·B φ a')
```

```
-- MonoidAxioms : (A : Type ℓ) → RawMonoidStructure A → Type ℓ
-- MonoidAxioms A (e , _·_) =
--     isSet A
--   × ((x y z : A) → x · (y · z) ≡ (x · y) · z)
--   × ((x : A) → x · e ≡ x)
--   × ((x : A) → e · x ≡ x)

-- MonoidStructure : StrNotion ℓ ℓ
-- MonoidStructure = AxiomsStr RawMonoidStructure MonoidAxioms

-- Monoid : (ℓ : Level) → Type (ℓ-suc ℓ)
-- Monoid ℓ = Type-with ℓ MonoidStructure

-- MonoidEquivStr : StrEquivNotion MonoidStructure ℓ
-- MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

-- isPropMonoidAxioms : (M : Type ℓ) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
-- isPropMonoidAxioms M (e , _·_) = isPropΣ isProp-isSet λ s →
--   isProp× (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → s _ _) (
--   isProp× (isPropΠ λ _ → s _ _)
--           (isPropΠ λ _ → s _ _))
  -- mvrnote: Or directly, eg
  -- λ x y i → (λ x₁ y₁ z → s _ _ (fst x x₁ y₁ z) (fst y x₁ y₁ z) i) , ({!!} , {!!})

-- monoidUnivalentStr : ∀ {ℓ} → UnivalentStr (MonoidStructure {ℓ}) (MonoidEquivStr {ℓ})
-- monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr
```

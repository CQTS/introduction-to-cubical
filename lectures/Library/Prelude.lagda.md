<!--
```
module Library.Prelude where
```
-->


# Prelude

The vast majority of the code that we use is defined in the lectures,
but we do define some of the basics behind the scenes here.

First, we import the built-in cubical operations that Agda
provides, giving them more readable names.

```
import Library.Primitive as Prim

open Prim public
  renaming (primINeg to ~_;
            primIMax to _∨_;
            primIMin to _∧_;
            primTransp to transport-fixing
  )
```

We slightly fiddle the definition of the primitive ``hcomp``, so that
the base of the composition is included in the partial element rather
than being provided separately.

A trick from the 1lab are used to make ``hcomp`` print nicely in goals
<https://github.com/the1lab/1lab/pull/468>.

``` 
hcomp : {ℓ : Level} {A : Type ℓ} (φ : I) 
  → (u : (i : I) → Partial (φ ∨ ~ i) A) → A
hcomp {A = A} φ u = primHComp sys (u i0 IsOne-i1) module hcomp-sys where 
  sys : ∀ j → Partial φ A 
  sys j (φ = i1) = u j IsOne-i1

{-# DISPLAY primHComp {ℓ} {A} {φ} (hcomp-sys.sys _ u) _ = hcomp {ℓ} {A} φ u #-}
```


## Σ-Types

Although in Lecture 1-1 we treat Σ-types as a built-in type
constructor, we in fact define them manually as a "record" type, which
we discuss in Lecture 1-4.

```
record Σ {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

open Σ public -- This allows us to use the `fst` and `snd` projections
              -- unqualified.
```

The following lines enable the `Σ[ x ∈ A ] B x` syntax, whereas
normally we would not be able to bind a variable `x` in this way.

```
infix 2 Σ-syntax

Σ-syntax : {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

The non-dependent ``×``-types are the instance of ``Σ``-types where the second
component does not depend on the first.

```
_×_ : {ℓ ℓ' : Level} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ[ a ∈ A ] B

infixr 5 _×_
```


## Path Types

``PathP`` is the primitive notion, but we give some convenient
syntax for non-dependent paths.

```
Path : {ℓ : Level} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)

infix 4 _≡_

_≡_ : {ℓ : Level} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = Path A

{-# BUILTIN PATH _≡_ #-}
```

## Case Analysis

The notion of pattern matching λ-abstractions is built into Agda. The
following mixfix definition gives some nicer syntax for case analysis,
making it look more like the case splitting notation used in other
functional languages. See the top of Lecture 1-2 for examples.

```
case_of_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A → (A → B) → B
case x of f = f x

infix 0 case_of_
```


## Computation Tests

The ``test-identical`` helper is used to write tests that definitions
compute correctly. Evaluating `test-identical a a'` will fail unless
`a` and `a'` can be unified by Agda.

```
data Test-Id-Family {ℓ : Level} {A : Type ℓ} (x : A) : A → Type ℓ where
  instance test-id-refl : Test-Id-Family x x

data Test-Identical {ℓ : Level} {A : Type ℓ} : Type ℓ where
  test-identical : (a a' : A) → {{Test-Id-Family a a'}} → Test-Identical
```

The ``test-type`` helper checks that a term has the expected type. We
order the arguments so that the term comes before the type, because we
want `a : A` to be tested by `test-type a A`.

```
data Test-Type {ℓ : Level} : Type (ℓ-suc ℓ) where
  test-type : {A : Type ℓ} → (a : A) → (A' : Type ℓ) → {{Test-Id-Family A A'}} → Test-Type
```

These helpers are defined using a trick involving "instance
arguments", which we don't talk about at all in these notes, sorry.


## Natural Numbers

We define the natural numbers and a couple of functions here, so that
we can use them in as examples in Lecture 1-1. They are properly
discussed in Lecture 1-2.

```
data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

_·_ : ℕ → ℕ → ℕ
zero · m = zero
(suc n) · m = m + (n · m)

infixl 6 _+_
infixl 7 _·_
```

The following code sets up Agda to let us write numerals like `1`,
`2`, etc. and have it automatically interpreted as a natural number or
integer as appropriate.

```
record Number {ℓ : Level} (A : Type ℓ) : Type ℓ where
  field fromNat : ℕ → A

open Number {{...}} public using (fromNat)

record Negative {ℓ : Level} (A : Type ℓ) : Type ℓ where
  field fromNeg : ℕ → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-ℕ : Number ℕ
  Number-ℕ .fromNat n = n
```

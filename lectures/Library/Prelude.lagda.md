```
module Library.Prelude where
```


# Prelude

The vast majority of the code that we use is defined in the lectures,
but we do define some of the basics behind the scenes here.

First, we import all the primitive, built-in operations that Agda
provides, giving them more readable names.

```
open import Library.Primitive public
  renaming (primINeg to ~_;
            primIMax to _∨_;
            primIMin to _∧_;
            primHComp to hcomp;
            primTransp to transp;
            primComp to comp;
            itIsOne to 1=1;
            Sub to _[_↦_];
            primSubOut to outS
  )
```

## Σ-Types

Although in the text we treat Σ-types as a built-in type constructor,
we in fact define them manually as a "record" type. We do not discuss
record types in these lecture notes.

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
normally we would not be able to bind a new variable `x` in this way.

```
infix 2 Σ-syntax

Σ-syntax : {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
```

The `×`{.Agda}-types are the instance so Σ-types where the second
component does not actually depend on the first.

```
_×_ : {ℓ ℓ' : Level} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ[ a ∈ A ] B
```


## Path Types

`PathP`{.Agda} is the primitive notion, but we give some convenient
syntax for non-dependent paths.

```
Path : {ℓ : Level} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)

infix 4 _≡_

_≡_ : {ℓ : Level} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = Path A

{-# BUILTIN PATH _≡_ #-}
```


## The Natural Numbers

We define the natural numbers and a couple of example functions here,
so that we can use them in examples in Lecture 1-1. They are properly
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

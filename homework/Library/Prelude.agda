module homework.Library.Prelude where

open import homework.Library.Primitive public
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

-- Homogeneous filling
hfill : ∀ {ℓ} {A : Type ℓ} {φ : I}
          (u : ∀ i → Partial φ A)
          (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- Heterogeneous filling defined using comp
fill : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i0 [ φ ↦ u i0 ]) →
         ∀ i →  A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → \ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0 })
       (outS {φ = φ} u0)

record Σ {a b} (A : Type a) (B : A → Type b) : Type (ℓ-max a b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)

infix 4 _≡_

_≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = Path A

{-# BUILTIN PATH _≡_ #-}

idfun : {ℓ : Level} (A : Type ℓ) → A → A
idfun A x = x

_∘_ : {ℓ ℓ' ℓ'' : Level}
      {A : Type ℓ}
      {B : A → Type ℓ'}
      {C : (x : A) → B x → Type ℓ''}

      (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)

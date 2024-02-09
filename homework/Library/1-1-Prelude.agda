module homework.Library.1-1-Prelude where

open import homework.Library.Prelude

private
  to-path : ∀ {ℓ} {A : Type ℓ} → (f : I → A) → Path A (f i0) (f i1)
  to-path f i = f i

refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = to-path (λ i → x)

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

MultiplesOf : ℕ → Type
MultiplesOf n = Σ[ m ∈ ℕ ] Σ[ i ∈ ℕ ] m ≡ i · n

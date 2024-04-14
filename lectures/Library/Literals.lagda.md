```
module Library.Literals where

open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types

record TrivialConstraint : Type where
  instance constructor constraint-trivially-holds

record Number {a} (A : Type a) : Type (ℓ-suc a) where
  field
    Constraint : ℕ → Type a
    fromNat : ∀ n → {{_ : Constraint n}} → A

open Number {{...}} public using (fromNat)

record Negative {a} (A : Type a) : Type (ℓ-suc a) where
  field
    Constraint : ℕ → Type a
    fromNeg : ∀ n → {{_ : Constraint n}} → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-Nat : Number ℕ
  Number-Nat .Number.Constraint _ = TrivialConstraint
  Number-Nat .Number.fromNat n = n

  Number-Int : Number ℤ
  Number-Int .Number.Constraint _ = TrivialConstraint
  Number-Int .Number.fromNat n    = pos n

  Negative-Int : Negative ℤ
  Negative-Int .Negative.Constraint _ = TrivialConstraint
  Negative-Int .Negative.fromNeg zero = pos zero
  Negative-Int .Negative.fromNeg (suc x) = negsuc x
```

module homework.Library.Primitive where

{-# BUILTIN PROP           Prop      #-}
{-# BUILTIN TYPE           Type      #-}
{-# BUILTIN STRICTSET      SSet      #-}

{-# BUILTIN PROPOMEGA      Propω     #-}
{-# BUILTIN SETOMEGA       Typeω     #-}
{-# BUILTIN STRICTSETOMEGA SSetω     #-}

{-# BUILTIN LEVELUNIV      LevelUniv #-}

-- Level is the first thing we need to define.
-- The other postulates can only be checked if built-in Level is known.

postulate
  Level : LevelUniv

{-# BUILTIN LEVEL Level #-}

postulate
  ℓ-zero : Level
  ℓ-suc  : (ℓ : Level) → Level
  ℓ-max   : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVELZERO ℓ-zero #-}
{-# BUILTIN LEVELSUC  ℓ-suc  #-}
{-# BUILTIN LEVELMAX  ℓ-max   #-}

{-# BUILTIN CUBEINTERVALUNIV IUniv #-}  -- IUniv : SSet₁
{-# BUILTIN INTERVAL I  #-}  -- I : IUniv

{-# BUILTIN IZERO    i0 #-}
{-# BUILTIN IONE     i1 #-}

infix  30 primINeg
infixr 20 primIMin primIMax

primitive
    primIMin : I → I → I
    primIMax : I → I → I
    primINeg : I → I

{-# BUILTIN ISONE    IsOne    #-}  -- IsOne : I → Setω

postulate
  itIsOne : IsOne i1
  IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
  IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)

{-# BUILTIN ITISONE  itIsOne  #-}
{-# BUILTIN ISONE1   IsOne1   #-}
{-# BUILTIN ISONE2   IsOne2   #-}

{-# BUILTIN PARTIAL  Partial  #-}
{-# BUILTIN PARTIALP PartialP #-}

postulate
  isOneEmpty : ∀ {ℓ} {A : Partial i0 (Type ℓ)} → PartialP i0 A

{-# BUILTIN ISONEEMPTY isOneEmpty #-}

primitive
  primPOr : ∀ {ℓ} (i j : I) {A : Partial (primIMax i j) (Type ℓ)}
            → (u : PartialP i (λ z → A (IsOne1 i j z)))
            → (v : PartialP j (λ z → A (IsOne2 i j z)))
            → PartialP (primIMax i j) A

  -- Computes in terms of primHComp and primTransp
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

syntax primPOr p q u t = [ p ↦ u , q ↦ t ]

primitive
  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A

postulate
  PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP PathP #-}

{-# BUILTIN SUB Sub #-}

postulate
  inS : ∀ {ℓ} {A : Type ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

{-# BUILTIN SUBIN inS #-}

primitive
  primSubOut : ∀ {ℓ} {A : Type ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A


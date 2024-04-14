```
module Library.Primitive where
```

# Agda Primitives

This module is the very first thing that is imported in all our files.
It mostly consists of assigning names to a bunch of built in Agda
constructions, some of which we rename to make more convenient to use
in `Library.Prelude`. mvrnote: link when those work again

## Universes

```
{-# BUILTIN PROP           IrrProp      #-}
{-# BUILTIN TYPE           Type      #-}
{-# BUILTIN STRICTSET      SSet      #-}

{-# BUILTIN PROPOMEGA      IrrPropω     #-}
{-# BUILTIN SETOMEGA       Typeω     #-}
{-# BUILTIN STRICTSETOMEGA SSetω     #-}

{-# BUILTIN LEVELUNIV      LevelUniv #-}

postulate
  Level : LevelUniv
  ℓ-zero : Level
  ℓ-suc  : (ℓ : Level) → Level
  ℓ-max  : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO ℓ-zero #-}
{-# BUILTIN LEVELSUC  ℓ-suc  #-}
{-# BUILTIN LEVELMAX  ℓ-max   #-}
```

## The Interval

```
{-# BUILTIN CUBEINTERVALUNIV IUniv #-}  -- IUniv : SSet₁
{-# BUILTIN INTERVAL I  #-}             -- I : IUniv

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
```

## Partial Elements

```
{-# BUILTIN PARTIAL  Partial  #-}
{-# BUILTIN PARTIALP PartialP #-}

postulate
  isOneEmpty : ∀ {ℓ} {A : Partial i0 (Type ℓ)} → PartialP i0 A

primitive
  primPOr : ∀ {ℓ} (i j : I) {A : Partial (primIMax i j) (Type ℓ)}
            → (u : PartialP i (λ z → A (IsOne1 i j z)))
            → (v : PartialP j (λ z → A (IsOne2 i j z)))
            → PartialP (primIMax i j) A

{-# BUILTIN ISONEEMPTY isOneEmpty #-}

syntax primPOr p q u t = [ p ↦ u , q ↦ t ]

{-# BUILTIN SUB Sub #-}

postulate
  inS : ∀ {ℓ} {A : Type ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

{-# BUILTIN SUBIN inS #-}

primitive
  primSubOut : ∀ {ℓ} {A : Type ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A
```

## Composition and Transport

```
primitive
  -- Computes in terms of `primHComp` and `primTransp`
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

primitive
  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A

postulate
  PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP PathP #-}

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)

infix 4 _≡_

_≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = Path A

{-# BUILTIN PATH _≡_ #-}
```

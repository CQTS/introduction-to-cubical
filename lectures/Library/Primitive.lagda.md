```
module Library.Primitive where
```

# Agda Primitives

This module is the very first thing that Agda sees when loading our
files. It consists entirely of assigning names to various built-in
Agda constructions, some of which we rename when this file is imported
in `Library.Prelude`.


## Universes

We declare we will be using `Type`{.Agda} as our name for the
universes of types.

```
{-# BUILTIN TYPE           Type             #-}
```

We also need to assign names to some other notions of universe
provided by Agda, even though we never use them.

```
{-# BUILTIN SETOMEGA       Unused-Typeω     #-}
{-# BUILTIN PROP           Unused-Prop      #-}
{-# BUILTIN PROPOMEGA      Unused-Propω     #-}
{-# BUILTIN STRICTSET      Unused-SSet      #-}
{-# BUILTIN STRICTSETOMEGA Unused-SSetω     #-}
```

Now, our notation for universe levels.

```
{-# BUILTIN LEVELUNIV      LevelUniv        #-}

postulate
  Level : LevelUniv
  ℓ-zero : Level
  ℓ-suc  : (ℓ : Level) → Level
  ℓ-max  : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO ℓ-zero #-}
{-# BUILTIN LEVELSUC  ℓ-suc  #-}
{-# BUILTIN LEVELMAX  ℓ-max   #-}
```


## The Interval

We give a name to the interval and the special universe that it lives
in, and names for the endpoints of the interval.

```
{-# BUILTIN CUBEINTERVALUNIV IUniv #-}
{-# BUILTIN INTERVAL I  #-}

{-# BUILTIN IZERO    i0 #-}
{-# BUILTIN IONE     i1 #-}
```

These are the built-in De Morgan operations on the interval, which we
give a better syntax for when importing them in `Library.Prelude`.

```
infix  30 primINeg
infixr 20 primIMin primIMax

primitive
    primIMin : I → I → I -- ∧
    primIMax : I → I → I -- ∨
    primINeg : I → I     -- ~
```

This a built-in `IsOne` predicate for when an element of `I` is equal
to `i1`, only used behind the scenes.

```
{-# BUILTIN ISONE    IsOne    #-}

postulate
  itIsOne : IsOne i1
  IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
  IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)

{-# BUILTIN ITISONE  itIsOne  #-}
{-# BUILTIN ISONE1   IsOne1   #-}
{-# BUILTIN ISONE2   IsOne2   #-}
```

## Partial Elements

These declare the notions partiale elements and cubical subtypes that
we discuss a little in Lecture 2-4.

```
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

syntax primPOr p q u t = [ p ↦ u , q ↦ t ]

{-# BUILTIN SUB Sub #-}

postulate
  inS : ∀ {ℓ} {A : Type ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

{-# BUILTIN SUBIN inS #-}

primitive
  primSubOut : ∀ {ℓ} {A : Type ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A
```


## Composition and Transport

Here we have `transp`{.Agda}, discussed in Lecture 2-3 and
`hcomp`{.Agda}, discussed in Lecture 2-4.

```
primitive
  -- Computes in terms of `primHComp` and `primTransp`
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
```

## Paths

Finally we have the primitive notion of `PathP`{.Agda}.

```
postulate
  PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP PathP #-}
```

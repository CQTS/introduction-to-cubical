<!--
```
module Library.Primitive where
```
-->

# Agda Primitives

This module is the very first thing that Agda sees when loading our
files. It consists entirely of assigning names to various built-in
Agda constructions, some of which we rename when this file is imported
in `Library.Prelude`.


## Universes

We declare we will be using ``Type`` as the name for the universes of
ntypes.

```
{-# BUILTIN TYPE           Type             #-}
```

We also have the universe hierarchy of "strict sets", which are
mentioned very briefly in Lecture 2-4.

```
{-# BUILTIN STRICTSET      SSet             #-}
```

We also need to assign names to some other notions of universe
provided by Agda, even though we never use them.

```
{-# BUILTIN SETOMEGA       Unused-Typeω     #-}
{-# BUILTIN STRICTSETOMEGA Unused-SSetω     #-}
{-# BUILTIN PROP           Unused-Prop      #-}
{-# BUILTIN PROPOMEGA      Unused-Propω     #-}
```

Now, our notation for universe levels which we discuss in Lecture 1-3.

```
{-# BUILTIN LEVELUNIV      LevelUniv        #-}

postulate
  Level : LevelUniv
  ℓ-zero : Level
  ℓ-suc  : (ℓ : Level) → Level
  ℓ-max  : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVEL          Level            #-}
{-# BUILTIN LEVELZERO      ℓ-zero           #-}
{-# BUILTIN LEVELSUC       ℓ-suc            #-}
{-# BUILTIN LEVELMAX       ℓ-max            #-}
```


## The Interval

We give a name to the interval and the special universe that it lives
in, and names for the endpoints of the interval.

```
-- Roughly:
-- postulate
--   IUniv : SSet (ℓ-suc ℓ-zero)
--   I  : IUniv
--   i0 : I
--   i1 : I

{-# BUILTIN CUBEINTERVALUNIV IUniv          #-}
{-# BUILTIN INTERVAL       I                #-}
{-# BUILTIN IZERO          i0               #-}
{-# BUILTIN IONE           i1               #-}
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

And the primitive notion of ``PathP``, discussed in Lecture 2-1.

```
postulate
  PathP : {ℓ : Level} → (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP          PathP            #-}
```

## Partial Elements

First, a built-in ``IsOne`` predicate for when an element of ``I`` is
equal to ``i1``.

```
-- Roughly:
-- IsOne : I → SSet
-- IsOne i = (i ≡ i1)

{-# BUILTIN ISONE          IsOne            #-}
```

And some basic facts about it:

```
postulate
  IsOne-i1   : IsOne i1
  IsOne-inl  : (i j : I) → IsOne i → IsOne (primIMax i j)
  IsOne-inr  : (i j : I) → IsOne j → IsOne (primIMax i j)

{-# BUILTIN ITISONE        IsOne-i1         #-}
{-# BUILTIN ISONE1         IsOne-inl        #-}
{-# BUILTIN ISONE2         IsOne-inr        #-}
```

And then partial elements of types, including partial elements of
partial types. (Like how ``Path`` relates to ``PathP``.)

```
-- Roughly:
-- Partial : {ℓ : Level} (φ : I) (A : Type ℓ) → SSet ℓ
-- Partial φ A = IsOne φ → A
-- PartialP : {ℓ : Level} (φ : I) (A : Partial φ (Type ℓ)) → SSet ℓ
-- PartialP φ A = (t : IsOne φ) → A t

{-# BUILTIN PARTIAL        Partial          #-}
{-# BUILTIN PARTIALP       PartialP         #-}
```

Some interactions of ``PartialP`` with the ``IsOne`` predicate are
axiomatised. First, you can get a partial element of any type `A`, as
long as that partial element is defined nowhere.

```
postulate
  isOneEmpty : {ℓ : Level} {A : Partial i0 (Type ℓ)} → PartialP i0 A

{-# BUILTIN ISONEEMPTY     isOneEmpty       #-}
```

And if you have two partial elements of the same type, you can take
the union of these types, so long as they agree on the overlap where
they are both defined.

```
primitive
  primPOr : {ℓ : Level} (i j : I) {A : Partial (primIMax i j) (Type ℓ)}
            → (u : PartialP i (λ z → A (IsOne-inl i j z)))
            → (v : PartialP j (λ z → A (IsOne-inr i j z)))
            → PartialP (primIMax i j) A
```

These declare the notion of cubical subtype, which have tried our best
to avoid discussing in these notes.

```
-- Roughly:
-- Sub : {ℓ : Level} (A : Type ℓ) (φ : I) → (IsOne φ → A) → Type ℓ
-- Sub A φ u = Σ[ a ∈ A ] ((t : IsOne φ) → a ≡ u t)

{-# BUILTIN SUB            Sub              #-}

postulate
  inS : {ℓ : Level} {A : Type ℓ} {φ : I} → (x : A) → Sub A φ (λ _ → x)

{-# BUILTIN SUBIN          inS              #-}

primitive
  primSubOut : {ℓ : Level} {A : Type ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A
```


## Composition and Transport

Here we have ``transport-fixing`` operation, discussed in Lectures 2-3
and 2-5, and ``hcomp`` discussed in Lecture 2-4.

```
primitive
  primTransp : {ℓ : _} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : {ℓ : Level} {A : Type ℓ} {φ : I} (u : (i : I) → Partial φ A) (a : A) → A
```

Finally, so-called "heterogeneous" composition, which is used behind
the scenes but which we don't end up calling on ourselves.

```
  primComp : {ℓ : _} (A : (i : I) → Type (ℓ i)) {φ : I} (u : (i : I) → Partial φ (A i)) (a : A i0) → A i1
```

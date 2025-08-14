module Library.Univalence where

import Library.Primitive
open import Library.Prelude
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

-- We prove Equiv→Bijection in Section 2-9, but we don't have it at
-- this point. We copy the proof here.
private
  isContr : Type ℓ → Type ℓ
  isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

  flippedFiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
  flippedFiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)

  isBijection : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
  isBijection {A = A} f = ∀ b → isContr (flippedFiber f b)

  module _ {f : A → B} (isI : isEquiv f) where
    private
      g = isI .section .map
      s : isSection f g
      s = isI .section .proof
      g' = isI .retract .map
      t : isSection g' f
      t = isI .retract .proof

      module _ (y : A) (x0 x1 : B) (p0 : g x0 ≡ y) (p1 : g x1 ≡ y) where
        fill0 : Square (ap f (sym p0)) (ap f (sym p0) ∙ s x0) refl (s x0)
        fill0 = ∙-filler (ap f (sym p0)) (s x0)

        fill1 : Square (ap f (sym p1)) (ap f (sym p1) ∙ s x1) refl (s x1)
        fill1 = ∙-filler (ap f (sym p1)) (s x1)

        fill2 : Square refl (sym (fill0 i1) ∙∙ refl ∙∙ (fill1 i1)) (fill0 i1) (fill1 i1)
        fill2 = ∙∙-filler (sym (fill0 i1)) refl (fill1 i1)

        p : x0 ≡ x1
        p = fill2 i1

        sq : Square (ap (f ∘ g) p) refl (ap f p0) (ap f p1) 
        sq i j = hcomp (∂ i ∨ ∂ j) (λ k → λ { (i = i0) → s (p j) (~ k)
                                ; (i = i1) → f y
                                ; (j = i0) → fill0 (~ k) (~ i)
                                ; (j = i1) → fill1 (~ k) (~ i)
                                ; (k = i0) → fill2 (~ i) j})

        sq1 : Square (ap g p) refl p0 p1
        sq1 i j = hcomp (∂ i ∨ ∂ j) (λ k → λ { 
                                   (i = i0) → t (g (p j)) k
                                 ; (i = i1) → t y k
                                 ; (j = i0) → t (p0 i) k
                                 ; (j = i1) → t (p1 i) k 
                                 ; (k = i0) → g' (sq i j)})

        lemEquiv : (x0 , p0) ≡ (x1 , p1)
        fst (lemEquiv i) = p i
        snd (lemEquiv i) j = sq1 j i

    isProp→with-point-isContr : {A : Type ℓ} → ((x y : A) → x ≡ y) → (A → isContr A)
    isProp→with-point-isContr p a = a , p a

    isEquiv→secIsBijection : isBijection g
    isEquiv→secIsBijection y = isProp→with-point-isContr (λ (x0 , p0) (x1 , p1) → lemEquiv y x0 x1 p0 p1) (f y , sec≡ret (equiv f isI) (f y) ∙ t y )

  Equiv→Bijection : A ≃ B → Σ[ f ∈ (A → B) ] isBijection f
  Equiv→Bijection (equiv f isE) = (f , isEquiv→secIsBijection (invEquiv (equiv f isE) .proof))

builtinEquivProof : ∀ {la lt} (T : Type la) (A : Type lt) → (w : T ≃ A) → (a : A)
           → ∀ ψ (f : Partial ψ (flippedFiber (w .map) a)) → Sub (flippedFiber (w .map) a) ψ f
builtinEquivProof A B v a ψ fb =
  inS (contr' {A = flippedFiber (w .fst) a} (w .snd a) ψ fb)
  where
    w = Equiv→Bijection v
    contr' : {ℓ : Level} {A : Type ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' (c , p) φ u = primHComp (λ i → λ { (φ = i1) → p (u IsOne-i1) i
                                            ; (φ = i0) → c }) c

{-# BUILTIN EQUIV      _≃_               #-}
{-# BUILTIN EQUIVFUN   map               #-}
{-# BUILTIN EQUIVPROOF builtinEquivProof #-}

private
  -- Homogeneous filling
  hfill : {ℓ : Level} {A : Type ℓ} {φ : I}
        → (u : (i : I) → Partial φ A)
        → (u0 : Sub A φ (u i0))
        → Path A (primSubOut u0) (primHComp (λ { j (φ = i1) → u j IsOne-i1 }) (primSubOut u0))
  hfill {φ = φ} u u0 i =
    primHComp (λ j → λ { (φ = i1) → u (i ∧ j) IsOne-i1
                   ; (i = i0) → primSubOut u0 })
          (primSubOut u0)

  -- Heterogeneous filling defined using comp
  fill : {ℓ : Level} (A : ∀ i → Type ℓ) {φ : I}
           (u : ∀ i → Partial φ (A i))
           (u0 : Sub (A i0) φ (u i0)) →
            (i : I) →  A i
  fill A {φ = φ} u u0 i =
    primComp (λ j → A (i ∧ j))
         (λ j → λ { (φ = i1) → u (i ∧ j) IsOne-i1
                  ; (i = i0) → primSubOut u0 })
         (primSubOut {φ = φ} u0)

transpProof : {ℓ : Level} → (e : I → Type ℓ) → (φ : I) → (a : Partial φ (e i0)) → (b : Sub (e i1) φ (λ o → transport-fixing (λ i → e i) i0 (a o)) ) → flippedFiber (transport-fixing (λ i → e i) i0) (primSubOut b)
transpProof e φ a b = f , λ j → primComp (λ i → e i) (λ i →
                                               λ { (φ = i1) → transport-fixing (λ j → e (j ∧ i)) (~ i) (a IsOne-i1)
                                                 ; (j = i0) → transport-fixing (λ j → e (j ∧ i)) (~ i) f
                                                 ; (j = i1) → g (~ i) })
                                        f
    where
      b' = primSubOut {u = (λ o → transport-fixing (λ i → e i) i0 (a o))} b
      g : (k : I) → e (~ k)
      g k = fill (λ i → e (~ i)) (λ i → λ { (φ = i1) → transport-fixing (λ j → e (j ∧ ~ i)) i (a IsOne-i1)
                                          ; (φ = i0) → transport-fixing (λ j → e (~ j ∨ ~ i)) (~ i) b' }) (inS b') k
      f = primComp (λ i → e (~ i)) (λ i → λ { (φ = i1) → transport-fixing (λ j → e (j ∧ ~ i)) i (a IsOne-i1); (φ = i0) → transport-fixing (λ j → e (~ j ∨ ~ i)) (~ i) b' }) b'

{-# BUILTIN TRANSPPROOF transpProof #-}

private module GluePrimitives where primitive
  primGlue    : {ℓ ℓ' : Level} (A : Type ℓ) {φ : I}
    → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
    → Type ℓ'

  prim^glue   : {ℓ ℓ' : Level} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → (t : PartialP φ T) → (a : A) → primGlue A T e

  prim^unglue : {ℓ ℓ' : Level} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → primGlue A T e → A

  -- These need to be bound, but aren't ever used manually
  prim^glueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
               {A : Sub (Type ℓ) φ (T i0)} →
               PartialP φ (T i1) → primSubOut A → primHComp T (primSubOut A)

  prim^unglueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
                 {A : Sub (Type ℓ) φ (T i0)} →
                 primHComp T (primSubOut A) → primSubOut A

  primFaceForall : (I → I) → I

open GluePrimitives public renaming (prim^glue to glue)

Glue : (A : Type ℓ)
     → {φ : I}
     → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
     → Type ℓ'
Glue A {φ} Te = primGlue A tys eqvs module glue-sys where
  tys : Partial φ (Type _)
  tys (φ = i1) = Te IsOne-i1 .fst

  eqvs : PartialP φ (λ .o → tys _ ≃ A)
  eqvs (φ = i1) = Te IsOne-i1 .snd

{-# DISPLAY primGlue A (glue-sys.tys _ Te) (glue-sys.eqvs _ Te) = Glue A Te #-}

-- Make the φ argument of prim^unglue explicit
unglue
  : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
    {e : PartialP φ (λ o → T o ≃ A)}
  → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

{-# DISPLAY prim^unglue {l} {l'} {A} {φ} {t} {e} x = unglue {l} {l'} {A} φ {t} {e} x #-}

-- Unfortunately we can't do the same for prim^glue without involving
-- cubical subtypes (which we are trying to avoid)

-- {-# DISPLAY prim^glue {_} {_} {_} {φ} {_} {_} x y = glue x y #-}

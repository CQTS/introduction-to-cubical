module Library.Univalence where

-- mvrnote: we should add some commentary to this file, because you
-- can easily get here by clicking `Glue` for example.

open import Library.Primitive public
  renaming (primComp to comp;
            Sub to _[_↦_];
            primSubOut to outS)
open import Library.Prelude
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

-- We prove Equiv→Bijection in Section 2-X, but we don't have it at
-- this point. We copy the proof here.
-- mvrnote: cleanup
private
  isContr : Type ℓ → Type ℓ
  isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

  fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
  fiber {A = A} f y = Σ[ x ∈ A ] (y ≡ f x)

  flippedFiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
  flippedFiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)

  flippedFiber-isContr : {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} → isContr (fiber f b) → isContr (flippedFiber f b)
  flippedFiber-isContr ((a , p) , h) .fst = a , sym p
  flippedFiber-isContr ((a , p) , h) .snd (a₂ , p₂) i .fst = fst (h (a₂ , sym p₂) i)
  flippedFiber-isContr ((a , p) , h) .snd (a₂ , p₂) i .snd = sym (snd (h (a₂ , sym p₂) i))

  isBijection : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
  isBijection {A = A} f = ∀ b → isContr (Σ[ a ∈ A ] (b ≡ f a))

  module _ {f : A → B} (isI : isEquiv f) where
    private
      g = isI .section .map
      s : isSection f g
      s = isI .section .proof
      g' = isI .retract .map
      t : isSection g' f
      t = isI .retract .proof

      module _ (y : A) (x0 x1 : B) (p0 : y ≡ g x0) (p1 : y ≡ g x1) where
        fill0 : Square (ap f p0) (ap f p0 ∙ s x0) refl (s x0)
        fill0 = ∙-filler (ap f p0) (s x0)

        fill1 : Square (ap f p1) (ap f p1 ∙ s x1) refl (s x1)
        fill1 = ∙-filler (ap f p1) (s x1)

        fill2 : Square refl (sym (fill0 i1) ∙∙ refl ∙∙ (fill1 i1)) (fill0 i1) (fill1 i1)
        fill2 = ∙∙-filler (sym (fill0 i1)) refl (fill1 i1)

        p : x0 ≡ x1
        p = fill2 i1

        sq : Square refl (ap (f ∘ g) p) (ap f p0) (ap f p1)
        sq i j = primHComp (λ k → λ { (i = i0) → f y
                                ; (i = i1) → s (p j) (~ k)
                                ; (j = i0) → fill0 (~ k) i
                                ; (j = i1) → fill1 (~ k) i })
                       (fill2 i j)

        sq1 : Square refl (ap g p) p0 p1
        sq1 i j = primHComp (λ k → λ { (i = i0) → t y k
                                 ; (i = i1) → t (g (p j)) k
                                 ; (j = i0) → t (p0 i) k
                                 ; (j = i1) → t (p1 i) k })
                        (g' (sq i j))

        lemEquiv : (x0 , p0) ≡ (x1 , p1)
        fst (lemEquiv i) = p i
        snd (lemEquiv i) j = sq1 j i

    isProp→with-point-isContr : {A : Type ℓ} → ((x y : A) → x ≡ y) → (A → isContr A)
    isProp→with-point-isContr p a = a , p a

    isEquiv→secIsBijection : isBijection g
    isEquiv→secIsBijection y = isProp→with-point-isContr (λ (x0 , p0) (x1 , p1) → lemEquiv y x0 x1 p0 p1) (f y , sym (t y) ∙ sym (sec≡ret (equiv f isI) (f y)))

  Equiv→Bijection : A ≃ B → Σ[ f ∈ (A → B) ] isBijection f
  Equiv→Bijection (equiv f isE) = (f , isEquiv→secIsBijection (proof (invEquiv (equiv f isE))))

builtinEquivProof : ∀ {la lt} (T : Type la) (A : Type lt) → (w : T ≃ A) → (a : A)
           → ∀ ψ (f : Partial ψ (flippedFiber (w .map) a)) → flippedFiber (w .map) a [ ψ ↦ f ]
builtinEquivProof A B v a ψ fb =
  inS (contr' {A = flippedFiber (w .fst) a} (flippedFiber-isContr (w .snd a)) ψ fb)
  where
    w = Equiv→Bijection v
    contr' : ∀ {ℓ} {A : Type ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' {A = A} (c , p) φ u = primHComp (λ i → λ { (φ = i1) → p (u IsOne-i1) i
                                                ; (φ = i0) → c }) c

{-# BUILTIN EQUIV      _≃_               #-}
{-# BUILTIN EQUIVFUN   map               #-}
{-# BUILTIN EQUIVPROOF builtinEquivProof #-}

private
  -- Homogeneous filling
  hfill : {ℓ : Level} {A : Type ℓ} {φ : I}
        → (u : (i : I) → Partial φ A)
        → (u0 : A [ φ ↦ u i0 ])
        → Path A (outS u0) (primHComp (λ { j (φ = i1) → u j IsOne-i1 }) (outS u0))
  hfill {φ = φ} u u0 i =
    primHComp (λ j → λ { (φ = i1) → u (i ∧ j) IsOne-i1
                   ; (i = i0) → outS u0 })
          (outS u0)

  -- Heterogeneous filling defined using comp
  fill : {ℓ : Level} (A : ∀ i → Type ℓ) {φ : I}
           (u : ∀ i → Partial φ (A i))
           (u0 : A i0 [ φ ↦ u i0 ]) →
            (i : I) →  A i
  fill A {φ = φ} u u0 i =
    comp (λ j → A (i ∧ j))
         (λ j → λ { (φ = i1) → u (i ∧ j) IsOne-i1
                  ; (i = i0) → outS u0 })
         (outS {φ = φ} u0)

transpProof : {ℓ : Level} → (e : I → Type ℓ) → (φ : I) → (a : Partial φ (e i0)) → (b : e i1 [ φ ↦ (λ o → transport-fixing (λ i → e i) i0 (a o)) ] ) → flippedFiber (transport-fixing (λ i → e i) i0) (outS b)
transpProof e φ a b = f , λ j → comp (λ i → e i) (λ i →
                                               λ { (φ = i1) → transport-fixing (λ j → e (j ∧ i)) (~ i) (a IsOne-i1)
                                                 ; (j = i0) → transport-fixing (λ j → e (j ∧ i)) (~ i) f
                                                 ; (j = i1) → g (~ i) })
                                        f
    where
      b' = outS {u = (λ o → transport-fixing (λ i → e i) i0 (a o))} b
      g : (k : I) → e (~ k)
      g k = fill (λ i → e (~ i)) (λ i → λ { (φ = i1) → transport-fixing (λ j → e (j ∧ ~ i)) i (a IsOne-i1)
                                          ; (φ = i0) → transport-fixing (λ j → e (~ j ∨ ~ i)) (~ i) b' }) (inS b') k
      f = comp (λ i → e (~ i)) (λ i → λ { (φ = i1) → transport-fixing (λ j → e (j ∧ ~ i)) i (a IsOne-i1); (φ = i0) → transport-fixing (λ j → e (~ j ∨ ~ i)) (~ i) b' }) b'

{-# BUILTIN TRANSPPROOF transpProof #-}

module GluePrimitives where
  primitive
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
                 {A : Type ℓ [ φ ↦ T i0 ]} →
                 PartialP φ (T i1) → outS A → primHComp T (outS A)

    prim^unglueU : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
                   {A : Type ℓ [ φ ↦ T i0 ]} →
                   primHComp T (outS A) → outS A

    primFaceForall : (I → I) → I

open GluePrimitives public renaming (prim^glue to glue)

-- Uncurry `Glue` to make it more pleasant to use
Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

-- Unfortunately we can't do the same for prim^glue without involving
-- cubical subtypes (which we are trying to avoid)

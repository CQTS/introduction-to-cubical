module Library.Univalence where

open import Library.Prelude
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
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
      g = fst (fst isI)
      s : isSection f g
      s = snd (fst isI)
      g' = fst (snd isI)
      t : isSection g' f
      t = snd (snd isI)

      module _ (y : A) (x0 x1 : B) (p0 : y ≡ g x0) (p1 : y ≡ g x1) where
        fill0 : Square (cong f p0) (cong f p0 ∙ s x0) refl (s x0)
        fill0 = ∙-filler (cong f p0) (s x0)

        fill1 : Square (cong f p1) (cong f p1 ∙ s x1) refl (s x1)
        fill1 = ∙-filler (cong f p1) (s x1)

        fill2 : Square refl (sym (fill0 i1) ∙∙ refl ∙∙ (fill1 i1)) (fill0 i1) (fill1 i1)
        fill2 = ∙∙-filler (sym (fill0 i1)) refl (fill1 i1)

        p : x0 ≡ x1
        p = fill2 i1

        sq : Square refl (cong (f ∘ g) p) (cong f p0) (cong f p1)
        sq i j = hcomp (λ k → λ { (i = i0) → f y
                                ; (i = i1) → s (p j) (~ k)
                                ; (j = i0) → fill0 (~ k) i
                                ; (j = i1) → fill1 (~ k) i })
                       (fill2 i j)

        sq1 : Square refl (cong g p) p0 p1
        sq1 i j = hcomp (λ k → λ { (i = i0) → t y k
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
    isEquiv→secIsBijection y = isProp→with-point-isContr (λ (x0 , p0) (x1 , p1) → lemEquiv y x0 x1 p0 p1) (f y , sym (t y) ∙ sym (sec≡ret (f , isI) (f y)))

  Equiv→Bijection : A ≃ B → Σ[ f ∈ (A → B) ] isBijection f
  Equiv→Bijection (f , isE) = (f , isEquiv→secIsBijection (snd (invEquiv (f , isE))))

equivProof : ∀ {la lt} (T : Type la) (A : Type lt) → (w : T ≃ A) → (a : A)
           → ∀ ψ (f : Partial ψ (flippedFiber (w .fst) a)) → flippedFiber (w .fst) a [ ψ ↦ f ]
equivProof A B v a ψ fb =
  inS (contr' {A = flippedFiber (w .fst) a} (flippedFiber-isContr (w .snd a)) ψ fb)
  where
    w = Equiv→Bijection v
    contr' : ∀ {ℓ} {A : Type ℓ} → isContr A → (φ : I) → (u : Partial φ A) → A
    contr' {A = A} (c , p) φ u = hcomp (λ i → λ { (φ = i1) → p (u 1=1) i
                                                ; (φ = i0) → c }) c

{-# BUILTIN EQUIV      _≃_        #-}
{-# BUILTIN EQUIVFUN   equivFun   #-}
{-# BUILTIN EQUIVPROOF equivProof #-}

module GluePrimitives where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
      → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Type ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
      → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → (t : PartialP φ T) → (a : A) → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
      → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A

    prim^glueU : {la : Level} {φ : I} {T : I → Partial φ (Type la)}
                 {A : Type la [ φ ↦ T i0 ]} →
                 PartialP φ (T i1) → outS A → hcomp T (outS A)
    prim^unglueU : {la : Level} {φ : I} {T : I → Partial φ (Type la)}
                   {A : Type la [ φ ↦ T i0 ]} →
                   hcomp T (outS A) → outS A

    primFaceForall : (I → I) → I

open GluePrimitives renaming (prim^glue to glue)

-- Uncurry Glue to make it more pleasant to use
Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

-- Make the φ argument of prim^unglue explicit
unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

-- Homogeneous filling
hfill : {ℓ : Level} {A : Type ℓ} {φ : I}
      → (u : (i : I) → Partial φ A)
      → (u0 : A [ φ ↦ u i0 ])
      → Path A (outS u0) (hcomp (λ { j (φ = i1) → u j 1=1 }) (outS u0))
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- Heterogeneous filling defined using comp
fill : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i0 [ φ ↦ u i0 ]) →
          (i : I) →  A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0 })
       (outS {φ = φ} u0)

transpProof : {ℓ : Level} → (e : I → Type ℓ) → (φ : I) → (a : Partial φ (e i0)) → (b : e i1 [ φ ↦ (λ o → transp (λ i → e i) i0 (a o)) ] ) → flippedFiber (transp (λ i → e i) i0) (outS b)
transpProof e φ a b = f , λ j → comp (λ i → e i) (λ i →
                                               λ { (φ = i1) → transp (λ j → e (j ∧ i)) (~ i) (a 1=1)
                                                 ; (j = i0) → transp (λ j → e (j ∧ i)) (~ i) f
                                                 ; (j = i1) → g (~ i) })
                                        f
    where
      b' = outS {u = (λ o → transp (λ i → e i) i0 (a o))} b
      g : (k : I) → e (~ k)
      g k = fill (λ i → e (~ i)) (λ i → λ { (φ = i1) → transp (λ j → e (j ∧ ~ i)) i (a 1=1)
                                          ; (φ = i0) → transp (λ j → e (~ j ∨ ~ i)) (~ i) b' }) (inS b') k
      f = comp (λ i → e (~ i)) (λ i → λ { (φ = i1) → transp (λ j → e (j ∧ ~ i)) i (a 1=1); (φ = i0) → transp (λ j → e (~ j ∨ ~ i)) (~ i) b' }) b'

{-# BUILTIN TRANSPPROOF transpProof #-}

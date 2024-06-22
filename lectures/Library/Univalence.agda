module Library.Univalence where

open import Library.Prelude
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-6--Propositions
open import 2--Paths-and-Identifications.2-8--Equivalences

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

flippedFiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
flippedFiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)

flippedFiber-isContr : {A : Type ℓ} {B : Type ℓ'} {f : A → B} {b : B} → isContr (fiber f b) → isContr (flippedFiber f b)
flippedFiber-isContr ((a , p) , h) .fst = a , sym p
flippedFiber-isContr ((a , p) , h) .snd (a₂ , p₂) i .fst = fst (h (a₂ , sym p₂) i)
flippedFiber-isContr ((a , p) , h) .snd (a₂ , p₂) i .snd = sym (snd (h (a₂ , sym p₂) i))

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

transpProof : ∀ {l} → (e : I → Type l) → (φ : I) → (a : Partial φ (e i0)) → (b : e i1 [ φ ↦ (\ o → transp (\ i → e i) i0 (a o)) ] ) → flippedFiber (transp (\ i → e i) i0) (outS b)
transpProof e φ a b = f , \ j → comp (\ i → e i) (\ i →
                                               \ { (φ = i1) → transp (\ j → e (j ∧ i)) (~ i) (a 1=1)
                                                 ; (j = i0) → transp (\ j → e (j ∧ i)) (~ i) f
                                                 ; (j = i1) → g (~ i) })
                                        f
    where
      b' = outS {u = (\ o → transp (\ i → e i) i0 (a o))} b
      g : (k : I) → e (~ k)
      g k = fill (\ i → e (~ i)) (\ i → \ { (φ = i1) → transp (\ j → e (j ∧ ~ i)) i (a 1=1)
                                          ; (φ = i0) → transp (\ j → e (~ j ∨ ~ i)) (~ i) b' }) (inS b') k
      f = comp (\ i → e (~ i)) (\ i → \ { (φ = i1) → transp (\ j → e (j ∧ ~ i)) i (a 1=1); (φ = i0) → transp (\ j → e (~ j ∨ ~ i)) (~ i) b' }) b'

{-# BUILTIN TRANSPPROOF transpProof #-}

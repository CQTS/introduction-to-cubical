module homework.Library.Univalence where

open import homework.Library.Prelude
open import homework.1--Type-Theory.1-2--Inductive-Types
open import homework.2--Paths-and-Identifications.2-1--Paths
open import homework.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework.2--Paths-and-Identifications.2-3--Uniqueness-and-Equivalence
open import homework.2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

-- Improved version of equivProof compared to Lemma 5 in CCHM. We put
-- the (φ = i0) face in contr' making it be definitionally c in this
-- case. This makes the computational behavior better, in particular
-- for transp in Glue.
equivProof : ∀ {la lt} (T : Type la) (A : Type lt) → (w : T ≃ A) → (a : A)
           → ∀ ψ (f : Partial ψ (fiber (w .fst) a)) → fiber (w .fst) a [ ψ ↦ f ]
equivProof A B w a ψ fb =
  inS (contr' {A = fiber (w .fst) a} (w .snd a) ψ fb)
  where
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

isoToPath : Iso A B → A ≡ B
isoToPath {A = A} {B = B} f i =
  Glue B (λ { (i = i0) → (A , isoToEquiv f)
            ; (i = i1) → (B , idEquiv B) })

transpProof : ∀ {l} → (e : I → Type l) → (φ : I) → (a : Partial φ (e i0)) → (b : e i1 [ φ ↦ (\ o → transp (\ i → e i) i0 (a o)) ] ) → fiber (transp (\ i → e i) i0) (outS b)
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

```
module 2--Paths-and-Identifications.2-8E--Embeddings-and-Surjections where
```

# Lecture 2-8E: Embeddings and Surjections

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Propositions
open import 2--Paths-and-Identifications.2-7--Sets
open import 2--Paths-and-Identifications.2-8--Equivalences

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
    f : A → B
```
-->

https://1lab.dev/1Lab.Function.Embedding.html#2632


## Embeddings

Also mention that suc, inl, inr, etc are injective.

```
isInjective : (A → B) → Type _
isInjective f = ∀ {x y} → f x ≡ f y → x ≡ y

isFaithful : (A → B) → Type _
isFaithful f = ∀ x y → isEquiv {A = x ≡ y} (cong f)

isEmbedding : (A → B) → Type _
isEmbedding f = ∀ x → isProp (fiber f x)

isPropIsFaithful : {f : A → B} → isProp (isFaithful f)
isPropIsFaithful {f = f} = isPropΠ λ _ → isPropΠ λ _ → isPropIsEquiv (cong f)

isInjective→isEmbedding
  : isSet B → (f : A → B) → isInjective f
  → isEmbedding f
isInjective→isEmbedding bset f inj x (f*x , p) (f*x' , q) =
  equivFun (≡InSubtype (∀isProp→isPred (λ a → bset x (f a))) (f*x , p) (f*x' , q)) (inj (sym p ∙ q))

-- isEquiv→isEmbedding : isEquiv f → isEmbedding f
-- isEquiv→isEmbedding e x = isContr→isProp (e x)

-- isFaithful→isInjective
--   : {f : A → B}
--   → isFaithful f
--   → isInjective f
-- isFaithful→isInjective emb p = emb _ _ p .fst .fst

-- -- mvrnote todo
-- private
--   lemma₀ : ∀ {y z}(p : y ≡ z) → fiber f y ≡ fiber f z
--   lemma₀ {f = f} p = λ i → fiber f (p i)

--   lemma₁ : isFaithful f → ∀ x → isContr (fiber f (f x))
--   lemma₁ {f = f} iE x = {!!}

-- isFaithful→isEmbedding : isFaithful f → isEmbedding f
-- isFaithful→isEmbedding iE y (x , p)
--   = subst (λ f → isProp f) (sym (lemma₀ p)) (isContr→isProp (lemma₁ iE x)) (x , p)

embedding-lemma : (∀ x → isContr (fiber f (f x))) → isEmbedding f
embedding-lemma {f = f} cffx y (x , p) q = isContr→isProp (subst isContr (cong (fiber f) (sym p)) (cffx x)) (x , p) q

-- cancellable→embedding : (∀ {x y} → (f x ≡ f y) ≃ (x ≡ y)) → isEmbedding f
-- cancellable→embedding eqv =
--   embedding-lemma λ x → isContrAcrossEquiv {!!} {!!}

-- cancellable→embedding : (∀ {x y} → (f x ≡ f y) ≃ (x ≡ y)) → is-embedding f
-- cancellable→embedding eqv =
--   embedding-lemma λ x → Equiv→is-hlevel 0 (Σ-ap-snd (λ _ → eqv)) $
--     contr (x , refl) λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

-- embedding→cancellable : is-embedding f → ∀ {x y} → is-equiv {B = f x ≡ f y} (ap f)
-- embedding→cancellable emb = total→equiv {f = λ y p → ap f {y = y} p}
--   (is-contr→is-equiv
--     (contr (_ , refl) λ (y , p) i → p i , λ j → p (i ∧ j))
--     (contr (_ , refl) (Equiv→is-hlevel 1 (Σ-ap-snd λ _ → sym-equiv) (emb _) _)))

--   equiv→cancellable : is-equiv f → ∀ {x y} → is-equiv {B = f x ≡ f y} (ap f)
--   equiv→cancellable eqv = embedding→cancellable (is-equiv→is-embedding eqv)
```



## Surjections

```
isSurjection : (A → B) → Type _
isSurjection f = ∀ b → ∃ fiber f b 

section→isSurjection : {f : A → B} {g : B → A} → isSection f g → isSurjection f
section→isSurjection {g = g} s b = ∣ g b , sym (s b) ∣

-- isEquiv→isEmbedding×isSurjection : isEquiv f → isEmbedding f × isSurjection f
-- isEquiv→isEmbedding×isSurjection e = isEquiv→isEmbedding e , isEquiv→isSurjection e

-- isEmbedding×isSurjection→isEquiv : isEmbedding f × isSurjection f → isEquiv f
-- equiv-proof (isEmbedding×isSurjection→isEquiv {f = f} (emb , sur)) b =
--   inhProp→isContr (PT.rec fib' (λ x → x) fib) fib'
--   where
--   hpf : hasPropFibers f
--   hpf = isEmbedding→hasPropFibers emb

--   fib : ∥ fiber f b ∥₁
--   fib = sur b

--   fib' : isProp (fiber f b)
--   fib' = hpf b

```

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
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
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

mvrnote: need to settle on names

https://1lab.dev/1Lab.Function.Embedding.html#2632


## Injections, Faithful maps, and Embeddings

In set-based mathematics, a function $f : A → B$ is injective when $f(x) = f(y)$ implies that $x = y$.
We can import this definition verbatim into Cubical Agda

```
isInjective : (A → B) → Type _
isInjective f = ∀ {x y} → f x ≡ f y → x ≡ y
```

This is a reasonable definition for sets, but for general types, there
is no reason for `isInjective f` to be a proposition. In fact, though
we don't have quite the tools to show it yet, the identity function `λ
x → x : S¹ → S¹` of the circle has two distinct witnesses to
`isInjective (λ (x : S¹) → x)`.

An equivalent way to say that a function $f$ is injective is to say
that $x = y$ if and only if $f(x) = f(y)$. We can use interpret this
definition in Cubical Agda as saying that `cong f : x ≡ y → f x ≡ f y`
is an equivalence.

```
-- already declared in 2.6
-- isFaithful : (A → B) → Type _
-- isFaithful f = ∀ x y → isEquiv {A = x ≡ y} (cong f)
```

Being faithful is evidently a proposition.

```
isPropIsFaithful : {f : A → B} → isProp (isFaithful f)
-- Exercise:
isPropIsFaithful {f = f} = {! !}
```

Of course, being faithful implies being injective
```
isFaithful→isInjective
   : {f : A → B}
   → isFaithful f
   → isInjective f
-- Exercise:
isFaithful→isInjective faithful {x} {y} = {!!}
```

The other direction is not true in general, but when `A` and `B` are sets
we can show that `f` is faithful when it is injective.

```
isInjective-isFaithful :
     isSet A
  →  isSet B 
  → (f : A → B)
  → isInjective f
  → isFaithful f
-- Exercise: 
isInjective-isFaithful aset bset f inj x y = {! !}
```

There is one more way we can express the concept of injectivity. Remember that a map `f` is an equivalence if and only if it has contractible fibers --- that is, if each fiber has exactly one element.
We can give a similar sort of definition for injectivity: a map is injective if and only if every fiber has at most one element --- in other words, if the fibers are propositions.

```
isEmbedding : (A → B) → Type _
isEmbedding f = ∀ x → isProp (fiber f x)
```

Like being faithful, being an embedding is a proposition.

```
isProp-isEmbedding : (f : A → B) → isProp (isEmbedding f)
isProp-isEmbedding f = isPropΠ λ x → isPropIsProp
```

Unlike the case for injectivity, we will see that `f` is an embedding if and only if it is faithful. First, we begin by showing that if `f` is faithful, it is an embedding.

```
-- djnote: we need to prove this lemma somewhere else so we can use it here.
compPathLeftEquiv : {x y : A} (p : x ≡ y) → ∀ {z} → (y ≡ z) ≃ (x ≡ z)
compPathLeftEquiv p = equiv (p ∙_) (sym p ∙_) to-fro fro-to
  where
    to-fro : isSection (p ∙_) (sym p ∙_)
    to-fro q = {!!}

    fro-to : isRetract (p ∙_) (sym p ∙_)
    fro-to q = {!!}

isFaithful-isEmbedding : (f : A → B)
  → isFaithful f
  → isEmbedding f
isFaithful-isEmbedding f faith b = with-point-isContr→isProp λ z → isContrEquiv (lemma z) (isContrSingl (fst z))
  where
    lemma : (z : fiber f b) → fiber f b ≃ singl (fst z)
    lemma (x , p) = compEquiv
      (invEquiv (Σ-map-snd-≃ (λ y → (cong f , faith x y))))
      (invEquiv (Σ-map-snd-≃ (λ y → compPathLeftEquiv p)))
```

```
-- isInjective→isEmbedding
--  : isSet B → (f : A → B) → isInjective f
--  → isEmbedding f
-- isInjective→isEmbedding bset f inj x (f*x , p) (f*x' , q) =
--  equivFun (≡InSubtype (∀isProp→isPred (λ a → bset x (f a))) (f*x , p) (f*x' , q)) (inj (sym p ∙ q))

-- isEquiv→isEmbedding : isEquiv f → isEmbedding f
-- isEquiv→isEmbedding e x = isContr→isProp (e x)

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

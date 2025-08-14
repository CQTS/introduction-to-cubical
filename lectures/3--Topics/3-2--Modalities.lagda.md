<!--
```
module 3--Topics.3-2--Modalities where

-- mvrnote: check redundant imports/variables
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types
open import 2--Paths-and-Identifications.2-9--Contractible-Maps

open import 3--Topics.Lemmas

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B : A → Type ℓ
```
-->


# Lecture 3-2: Modalities

(Monadic) modalities

```
record Subuniverse (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor subuniverseData
  field
    predicate : Type ℓ → Type ℓ
    isProp-predicate : (X : Type ℓ) → isProp (predicate X)
open Subuniverse

record Type-in (S : Subuniverse ℓ) : Type (ℓ-suc ℓ) where
  constructor type-in
  field
    type : Type ℓ
    proof : S .predicate type
open Type-in
```

```
Contr-Subuniverse : Subuniverse ℓ
Contr-Subuniverse .predicate X = isContr X
Contr-Subuniverse .isProp-predicate X = isProp-isContr

Prop-Subuniverse : Subuniverse ℓ
Prop-Subuniverse .predicate X = isProp X
Prop-Subuniverse .isProp-predicate X = isProp-isProp

Set-Subuniverse : Subuniverse ℓ
Set-Subuniverse .predicate X = isSet X
Set-Subuniverse .isProp-predicate X = isProp-isSet

isProp-Lift : isProp A → isProp (Lift ℓ A)
isProp-Lift pA (lift x) (lift y) = ap lift (pA x y)

Everything-Subuniverse : Subuniverse ℓ
Everything-Subuniverse .predicate X = Lift _ ⊤
Everything-Subuniverse .isProp-predicate X = isProp-Lift isProp-⊤

Nothing-Subuniverse : Subuniverse ℓ
Nothing-Subuniverse .predicate X = Lift _ ∅
Nothing-Subuniverse .isProp-predicate X = isProp-Lift isProp-∅

Inhabited-Subuniverse : Subuniverse ℓ
Inhabited-Subuniverse .predicate X = ∃ X
Inhabited-Subuniverse .isProp-predicate X = isProp-∃

Decidable-Subuniverse : Subuniverse ℓ
Decidable-Subuniverse .predicate X = ∃ (Dec X)
Decidable-Subuniverse .isProp-predicate X = isProp-∃

Contradictory-Subuniverse : Subuniverse ℓ
Contradictory-Subuniverse .predicate X = ¬ X
Contradictory-Subuniverse .isProp-predicate X = isProp-¬

Stable-Subuniverse : Subuniverse ℓ
Stable-Subuniverse .predicate X = isProp X × (¬ ¬ X → X)
Stable-Subuniverse .isProp-predicate X x y = isProp-× isProp-isProp (isProp-→ (x .fst)) x y

-- mvrnote: other examples? (even silly ones)
```

```
record Prop (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor propData
  field
    witness : Type ℓ
    isProp-witness : isProp witness
open Prop public

Prop≃Prop-Subuniverse : Prop ℓ ≃ Type-in {ℓ} Prop-Subuniverse
Prop≃Prop-Subuniverse .map P .type = P .witness
Prop≃Prop-Subuniverse .map P .proof = P .isProp-witness
Prop≃Prop-Subuniverse .proof .section .map T .witness = T .type
Prop≃Prop-Subuniverse .proof .section .map T .isProp-witness = T .proof
Prop≃Prop-Subuniverse .proof .section .proof b = refl
Prop≃Prop-Subuniverse .proof .retract .map T .witness = T .type
Prop≃Prop-Subuniverse .proof .retract .map T .isProp-witness = T .proof
Prop≃Prop-Subuniverse .proof .retract .proof b = refl
```

::: Caution:
There are two very similar unicode symbols `\cw`: ○ and `\bigcirc`: ◯,
I'm using the former because it's shorter to type.
:::

```
record Modality (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor modality
  field
    isModal : Type ℓ → Type ℓ
    isProp-isModal : (X : Type ℓ) → isProp (isModal X)

    ○ : Type ℓ → Type ℓ
    isModal-○ : (X : Type ℓ) → isModal (○ X)

    η   : (X : Type ℓ) → (X → ○ X)
    ump : (X : Type ℓ) 
        → ((P : ○ X → Type-in (subuniverseData isModal isProp-isModal))
        → isEquiv λ (f : (z : ○ X) → P z .type) → f ∘ η X)
open Modality

Modal-Subuniverse : Modality ℓ → Subuniverse ℓ
Modal-Subuniverse M .predicate = M .isModal
Modal-Subuniverse M .isProp-predicate = M .isProp-isModal

Identity-Modality : Modality ℓ-zero
Identity-Modality .isModal = Everything-Subuniverse .predicate
Identity-Modality .isProp-isModal = Everything-Subuniverse .isProp-predicate
Identity-Modality .○ X = X
Identity-Modality .isModal-○ X = lift tt
Identity-Modality .η X = idfun
Identity-Modality .ump X P = isEquiv-idfun

Contr-Modality : Modality ℓ-zero
Contr-Modality .isModal = Contr-Subuniverse .predicate
Contr-Modality .isProp-isModal = Contr-Subuniverse .isProp-predicate
Contr-Modality .○ X = ⊤
Contr-Modality .isModal-○ X = isContr-⊤
Contr-Modality .η X x = tt
Contr-Modality .ump X P = contrEnds→isEquiv (isContr-Π (λ a → P a .proof)) (isContr-Π (λ a → P tt .proof)) (λ g a → g tt)

Prop-Modality : Modality ℓ
Prop-Modality .isModal = Prop-Subuniverse .predicate
Prop-Modality .isProp-isModal = Prop-Subuniverse .isProp-predicate
Prop-Modality .○ X = ∃ X
Prop-Modality .isModal-○ X = isProp-∃
Prop-Modality .η X = in-∃
Prop-Modality .ump X P = invEquiv (∃-ump-≃ λ e → P e .proof) .proof -- mvrnote: this invEquiv is annoying, can we switch the original?

Stable-Modality : Modality ℓ
Stable-Modality .isModal = Stable-Subuniverse .predicate
Stable-Modality .isProp-isModal = Stable-Subuniverse .isProp-predicate
Stable-Modality .○ X = ¬ ¬ X
Stable-Modality .isModal-○ X = isProp-¬ , λ nnnx nx → nnnx (λ nnx → nnx nx)
Stable-Modality .η X a f = f a
Stable-Modality .ump X P = packIsEquiv to isSec to isRet
  where
    ¬¬-func : {P : Type ℓ} {Q : Type ℓ} → (P → Q) → ((¬ ¬ P) → (¬ ¬ Q))
    ¬¬-func f nnp nq = nnp (λ p → nq (f p))

    to : ((a : X) → P (λ f → f a) .type) → (z : ¬ (¬ X)) → P z .type
    to f z = P z .proof .snd (¬¬-func (λ x → subst (type ∘ P) (isProp-¬ (λ f → f x) z) (f x)) z)

    isSec : isSection (λ f → f ∘ (λ a f₁ → f₁ a)) to
    isSec b = isProp-Π (λ _ → P _ .proof .fst) _ _

    isRet : isRetract (λ f → f ∘ (λ a f₁ → f₁ a)) to
    isRet b = isProp-Π (λ _ → P _ .proof .fst) _ _
```



mvrnote the universal property excludes dumb examples, e.g. a reflector into Set that is constant


## The Open and Closed Modalities

```
-- mvrnote: move later?
Open-Subuniverse : Prop ℓ → Subuniverse ℓ
Open-Subuniverse Q .predicate X = isEquiv constX
  where constX : X → (Q .witness → X)
        constX x _ = x
Open-Subuniverse Q .isProp-predicate X = isProp-isEquiv _

Open-Modality : Prop ℓ → Modality ℓ
Open-Modality Q .isModal = Open-Subuniverse Q .predicate
Open-Modality Q .isProp-isModal = Open-Subuniverse Q .isProp-predicate
Open-Modality Q .○ X = Q .witness → X
Open-Modality Q .isModal-○ X = iseq
  where
    iseq : isEquiv (λ (x : Q .witness → X) (q : Q .witness) → x)
    iseq .section .map f q = f q q
    iseq .section .proof f i q q' = f (Q .isProp-witness q' q i) q'
    iseq .retract .map f q = f q q
    iseq .retract .proof b = refl
Open-Modality Q .η X = const
Open-Modality Q .ump X P = ○-ump P
  where
    ○-ump-for-○P : (P : Open-Modality Q .○ X → Type _) → isEquiv λ (f : (z : Open-Modality Q .○ X) → Open-Modality Q .○ (P z)) → f ∘ const
    ○-ump-for-○P P .section .map g z q = subst P (λ i q' → z (Q .isProp-witness q q' i)) (g (z q) q)
    ○-ump-for-○P P .section .proof g i x q = transport-refl (g x q) i
    ○-ump-for-○P P .retract .map = ○-ump-for-○P P .section .map
    ○-ump-for-○P P .retract .proof f i z q = fromPathP (λ j → f (λ q' → z (Q .isProp-witness q q' j)) q) i

    ○-ump-path : (P : Open-Modality Q .○ X → Type-in (Open-Subuniverse Q)) → Path (Open-Modality Q .○ X → Type _) (λ z → Open-Modality Q .○ (P z .type)) (λ z → P z .type)
    ○-ump-path P i z = ua (equiv _ (P z .proof)) (~ i)

    ○-ump : (P : Open-Modality Q .○ X → Type-in (Open-Subuniverse Q)) → isEquiv λ (f : (z : Open-Modality Q .○ X) → P z .type) → f ∘ const
    ○-ump P = subst (λ P' → isEquiv (λ (f : (z : Open-Modality Q .○ X) → P' z) → f ∘ const)) (○-ump-path P) (○-ump-for-○P (λ z → P z .type))
```

mvrnote: lemmas
```
×-fst-≃ : {A : Type ℓ} → {B : Type ℓ'} → isContr B → A × B ≃ A
-- Exercise:
×-fst-≃ c = {!!}

×-snd-≃ : {A : Type ℓ} → {B : Type ℓ'} → isContr A → A × B ≃ B
-- Exercise:
×-snd-≃ c = {!!}
```

```
Closed-Subuniverse : Prop ℓ → Subuniverse ℓ
Closed-Subuniverse Q .predicate X = Q .witness → isContr X
Closed-Subuniverse Q .isProp-predicate X = isProp-→ isProp-isContr

data Join (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → Join A B
  inr : B → Join A B
  push : (a : A) → (b : B) → inl a ≡ inr b

Join-ump-≃ : {A : Type ℓ} {B : Type ℓ'} {C : Join A B → Type ℓ}
  → ((ab : Join A B) → C ab)
  ≃ (Σ[ f ∈ ((a : A) → C (inl a)) ] Σ[ g ∈ ((b : B) → C (inr b)) ] ((a : A) → (b : B) → PathP (λ i → C (push a b i)) (f a) (g b)))
Join-ump-≃ {A = A} {B} {C} = inv→equiv to fro to-fro fro-to
  where
    to : ((ab : Join A B) → C ab) → (Σ[ f ∈ ((a : A) → C (inl a)) ] Σ[ g ∈ ((b : B) → C (inr b)) ] ((a : A) → (b : B) → PathP (λ i → C (push a b i)) (f a) (g b)))
    to f = f ∘ inl , f ∘ inr , λ a b → ap f (push a b)
    fro : (Σ[ f ∈ ((a : A) → C (inl a)) ] Σ[ g ∈ ((b : B) → C (inr b)) ] ((a : A) → (b : B) → PathP (λ i → C (push a b i)) (f a) (g b))) → ((ab : Join A B) → C ab)
    fro (f , g , p) (inl a) = f a
    fro (f , g , p) (inr b) = g b
    fro (f , g , p) (push a b i) = p a b i
    to-fro : isSection to fro
    to-fro b = refl
    fro-to : isRetract to fro
    fro-to f i (inl a) = f (inl a)
    fro-to f i (inr b) = f (inr b)
    fro-to f i (push a b j) = f (push a b j)

isContr-Join : {A B : Type ℓ} → isContr A → isContr (Join A B)
isContr-Join cA .center = inl (cA .center)
isContr-Join cA .contraction (inl a) = ap inl (cA .contraction a)
isContr-Join cA .contraction (inr b) = push (cA .center) b
isContr-Join cA .contraction (push a b i) j
  = J (λ y p → Square (ap inl p) (push (cA .center) b) refl (push y b))
      (λ i j → push (cA .center) b (i ∧ j))
      (cA .contraction a) i j

∅-Join : {B : Type ℓ} → (Join ∅ B) ≃ B
∅-Join .map (inl ())
∅-Join .map (inr b) = b
∅-Join .map (push () b i)
∅-Join .proof .section .map = inr
∅-Join .proof .section .proof b = refl
∅-Join .proof .retract .map = inr
∅-Join .proof .retract .proof (inl ())
∅-Join .proof .retract .proof (inr b) = refl
∅-Join .proof .retract .proof (push () b i)

Closed-Modality : Prop ℓ → Modality ℓ
Closed-Modality Q .isModal = Closed-Subuniverse Q .predicate
Closed-Modality Q .isProp-isModal = Closed-Subuniverse Q .isProp-predicate
Closed-Modality Q .○ X = Join (Q .witness) X
Closed-Modality Q .isModal-○ X q = isContr-Join (isProp-with-point→isContr (Q .isProp-witness) q)
Closed-Modality Q .η X = inr
Closed-Modality Q .ump X P = ○-ump P
  where
    ○-eq : (P : Closed-Modality Q .○ X → Type-in (Closed-Subuniverse Q)) →
      ((z : Closed-Modality Q .○ X) → P z .type) ≃ ((x : X) → P (inr x) .type)
    ○-eq P =
      ((z : Closed-Modality Q .○ X) → P z .type)
        ≃⟨ Join-ump-≃ ⟩
      Σ[ f ∈ ((q : Q .witness) → P (inl q) .type) ]
      Σ[ g ∈ ((x : X) → P (inr x) .type) ]
      ((q : Q .witness) (x : X) → PathP (λ i → P (push q x i) .type) (f q) (g x))
        ≃⟨ Σ-map-snd-≃ (λ f → Σ-fst-≃ λ g → isContr-Π (λ q → isContr-Π (λ x → isContr→isContr-PathP (P (inr x) .proof q) _ _))) ⟩
      ((q : Q .witness) → P (inl q) .type) × ((x : X) → P (inr x) .type)
        ≃⟨ ×-snd-≃ (isContr-Π (λ q → P (inl q) .proof q)) ⟩
      ((x : X) → P (inr x) .type)
        ∎e

    ○-ump : (P : Closed-Modality Q .○ X → Type-in (Closed-Subuniverse Q)) → isEquiv λ (f : (z : Closed-Modality Q .○ X) → P z .type) → f ∘ inr
    ○-ump P = ○-eq P .proof
```


## Generalities

```
record IsReflection (S : Subuniverse ℓ) (X : Type ℓ) (R : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor isReflection
  field
    isModal : S .predicate R
    η : X → R
    ump : ((P : R → Type-in S) → isEquiv λ (f : (z : R) → P z .type) → f ∘ η)
open IsReflection

Modal-Reflection : (M : Modality ℓ) → (X : Type ℓ) → IsReflection (Modal-Subuniverse M) X (M .○ X)
Modal-Reflection M X .isModal = M .isModal-○ X
Modal-Reflection M X .η = M .η X
Modal-Reflection M X .ump = M .ump X

isProp-Reflection : (S : Subuniverse ℓ) → (X : Type ℓ) → isProp (Σ[ R ∈ Type ℓ ] IsReflection S X R)
isProp-Reflection S X (R₀ , isReflection isModal₀ η₀ ump₀) (R₁ , isReflection isModal₁ η₁ ump₁) i 
  = R₀≡R₁ i , isReflection (isModal≡isModal₁ i) (η≡η₁ i) (ump₀≡ump₁ i)
  where
        ∘-η₀-≃₀ : (R₀ → R₀) ≃ (X → R₀)
        ∘-η₀-≃₀ = equiv (λ f → f ∘ η₀) (ump₀ (λ _ → type-in R₀ isModal₀))

        ∘-η₀-≃₁ : (R₀ → R₁) ≃ (X → R₁)
        ∘-η₀-≃₁ = equiv (λ f → f ∘ η₀) (ump₀ (λ _ → type-in R₁ isModal₁))

        ∘-η₁-≃₀ : (R₁ → R₀) ≃ (X → R₀)
        ∘-η₁-≃₀ = equiv (λ f → f ∘ η₁) (ump₁ (λ _ → type-in R₀ isModal₀))

        ∘-η₁-≃₁ : (R₁ → R₁) ≃ (X → R₁)
        ∘-η₁-≃₁ = equiv (λ f → f ∘ η₁) (ump₁ (λ _ → type-in R₁ isModal₁))

        to : R₀ → R₁
        to = ∘-η₀-≃₁ .proof .section .map η₁

        to-η : to ∘ η₀ ≡ η₁
        to-η = ∘-η₀-≃₁ .proof .section .proof η₁

        fro : R₁ → R₀
        fro = ∘-η₁-≃₀ .proof .section .map η₀

        fro-η : fro ∘ η₁ ≡ η₀
        fro-η = ∘-η₁-≃₀ .proof .section .proof η₀

        to-fro-η₁ : to ∘ fro ∘ η₁ ≡ η₁
        to-fro-η₁ =
          to ∘ fro ∘ η₁ ≡⟨ ap (to ∘_) fro-η ⟩
          to ∘ η₀       ≡⟨ to-η ⟩
          η₁            ∎

        to-fro : isSection to fro
        to-fro = funext⁻ (ap-≃ ∘-η₁-≃₁ .proof .section .map to-fro-η₁) 

        fro-to-η : fro ∘ to ∘ η₀ ≡ η₀
        fro-to-η =
          fro ∘ to ∘ η₀ ≡⟨ ap (fro ∘_) to-η ⟩
          fro ∘ η₁      ≡⟨ fro-η ⟩
          η₀            ∎

        fro-to : isRetract to fro
        fro-to = funext⁻ (ap-≃ ∘-η₀-≃₀ .proof .section .map fro-to-η)

        R₀≃R₁ : R₀ ≃ R₁
        R₀≃R₁ = inv→equiv to fro to-fro fro-to

        R₀≡R₁ : R₀ ≡ R₁
        R₀≡R₁ = ua R₀≃R₁

        isModal≡isModal₁ : PathP (λ i → S .predicate (R₀≡R₁ i)) isModal₀ isModal₁
        isModal≡isModal₁ = isProp→any-PathP (λ j → S .isProp-predicate (R₀≡R₁ j)) isModal₀ isModal₁

        η≡η₁ : PathP (λ i → X → R₀≡R₁ i) η₀ η₁
        η≡η₁ = funextP (λ x → Path→ua-PathP R₀≃R₁ (funext⁻ to-η x))

        ump₀≡ump₁ : PathP (λ i → (P : R₀≡R₁ i → Type-in S) → isEquiv (λ (f : (b : R₀≡R₁ i) → P b .type) → f ∘ η≡η₁ i)) ump₀ ump₁
        ump₀≡ump₁ = isProp→any-PathP (λ _ → isProp-Π λ _ → isProp-isEquiv _) ump₀ ump₁


-- todo: rename variables to use A, a instead of X, x

module _ (M : Modality ℓ) where
  ○-ump-≃ : (X : Type ℓ) → (P : M .○ X → Type-in (Modal-Subuniverse M)) → ((m : M .○ X) → P m .type) ≃ ((x : X) → P (M .η X x) .type)
  ○-ump-≃ X P = equiv (λ f → f ∘ M .η X) (M .ump X P)

  ○-ind : (B-modal : (x : M .○ A) → M .isModal (B x) )
      → ((x : A) → (B (M .η A x))) → ((x : M .○ A) → B x)
  ○-ind {A = A} {B = B} B-modal = M .ump A (λ x → type-in (B x) (B-modal x)) .section .map

  ○-ind-comp :
      (B-modal : (x : M .○ A) → M .isModal (B x))
      → (f : (x : A) → (B (M .η A x)))
      → (a : A) → ○-ind B-modal f (M .η A a) ≡ f a
  ○-ind-comp {A = A} {B = B} B-modal f a i = M .ump A (λ x → type-in (B x) (B-modal x)) .section .proof f i a

  modal-lemma' : isEquiv (M .η A) → M .isModal A
  modal-lemma' isE = subst (λ A → M .isModal A) (sym (ua (equiv (M .η _) isE))) (M .isModal-○ _)

  sectionequiv : RetractOf (M .η A) → isEquiv (M .η A)
  sectionequiv {X} (retractData g r) = packIsEquiv g s g r
    where s : isSection (M .η X) g -- surely overkill, can we extract what we need from the equiv directly?
          s b i = fst (isContr→isProp (isEquiv→isContractibleMap (M .ump X (λ _ → type-in (M .○ X) (M .isModal-○ X))) (M .η X)) ((M .η X) ∘ g , λ i a → ap (M .η X) (sym (r a)) i) (idfun , refl) i) b

  retract→isModal : RetractOf (M .η A) → M .isModal A
  retract→isModal = modal-lemma' ∘ sectionequiv

  -- Closure properties

  ⊤-isModal : M .isModal (Lift _ ⊤) -- Pity to use Lift
  ⊤-isModal = retract→isModal (retractData (λ _ → lift tt) isR)
    where isR : isRetract (M .η (Lift _ ⊤)) (λ _ → lift tt)
          isR (lift tt) = refl

  Σ-isModal : M .isModal A
            → ((a : A) → M .isModal (B a))
            → M .isModal (Σ[ a ∈ A ] B a)
  Σ-isModal {A} {B} isModalA isModalB = retract→isModal (retractData r isR)
    where
      h : M .○ (Σ[ a ∈ A ] B a) → A
      h = ○-ind (λ _ → isModalA) fst

      h-β : (x : Σ A B) → h (M .η _ x) ≡ fst x
      h-β = ○-ind-comp _ _

      k : (y : M .○ (Σ A B)) → B (h y)
      k = ○-ind (isModalB ∘ h) (λ p → subst B (sym (h-β p)) (snd p))

      k-β : (x : Σ A B) → PathP (λ i → B (h-β x i)) (k (M .η _ x)) (snd x)
      k-β = symP ∘ toPathP ∘ sym ∘ ○-ind-comp _ _

      r : M .○ (Σ[ a ∈ A ] B a) → (Σ[ a ∈ A ] B a)
      r p = h p , k p

      isR : isRetract (M .η _) r
      isR x i = h-β x i , k-β x i

  Π-isModal : {A : Type ℓ} {B : A → Type ℓ}
    → ((a : A) → M .isModal (B a))
    → M .isModal ((a : A) → B a)
  Π-isModal {A} {B} isModalB = retract→isModal (retractData r isR)
    where
      r : M .○ ((a : A) → B a) → ((a : A) → B a)
      r f a = ○-ind (λ _ → isModalB a) (λ g → g a) f

      isR : isRetract (M .η _) r
      isR f i a = ○-ind-comp (λ _ → isModalB a) (λ g → g a) f i

  ≡-isModal : M .isModal A → (x y : A) → M .isModal (x ≡ y)
  ≡-isModal {A} isModalA x y = retract→isModal (retractData r isR)
    where
      r'' : Path ((x ≡ y) → A) (const x) (const y)
      r'' i p = p i

      r' : Path (M .○ (x ≡ y) → A) (const x) (const y)
      r' = ap-≃ (○-ump-≃ (x ≡ y) (λ _ → type-in A isModalA)) .proof .section .map r''

      r : (M .○ (x ≡ y)) → x ≡ y
      r p i = r' i p

      isR' : ap (λ f → f ∘ (M .η _)) r' ≡ r''
      isR' = ap-≃ (○-ump-≃ (x ≡ y) (λ _ → type-in A isModalA)) .proof .section .proof r''

      isR : isRetract (M .η _) r
      isR t i j = isR' i j t
```

## n-Types and Truncation




## Lex Modalities

## References and Further Reading

mvrnote:
RSS
CORS https://arxiv.org/abs/1807.04155
Cubical
agda-unimath


--   modal-lemma : M .isModal A → isEquiv (η A)
--   modal-lemma {X} isM = subst (λ r → isEquiv (r .snd .η)) (isProp-Reflection (Modal-Subuniverse M) X idfun-reflection η-reflection) isEquiv-idfun
--     where η-reflection : Σ[ R ∈ Type ℓ ] IsReflection (Modal-Subuniverse M) X R
--           η-reflection = (M .○ X , isReflection ○-isModal (η X) (○-ump X))

--           idfun-reflection : Σ[ R ∈ Type ℓ ] IsReflection (Modal-Subuniverse M) X R
--           idfun-reflection = X , (isReflection isM idfun (λ _ → isEquiv-idfun))



  -- more general, maybe not used?
  -- retractIsModal : {A B : Type ℓ} (w : isModal A)
  --     (f : A → B) (g : B → A) (r : (b : B) → f (g b) ≡ b) →
  --     isModal B
  -- retractIsModal {A} {B} w f g r = {!!}

    -- isEquivToIsModal
    --   (isoToIsEquiv (iso η η-inv inv-l inv-r))
    -- where η-inv : ○ B → B
    --       η-inv = f ∘ (○-rec w g)

    --       inv-r : (b : B) → η-inv (η b) ≡ b
    --       inv-r b = ap f (○-rec-β w g b) ∙ r b

    --       inv-l : (b : ○ B) → η (η-inv b) ≡ b
    --       inv-l = ○-elim (λ b → ○-=-isModal _ _) (λ b → ap η (inv-r b))

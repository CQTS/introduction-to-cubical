<!--
```
module 3--Topics.Lemmas where

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

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level -- mvrnote: standardise
    ℓ₁ ℓ₂ ℓ₁' ℓ₂' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
```
-->

## Lemmas: Σ-types Respect Equivalence

The second goal of this Lecture is to prove that an equivalence of the
components of a Σ-type extends to an equivalence of the entire Σ-type.

Dealing with the second component is easier and only involves
rearranging some data, so let's do that first.

The claim to prove is that if we have a "fiberwise equivalence", a map
`(f₂ : (a : A) → B a → B' a)` so that every `f₂ a` is an equivalence,
then the map `(Σ[ a ∈ A ] B a) → (Σ[ a ∈ A ] B' a)` that applies `f₂`
to each fiber is also an equivalence.

mvrnote: adjust prose

```
Σ-map-fst : {B : A' → Type ℓ}
  → (f₁ : A → A')
  → Σ[ a ∈ A ] B (f₁ a) → Σ[ a' ∈ A' ] B a'
Σ-map-fst f₁ = Σ-map f₁ (λ _ → idfun)

Σ-map-snd : {B : A → Type ℓ} {B' : A → Type ℓ'}
  → (f₂ : (a : A) → B a → B' a)
  → Σ[ a ∈ A ] B a → Σ[ a ∈ A ] B' a
Σ-map-snd f₂ = Σ-map idfun f₂
```

Dealing with the second component is easy, in fact, we could have done
it way back in Lecture 2-2.

```
Σ-map-snd-isEquiv : {B : A → Type ℓ} {B' : A → Type ℓ'}
  → {f₂ : (a : A) → B a → B' a}
  → ((a : A) → isEquiv (f₂ a))
  → isEquiv (Σ-map-snd f₂)
-- Exercise:
Σ-map-snd-isEquiv isE = {!!}

Σ-map-snd-≃ : {B : A → Type ℓ} {B' : A → Type ℓ'}
  → (e₂ : (x : A) → B x ≃ B' x)
  → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] B' a)
Σ-map-snd-≃ e₂ .map = Σ-map-snd (map ∘ e₂)
Σ-map-snd-≃ e₂ .proof = Σ-map-snd-isEquiv (proof ∘ e₂)
```

The first component is the tough one, surprisingly difficult for such
a simple statement.

Here's the key fact, and what gives us the connection to contractible
maps. You will have to use the technology from Lecture 2-5 on
``transport`` and ``transport-filler``.

```
Σ-map-fst-fib-≃ : {B : A' → Type ℓ}
  → (f₁ : A → A')
  → (t : Σ[ a' ∈ A' ] B a')
  → fiber (Σ-map-fst f₁) t ≃ fiber f₁ (t .fst)
Σ-map-fst-fib-≃ {B = B} f₁ (a' , b') = inv→equiv to fro to-fro fro-to
  where
    to : fiber (Σ-map-fst f₁) (a' , b') → fiber f₁ a'
    -- Exercise:
    to ((a , b) , p) .fst = a

    fro : fiber f₁ a' → fiber (Σ-map-fst f₁) (a' , b')
    -- Exercise:
    fro (a , p) .fst .fst = a

    to-fro : isSection to fro
    to-fro (a , p) = refl

    fro-to : isRetract to fro
    -- Exercise:
    fro-to ((a , b) , p) i .fst .fst = a
```

mvrnote: this could alternatively be done by using J everywhere

Now, we know that `fiber (Σ-map-fst f₁) t` is contractible whenever
`fiber f₁ (t .fst)` is. Use ``isContractibleMap→isEquiv`` and
``isEquiv→isContractibleMap`` to complete the proof.

```
Σ-map-fst-isEquiv : {B : A' → Type ℓ}
  → (f₁ : A → A')
  → isEquiv f₁
  → isEquiv (Σ-map-fst {B = B} f₁)
-- Exercise:
Σ-map-fst-isEquiv f₁ e = isContractibleMap→isEquiv (λ t → isContr-equiv (Σ-map-fst-fib-≃ f₁ t) (isEquiv→isContractibleMap e (t .fst)))
```

Finally, combine ``Σ-map-fst-≃`` with ``Σ-map-snd-≃`` to prove the
original result were looking for.

```
Σ-map-≃ : {B : A → Type ℓ'} {B' : A' → Type ℓ'}
        → (e₁ : A ≃ A')
        → (e₂ : (a : A) → (B a) ≃ (B' (e₁ .map a)))
        → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')
Σ-map-≃ {A = A} {A' = A'} {B = B} {B' = B'} e₁ e₂ =
  Σ[ a  ∈ A  ] B  a           ≃⟨ Σ-map-snd-≃ e₂ ⟩
  Σ[ a  ∈ A  ] B' (e₁ .map a) ≃⟨ Σ-map-fst-≃ e₁ ⟩
  Σ[ a' ∈ A' ] B' a'          ∎e
```

```
Σ-fst-≃ : {B : A → Type ℓ} → ((a : A) → isContr (B a)) → (Σ[ a ∈ A ] B a) ≃ A
Σ-fst-≃ c = inv→equiv fst (λ a → a , c a .center) (λ _ → refl) (λ (a , b) → ap (a ,_) (c a .contraction b))

isContr-singlEquiv : {A : Type ℓ} → isContr ( Σ[ T ∈ Type ℓ ] (A ≃ T) )
isContr-singlEquiv {A = A} .center = (A , idEquiv A)
isContr-singlEquiv .contraction (B , e) i .fst = ua e i
isContr-singlEquiv .contraction (B , e) i .snd .map a = Path→ua-PathP e {x = a} refl i
isContr-singlEquiv .contraction (B , e) i .snd .proof = isProp→any-PathP (λ j → isProp-isEquiv (λ a → Path→ua-PathP e refl j)) isEquiv-idfun (e .proof) i

Equiv-J : {B : Type ℓ}
  → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
  → P A (idEquiv A)
  → (e : A ≃ B)
  → P B e
Equiv-J {A = A} {B = B} P p e = subst (λ t → P (t .fst) (t .snd)) (isContr-singlEquiv .contraction (B , e)) p
```

```
ap-isEquiv : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → isEquiv (ap {x = a₁} {a₂} (e .map) )
ap-isEquiv e {a₁} {a₂} = Equiv-J (λ B e → isEquiv (ap {x = a₁} {a₂} (e .map))) isEquiv-idfun e

ap-≃ : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → (a₁ ≡ a₂) ≃ (e .map a₁ ≡ e .map a₂)
ap-≃ e .map = ap (e .map)
ap-≃ e .proof = ap-isEquiv e
```

::: Aside:
Proving this kind of result using equivalence induction has the same
drawback as applying univalence directly (for example in
``×-map-≃-again``), in that the two input types *must* lie in the same
universe.

It is usually possible to give direct proofs, but for ``ap-≃`` the
direct proof is frankly a little fiddly and annoying, so we'll be
satisfied with the version using equivalence induction. mvrnote: reference
:::

```
module _ {A : Type ℓ} {B : I → Type ℓ'}
  {f : A → B i0} {g : A → B i1}
  where
  funextP :
      ((x : A) → PathP B (f x) (g x))
    → PathP (λ i → A → B i) f g
  funextP h i x = h x i

  funextP⁻ :
      PathP (λ i → A → B i) f g
    → ((x : A) → PathP B (f x) (g x))
  funextP⁻ p x i = p i x

funextP-≃ : {A : Type ℓ} {B : I → Type ℓ'}
  → {f : A → B i0} {g : A → B i1}
  → ((x : A) → PathP B (f x) (g x))
  ≃ PathP (λ i → A → B i) f g
funextP-≃ = inv→equiv funextP funextP⁻ (λ _ → refl) (λ _ → refl)

Π-map-cod≃ : {P : A → Type ℓ} {Q : A → Type ℓ'} → ((x : A) → P x ≃ Q x) → ((x : A) → P x) ≃ ((x : A) → Q x)
Π-map-cod≃ {A = A} {P = P} {Q = Q} e = packEquiv to sec to-fro ret fro-to
  where
    to : ((x : A) → P x) → ((x : A) → Q x)
    to f x = e x .map (f x)

    sec : ((x : A) → Q x) → ((x : A) → P x)
--  Exercise:
    sec g x = {!!}

    ret : ((x : A) → Q x) → ((x : A) → P x)
--  Exercise:
    ret g' = {!!}

    to-fro : isSection to sec
--  Exercise:
    to-fro g = {!!}

    fro-to : isRetract to ret
--  Exercise:
    fro-to f = {!!}

funexthalf-≃ : {A : Type ℓ} {B : I → Type ℓ'}
  {f : A → B i0} {g : A → B i1}
  → ((x₀ : A) (x₁ : A) → Path A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A → B i) f g
funexthalf-≃ {A = A} {B = B} {f = f} {g = g} =
  ((x₀ x₁ : A) → Path A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃⟨ Π-map-cod≃ (λ x₀ → J-ump-≃ (λ y _ → PathP B (f x₀) (g y))) ⟩
  ((x : A) → PathP B (f x) (g x))
  ≃⟨ funextP-≃ ⟩
  PathP (λ i → A → B i) f g ∎e

funextP-ump-≃ : {A : I → Type ℓ} {B : I → Type ℓ'}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x₀ : A i0) (x₁ : A i1) → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g
funextP-ump-≃ {A = A} {B = B} {f = f} {g = g} =
  J
  (λ A1 A → {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x₀ : A i0) (x₁ : A i1) → PathP (λ i → A i) x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ PathP (λ i → A i → B i) f g)
  funexthalf-≃ (λ i → A i)

```

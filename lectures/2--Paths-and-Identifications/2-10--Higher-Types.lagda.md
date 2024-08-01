```
module 2--Paths-and-Identifications.2-10--Higher-Types where
```

# Lecture 2-10: Higher Types

<!--
```
open import Library.Prelude
open import Library.Literals
open import Library.Univalence
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets
open import 2--Paths-and-Identifications.2-9--Contractible-Maps
```
-->


## Suspensions

mvrnote: where should this go? all the suspension examples work fine once we have composition

```
data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

Susp-map : {ℓ : Level} {X Y : Type ℓ} → (f : X → Y) → Susp X → Susp Y
Susp-map f north = north
Susp-map f south = south
Susp-map f (merid a i) = merid (f a) i
```

The simplest example is when we feed ``Susp`` the empty type
``∅``. You can use an absurd pattern in the ``merid`` case.

```
Susp∅≅Bool : Susp ∅ ≃ Bool
-- Exercise (trivial):
-- Susp∅≅Interval = {!!}
Susp∅≅Bool = equiv fun inv to-fro fro-to
  where
    fun : Susp ∅ → Bool
    fun north = true
    fun south = false
    fun (merid () i)
    inv : Bool → Susp ∅
    inv true = north
    inv false = south
    to-fro : isSection fun inv
    to-fro true = refl
    to-fro false = refl
    fro-to : isRetract fun inv
    fro-to north = refl
    fro-to south = refl
    fro-to (merid () i)
```

Next simplest is the unit type ``⊤``, where the result looks like
the following:

```
Susp⊤≅Interval : Susp ⊤ ≃ Interval
-- Exercise (also trivial):
-- Susp⊤≅Interval = {!!}
Susp⊤≅Interval = equiv fun inv to-fro fro-to
  where
    fun : Susp ⊤ → Interval
    fun north = zero
    fun south = one
    fun (merid tt i) = seg i
    inv : Interval → Susp ⊤
    inv zero = north
    inv one = south
    inv (seg i) = merid tt i
    to-fro : isSection fun inv
    to-fro zero = refl
    to-fro one = refl
    to-fro (seg i) = refl
    fro-to : isRetract fun inv
    fro-to north = refl
    fro-to south = refl
    fro-to (merid tt i) = refl
```

And we have seen that this ``Interval`` is contractible.

Finally something interesting happens once we try ``Bool``.

mvrnote: will this need hints?
```
SuspBool≅S¹ : Susp Bool ≃ S¹
-- Exercise:
SuspBool≅S¹ = {!!}
```

```
data S∞ : Type where
  snorth : S∞
  ssouth : S∞
  smerid : S∞ → snorth ≡ ssouth

S∞SelfSusp : S∞ ≃ Susp S∞
S∞SelfSusp = equiv to fro to-fro fro-to
  where
    to : S∞ → Susp S∞
    to snorth = north
    to ssouth = south
    to (smerid s i) = merid s i
    fro : Susp S∞ → S∞
    fro north = snorth
    fro south = ssouth
    fro (merid a i) = smerid a i
    to-fro : isSection to fro
    to-fro north = refl
    to-fro south = refl
    to-fro (merid a i) = refl
    fro-to : isRetract to fro
    fro-to snorth = refl
    fro-to ssouth = refl
    fro-to (smerid a i) = refl

isContrS∞ : isContr S∞
fst isContrS∞ = snorth
snd isContrS∞ = go
  where go : (y : S∞) → snorth ≡ y
        go snorth = refl ∙ refl
        go ssouth = smerid snorth ∙ refl
        go (smerid s i) = connection∧ (smerid snorth) i ∙ cong (λ t → smerid t i) (go s)

```

mvrnote: Some exercises: Suspension of isContr isContr, Suspension of isProp isSet


## Even Higher types

Egbert exercises:

Show that a type 𝑋 is a set if and only if the map
𝜆𝑥. 𝜆𝑡. 𝑥 : 𝑋 → (S1 → 𝑋)
is an equivalence.

mvrnote: exercises
(b) Construct an equivalence fib𝛿𝐴
(𝑥, 𝑦) ' (𝑥 = 𝑦) for any 𝑥, 𝑦 : 𝐴.
(c) Show that 𝐴 is (𝑘 + 1)-truncated if and only if 𝛿𝐴 : 𝐴 → 𝐴 × 𝐴 is
𝑘-truncated.

22.1 (a)

```
-- zero≢one : ¬ pos zero ≡ pos (suc zero)
-- zero≢one p = {!!}

-- -- isConnected : (X : Type) → Type
-- -- isConnected X = isContr ∥ X ∥₀

-- isConnectedS¹-path : (s : S¹) → ∥ base ≡ s ∥
-- isConnectedS¹-path base = ∣ refl ∣
-- isConnectedS¹-path (loop i) = squash ∣ (λ j → loop (i ∧ j)) ∣ ∣ (λ j → loop (i ∨ ~ j)) ∣ i

-- not-isContrS¹ : ¬ isContr S¹
-- not-isContrS¹ c = zero≢one (isContr→isProp (isContrAcrossIso (invIso ΩS¹Isoℤ) (isContrisContr≡ c base base)) (pos zero) (pos (suc zero)))

-- not-inhabited→pointed : ¬ ((A : Type) → ∥ A ∥ → A)
-- not-inhabited→pointed p = not-isContrS¹ (base , λ y → p (base ≡ y) (isConnectedS¹-path y))
```

22.2 and 22.4

```
-- degree : (f : S¹ → S¹) → (f base ≡ base) → ℤ
-- degree f = {!!}

-- S¹-auto : Iso (S¹ ≃ S¹) (S¹ ⊎ S¹)
-- Iso.fun S¹-auto x = {!!}
-- Iso.inv S¹-auto = {!!}
-- Iso.rightInv S¹-auto = {!!}
-- Iso.leftInv S¹-auto = {!!}
```

From Favonia's homeworks
------------------------------------------------------------------------------------
{- Task 1 -}
------------------------------------------------------------------------------------

-- loop spaces
Ω² : ∀ (A : Type) → A → Type
Ω² A x = (refl {x = x}) ≡ refl

{- Task 1.1: prove this lemma -}
ap-id : ∀ {A : Type} {x y : A} (p : x ≡ y) → ap (λ x → x) p ≡ p
ap-id = magic

-- binary version of ap
ap2 : ∀ {A B C : Type} (f : A → B → C) {x y : A} → x ≡ y → {z w : B} → z ≡ w → f x z ≡ f y w
ap2 f {x} {y} p {z} {w} q = ap (λ a → f a z) p ∙ ap (λ b → f y b) q

{- Task 1.2: find another way to implement ap2 that is "symmetric" to the above ap2 -}
ap2' : ∀ {A B C : Type} (f : A → B → C) {x y : A} → x ≡ y → {z w : B} → z ≡ w → f x z ≡ f y w
ap2' = magic

-- You might find this useful in Tasks 1.3 and 1.4
lemma₀ : ∀ {A : Type} {x : A} (p : Ω² A x) → ap (λ x → x ∙ refl) p ≡ p
lemma₀ {x = x} p = lemma₀' p ∙ ∙-unit-r p where
  lemma₀' : ∀ {l : x ≡ x} (p : refl ≡ l) → ap (λ x → x ∙ refl) p ≡ p ∙ ! (∙-unit-r l)
  lemma₀' refl = refl

{- Task 1.3: check the definition of `ap2` and prove this lemma -}
task1-3 : ∀ {A : Type} {x : A} (p q : Ω² A x) → ap2 (λ x y → x ∙ y) p q ≡ p ∙ q
task1-3 = magic
{- Hints:
   1. What are the implicit arguments x, y, z, and w when applying ap2?
   2. What's the relation between λ x → x and λ x → refl ∙ x? -}

{- Task 1.4: prove this lemma -}
task1-4 : ∀ {A : Type} {x : A} (p q : Ω² A x) → ap2' (λ x y → x ∙ y) p q ≡ q ∙ p
task1-4 = magic

{- Task 1.5: prove that ap2 f p q ≡ ap2' f p q -}
task1-5 : ∀ {A B C : Type} (f : A → B → C) {x y : A} (p : x ≡ y) {z w : B} (q : z ≡ w) → ap2 f p q ≡ ap2' f p q
task1-5 = magic

{- Task 1.6: the final theorem -}
eckmann-hilton : ∀ {A : Type} {x : A} (p q : Ω² A x) → p ∙ q ≡ q ∙ p
eckmann-hilton = magic

Cubical proof, from library

EH-base : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl)
         → (λ i → α i ∙ refl) ∙ (λ i → refl ∙ β i)
          ≡ (λ i → refl ∙ β i) ∙ (λ i → α i ∙ refl)
EH-base α β i = (λ j → α (~ i ∧ j) ∙ β (i ∧ j)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

EH : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl) → α ∙ β ≡ β ∙ α
EH {A = A} α β i j z =
  hcomp (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ (cong (λ x → lUnit x (~ k)) β)) j
                 ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ (cong (λ x → rUnit x (~ k)) α)) j
                 ; (j = i0) → rUnit refl (~ k)
                 ; (j = i1) → rUnit refl (~ k)})
  (EH-base α β i j) z

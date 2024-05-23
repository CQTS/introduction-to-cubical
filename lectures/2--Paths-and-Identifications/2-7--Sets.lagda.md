```
module 2--Paths-and-Identifications.2-7--Sets where
```

# Lecture 2-7: Sets

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

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B P : Type ℓ
```
-->

As we saw in Lecture 2-1, paths in inductive types like `Bool`{.Agda},
`ℕ`{.Agda} and `ℤ`{.Agda} are equalities between elements. As a
consequence, for any two elements `x` and `y`, the type of paths
`x ≡ y` is always a proposition --- specifically, the proposition that
`x` equals `y`.

We call types with this property *sets*.

```
isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
```

The type `⊤`{.Agda} is a one-element set, and the empty type
`∅`{.Agda} is the set with no elements.

```
isSet⊤ : isSet ⊤
isSet⊤ x y = isContr→isProp (isContrisContr≡ isContr⊤ x y)

isSet∅ : isSet ∅
isSet∅ ()
```

Other inductive type take a little more work, but we've already done
all of it in Lectures 2-2 and 2-5.

```
isSetBool : isSet Bool
isSetBool x y = isPropIso (≡Iso≡Bool x y) (isProp-≡Bool x y)

isSetℕ : isSet ℕ
isSetℕ x y = isPropIso (≡Iso≡ℕ x y) (isProp-≡ℕ x y)

isProp-≡⊎ : {A B : Type} → isSet A → isSet B → (a b : A ⊎ B) → isProp (a ≡⊎ b)
-- Exercise:
isProp-≡⊎ sA sB a b = ?

isSet⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
-- Exercise:
isSet⊎ pA pB = ?
```

We can show a number of closure properties of sets, similar to those
closure properties we showed for propositions and contractible types.

If `A` and `B` are sets, then `A × B` is a set.

```
isSet× : isSet A → isSet B → isSet (A × B)
-- Exercise:
isSet× pA pB = ?
```

If `B` is a set, then for any type `A`, the type `A → B` of functions
into `B` is a set.

```
isSet→ : isSet B → isSet (A → B)
-- Exercise:
isSet→ pB = ?
```

We can also show that any proposition is a set. This may sound a bit
odd, but we can think of any proposition `P` as a set with at most onexbf
element --- it is, after all, a type with at most one element.

Hint: Here is the cube we want to fill.

                        refl
                b - - - - - - - - > b
         p    / ^             q   / ^
            /   |               /   |
          /     | refl        /     |
        a - - - - - - - - > a       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       a - - - - - | - - > a
        |     /             |     /
        |   /               |   /
        | /                 | /
        a - - - - - - - - > a

```
isProp→isSet : isProp A → isSet A
-- Exercise:
isProp→isSet h = ?
```

Similar to contractible types and propositions, we have that any
retract of a set is a set.

```
isSetRetract :
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isSet B → isSet A
-- Exercise:
isSetRetract f g h setB = ?

isSetIso : Iso A B → isSet B → isSet A
isSetIso f pB = isSetRetract (isoFun f) (isoInv f) (isoLeftInv f) pB
```

In the rest of this section we will prove that `Σ[ a ∈ A ] B a` is a
set whenever `A` is a set and `B a` is a set for every `a : A`.

First, `Σ`{.Agda} is functorial:
```
-- mvrnote: surely this can go earlier somewhere
Σ-map : {A' : Type ℓ₂} {B : A → Type ℓ₃} {B' : A' → Type ℓ₄}
       (f : A → A')
     → (g : (a : A) → B a → B' (f a))
     → Σ[ a ∈ A ] B a → Σ[ a' ∈ A' ] B' a'
Σ-map f g (a , b) = (f a , g a b)
```

In particular, if `A` is the same as `A'` and `g a : B a → B' a` is
always an isomorphisms, then `Σ-map (idfun A) g` is an isomorphism.

```
Σ-cong-iso-snd : {B : A → Type ℓ₃} {B' : A → Type ℓ₄} →
                 ((x : A) → Iso (B x) (B' x)) → Iso (Σ[ a ∈ A ] B a) (Σ[ a ∈ A ] B' a)
Σ-cong-iso-snd {A = A} {B = B} {B' = B'} isom = iso fun inv rightInv leftInv
  where
    fun : (Σ[ a ∈ A ] B a) → (Σ[ a ∈ A ] B' a)
    fun (x , y) = x , isoFun (isom x) y

    inv : (Σ[ a ∈ A ] B' a) → (Σ[ a ∈ A ] B a)
    inv (x , y') = x , isoInv (isom x) y'

    rightInv : section fun inv
    rightInv (x , y) = ΣPathP→PathPΣ (refl , isoRightInv (isom x) y)

    leftInv : retract fun inv
    leftInv (x , y') = ΣPathP→PathPΣ (refl , isoLeftInv (isom x) y')
```

mvrnote: fix prose

With this isomorphism in hand, we can revisit what paths in a `Σ`{.Agda}-type are.

mvrnote: move this earlier? just needs composition

```
Σ-path-iso :
  {A : Type ℓ} {B : A → Type ℓ'}
  (a b : Σ[ a ∈ A ] B a) → Iso (Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b) (a ≡ b)
Σ-path-iso {B = B} a b =
  compIso (Σ-cong-iso-snd (λ p → invIso (PathP-iso-Path (λ i → B (p i)) _ _)))
          ΣPath-PathΣ-Iso
```

Finally, knowing what isomorphisms are in `Σ`{.Agda} types, we can
prove that `Σ[ a ∈ A ] B a` is a set whenever `A` is a set and `B a`
is a set for any `a : A`.

```
isSetΣ : {B : A → Type ℓ'} → isSet A → ((a : A) → isSet (B a))
       → isSet (Σ[ a ∈ A ] B a)
isSetΣ {A = A} {B = B} setA setB a b = isPropIso (invIso (Σ-path-iso a b)) isProp-ΣPathTransport
  where
    isProp-ΣPathTransport : isProp (Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b)
    isProp-ΣPathTransport = isPropΣ (setA (fst a) (fst b))
                                   (λ p → setB (p i1) (transport (λ i → B (p i)) (snd a)) (snd b))
```

mvrnote: where did these come from?
```
{-
data Bouquet (A : Type ℓ) : Type ℓ where
  pot : Bouquet A
  bulb : (a : A) → Bouquet A
  stem : (a : A) → pot ≡ bulb a
  flower : (a : A) → bulb a ≡ bulb a

ΩBouquet : (A : Type ℓ) → Type ℓ
ΩBouquet A = (pot {A = A} ≡ pot)

data InvList (A : Type ℓ) : Type ℓ where
  ε : InvList A
  _:∙:_ : (a : A) → InvList A → InvList A
  _⁻¹:∙:_ : (a : A) → InvList A → InvList A
  section-law : (a : A) (L : InvList A)  → (a :∙: (a ⁻¹:∙: L)) ≡ L  -- section-law a : section (a :∙:_) (a ⁻¹:∙:_)
  retract-law : (a : A) (L : InvList A)  → (a ⁻¹:∙: (a :∙: L)) ≡ L  -- retract-law a : retract (a :∙:_) (a ⁻¹:∙:_)
  is-set : isSet (InvList A)

_+++_ : {A : Type ℓ} → InvList A → InvList A → InvList A
ε +++ L' = L'
(a :∙: L) +++ L' = a :∙: (L +++ L')
(a ⁻¹:∙: L) +++ L' = a ⁻¹:∙: (L +++ L')
section-law a L i +++ L' = section-law a (L +++ L') i
retract-law a L i +++ L' = retract-law a (L +++ L') i
is-set L L₁ p q i j +++ L' = is-set (L +++ L') (L₁ +++ L') (λ j → p j +++ L') (λ j → q j +++ L') i j

bouquet-gen : ∀ {ℓ} {A : Type ℓ} → A → ΩBouquet A
bouquet-gen a = stem a ∙∙ flower a ∙∙ sym (stem a)

to-bouquet : ∀ {ℓ} {A : Type ℓ} (sA : isSet A) → InvList A → ΩBouquet A
to-bouquet sA ε = refl
to-bouquet sA (a :∙: L) = (bouquet-gen a) ∙ (to-bouquet sA L)
to-bouquet sA (a ⁻¹:∙: L) = sym (bouquet-gen a) ∙ to-bouquet sA L
to-bouquet sA (section-law a L i) = {!!}
to-bouquet sA (retract-law a L i) = {!!}
to-bouquet sA (is-set L L₁ x y i i₁) = {!!}
-}
{-
inverse : {A : Type ℓ} → InvList A → InvList A
inverse ε = ε
inverse (a :∙: L) = (inverse L) +++ (a ⁻¹:∙: ε)
inverse (a ⁻¹:∙: L) = (inverse L) +++ (a :∙: ε)
inverse (section-law a L i) = {!!}
inverse (retract-law a L i) = {!!}
inverse (is-set L L₁ x y i i₁) = {!!}


--- using encode-decode
one-of-our-theorems : {A : Type ℓ} → Iso (ΩBouquet A) (InvList A)
one-of-our-theorems = {!!}
-}
```

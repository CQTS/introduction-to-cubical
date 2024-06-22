```
module 2--Paths-and-Identifications.2-7--Sets where
```

# Lecture 2-7: Sets

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-X--Universe-Levels-and-More-Inductive-Types
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
    A A' B P : Type ℓ
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
isSet⊤ x y = isContr→isProp (isContr→isContr≡ isContr⊤ x y)

isSet∅ : isSet ∅
isSet∅ ()
```

Other inductive type take a little more work, but we've already done
all of it in Lectures 2-2 and 2-5.

```
isSetBool : isSet Bool
isSetBool x y = isPropEquiv (≡≃≡Bool x y) (isProp-≡Bool x y)

isSetℕ : isSet ℕ
isSetℕ x y = isPropEquiv (≡≃≡ℕ x y) (isProp-≡ℕ x y)

isProp-≡⊎ : {A B : Type} → isSet A → isSet B → (a b : A ⊎ B) → isProp (a ≡⊎ b)
-- Exercise:
isProp-≡⊎ sA sB a b = {!!}

isSet⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
-- Exercise:
isSet⊎ pA pB = {!!}
```

We can show a number of closure properties of sets, similar to those
closure properties we showed for propositions and contractible types.

If `A` and `B` are sets, then `A × B` is a set.

```
isSet× : isSet A → isSet B → isSet (A × B)
-- Exercise:
isSet× pA pB = {!!}
```

If `B` is a set, then for any type `A`, the type `A → B` of functions
into `B` is a set.

```
isSet→ : isSet B → isSet (A → B)
-- Exercise:
isSet→ pB = {!!}
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
isProp→isSet h = {!!}
```

Similar to contractible types and propositions, we have that any
retract of a set is a set.

```
isSetRetract : B retractsOnto A → isSet B → isSet A
-- Exercise:
isSetRetract (r , s , p) setB = ?

isSetEquiv : A ≃ B → isSet B → isSet A
isSetEquiv = isSetRetract ∘ equivRetracts
```

Finally, knowing what equivalences are in `Σ`{.Agda} types, we can
prove that `Σ[ a ∈ A ] B a` is a set whenever `A` is a set and `B a`
is a set for any `a : A`.

```
isSetΣ : {B : A → Type ℓ'}
  → isSet A
  → ((a : A) → isSet (B a))
  → isSet (Σ[ a ∈ A ] B a)
isSetΣ {A = A} {B = B} setA setB a b = isPropEquiv (Σ-path-≃ a b) isProp-ΣPathTransport
  where
    isProp-ΣPathTransport : isProp (Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b)
    isProp-ΣPathTransport = isPropΣ (setA (fst a) (fst b))
                                    (λ p → setB (p i1) (transport (λ i → B (p i)) (snd a)) (snd b))
```

As an aside, univalence allows us to prove that the type of
propositions is a set.

```
-- mvrnote: this has to go later, we don't have isProp (isEquiv f) until after contractible maps
-- mvrnote: turn parts of this into exercise
-- isPropEquivOfProp : ∀ {ℓ} → (X Y : Prop ℓ) → isProp (fst X ≃ fst Y)
-- isPropEquivOfProp (X , pX) (Y , pY) e f = equivEq (isProp→ pY _ _)

-- isPropProp≡ : ∀ {ℓ} → (X Y : Prop ℓ) → isProp (fst X ≡ fst Y)
-- isPropProp≡ (X , pX) (Y , pY) = isPropEquiv univalenceEquiv (isPropEquivOfProp (X , pX) (Y , pY))

-- isSetProp : ∀ {ℓ} → isSet (Prop ℓ)
-- isSetProp (X , pX) (Y , pY)
--   = isPropEquiv
--       (invEquiv (≡InSubtype (∀isProp→isPred λ _ → isPropIsProp) (X , pX) (Y , pY)))
--       (isPropProp≡ (X , pX) (Y , pY))
```


## Hedberg's Theorem

mvrnote: prose

```
Dec≡ : {ℓ : Level} → Type ℓ → Type ℓ
Dec≡ A = (x y : A) → Dec (x ≡ y)

```

Here's a simple example. We know that not all propositions are
decidable, but all propositions have decidable equality. Given two
elements of a proposition it is easy to decide whether they are equal,
the answer is always yes!

```
Dec≡-isProp : isProp A → Dec≡ A
-- Exercise:
Dec≡-isProp pA = {!!}
```

Inductive types often have decidable equality. The proofs are much
like the (very similarly named) `Dec-≡Bool`{.Agda} and `Dec-≡ℕ{.Agda}
definitions from earlier, which we wrote before we had the notion of
path.

```
Dec≡-Bool : Dec≡ Bool
-- Exercise:
Dec≡-Bool = {!!}

Dec≡-ℕ : Dec≡ ℕ
-- Exercise:
Dec≡-ℕ = {!!}
```

We now proceed to prove Hedberg's Theorem. We will follow a slick
proof that we learned from Favonia.

Here is the idea. Suppose we have a path `p₁ : x ≡ y`. By assumption,
`x ≡ y` is decidable, so we also have an element of `Dec (x ≡ y)`.
This can't be a `no`{.Agda}, because that would immediately give a
contradiction: after all, we already have the path `p₁`.

So we have `yes q : Dec (x ≡ y)`, for some other path `q : x ≡ y`. But
here is the key: this path `q` is the *same*, regardless of which `p₁`
we start with.

Start by replacing a path `p` with the `q` from `Dec (x ≡ y)`.

```
Dec≡-bad-replacement : {x y : A} → Dec (x ≡ y) → x ≡ y → x ≡ y
-- Exercise:
Dec≡-bad-replacement d p = {!!}
```

The next step is to show that this replacement is equal to the path
that we started with. We want to do this using `J`{.Agda}, but for
that to work, we need the replacement to equal `refl` when `p` is
itself `refl`. Right now it isn't: instead the replacement is just
`Dec≡-bad-replacement (dec x x) refl : x ≡ x`, which doesn't simplify.

This is easily fixed: just compose the bad replacement with the
inverse of the path we want to get rid of:

```
Dec≡-good-replacement : Dec≡ A → {x y : A} → x ≡ y → x ≡ y
-- Exercise:
Dec≡-good-replacement dec {x} {y} p = {!!}

Dec≡-replacement-undo : (dec : Dec≡ A) → {x y : A} → (p : x ≡ y) → Dec≡-good-replacement dec p ≡ p
-- Exercise:
Dec≡-replacement-undo dec {x} {y} p = J (λ y p → Dec≡-good-replacement dec p ≡ p) {!!} {!!}
```

The final lemma is that these good replacements are equal to each
other, regardless of what path you start with. This is easy once we
pattern match on `Dec (x ≡ y)`.

mvrnote: this spoils the answer to `Dec≡-good-replacement`...

```
Dec≡-replacement-same : (dec : Dec≡ A) → {x y : A} → (p₁ p₂ : x ≡ y)
  → Dec≡-good-replacement dec p₁ ≡ Dec≡-good-replacement dec p₂
-- Exercise:
Dec≡-replacement-same dec {x} {y} p₁ p₂ = {!!}
--      Exercise:
        helper d = {!!}
```

Now stick these together to finish the proof.

```
hedberg : Dec≡ A → isSet A
hedberg dec x y p₁ p₂ =
    p₁                           ≡⟨ sym (Dec≡-replacement-undo dec p₁) ⟩
    Dec≡-good-replacement dec p₁ ≡⟨ Dec≡-replacement-same dec p₁ p₂ ⟩
    Dec≡-good-replacement dec p₂ ≡⟨ Dec≡-replacement-undo dec p₂ ⟩
    p₂ ∎
```

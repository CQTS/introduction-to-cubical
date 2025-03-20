<!--
```
module 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types where

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

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
```
-->


# Lecture 2-8: Sets and Higher Types

We saw in Lecture 2-X that paths in inductive types like ``Bool``,
``ℕ`` and ``ℤ`` are equalities between elements. As a consequence, for
any two elements `x` and `y`, the type of paths `x ≡ y` is always a
proposition --- specifically, the proposition that `x` equals `y`.

We call types with this property *sets*.

```
isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
```

mvrnote: more intuition, uip, axiom k, etc


## Basic Examples

We characterised the types of paths in ``⊤``, ``Bool`` and ``ℕ`` back
in Lecture 2-X, and from these it is easy to show they are all sets.

```
isSet-⊤ : isSet ⊤
-- Exercise: (Hint: `≡≃≡⊤`)
isSet-⊤ x y = isPropEquiv {!!} {!!}

isSet-Bool : isSet Bool
-- Exercise:
isSet-Bool x y = {!!}

isSet-ℕ : isSet ℕ
-- Exercise:
isSet-ℕ x y = {!!}
```

The empty type ``∅`` is the set with no elements.

```
isSet-∅ : isSet ∅
-- Exercise:
isSet-∅ = {!!}
```

For ``⊎``, we will need a helper that relates paths in the two sides
to the characterisation ``≡⊎`` from back in Lecture 2-X.

```
isProp-≡⊎ : {A B : Type} → isSet A → isSet B → (a b : A ⊎ B) → isProp (a ≡⊎ b)
-- Exercise:
isProp-≡⊎ sA sB a b = {!!}

isSet-⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
-- Exercise:
isSet-⊎ pA pB = {!!}
```

Every proposition is a set. This may sound like an odd claim,
especially if you are used to first-order logic where there is a
strict separation between the two. In our setting, any proposition `P`
is a set that has at most one element.

```
isProp→isSet : isProp A → isSet A
-- Exercise:
isProp→isSet pA x y = {!!}
```

Again, not all types are sets. The type ``S¹`` should not be a set
since we have a path ``loop`` that we know is not the same as
``refl``.

```
¬isSet-S¹ : ¬ isSet S¹
-- Exercise:
¬isSet-S¹ isSet = {!!}
```

The type ``Type`` is not a set either. If all paths in ``Type`` were
equal, then ``not-Path`` would be equal to ``refl`` as a path `Bool ≡
Bool`, and this quickly leads to a contradiction.

```
¬isSet-Type : ¬ isSet Type
-- Exercise: (Hint: `true≢false`)
¬isSet-Type s = {!!}
```

One way of thinking of ``isSet`` is that for any paths `p : x ≡ y` and
`q : x ≡ y` there is a ``Square`` with shape

            refl
        y — — — — > y
        ^           ^            ^
      p |           | q        j |
        |           |            ∙ — >
        x — — — — > x              i
            refl

Of course, we can't necessarily get some ``Square`` like this for any
choice of corners `x` and `y`, we need the paths `p` and `q` to exist
to begin with.

So, ``isSet`` is like ``isProp`` but one dimension higher. We can't
necessarily fill a path between any two points, but we can fill any
``Square``:

```
isSet→Square : isSet A
  → {a b c d : A}
  → (r : a ≡ c) (s : b ≡ d)
  → (t : a ≡ b) (u : c ≡ d)
  → Square t u r s
-- Exercise: (Hint: `toPathP`)
isSet→Square sA r s t u = {!!}
```

Because being a set means that asking that a certain family of types
is all propositions, ``isSet`` is a proposition about a type.

```
isProp-isSet : isProp (isSet A)
-- Exercise: (Use `isProp-Π`)
isProp-isSet = {!!}
```


## Closure Properties

We can show a number of closure properties of sets like those for
 propositions and contractible types.

First, if `A` and `B` are sets, then `A × B` is a set, and for `A → B`
it is sufficient for just `B` to be a set.

```
isSet-× : isSet A → isSet B → isSet (A × B)
-- Exercise:
isSet-× pA pB = {!!}

isSet-→ : isSet B → isSet (A → B)
-- Exercise:
isSet-→ pB = {!!}
```

Similarly to contractible types and propositions, any retract of a set
is a set. This follows easily from the following general about fact
about homotopies.

mvrnote: do we need a "functions are functors" section?
mvrnote: what's a good name for this?
mvrnote: draw cube?

```
homotopy-conjugate : {f g : A → B}
  → (H : (x : A) → (f x ≡ g x))
  → {a b : A}
  → {r : a ≡ b}
  → f a ≡ f b
  → g a ≡ g b
homotopy-conjugate {B = B} H {a = a} {b} p i = hcomp (∂ i) faces
  where 
    faces : (k : I) → Partial (∂ i ∨ ~ k) B
    faces k (i = i0) = H a k
    faces k (i = i1) = H b k
    faces k (k = i0) = p i

homotopy-conjugate-Square : {f g : A → B}
  → (H : (x : A) → (f x ≡ g x))
  → {a b c d : A}
  → {r : a ≡ c} {s : b ≡ d}
  → {t : a ≡ b} {u : c ≡ d}
  → Square (ap f t) (ap f u) (ap f r) (ap f s)
  → Square (ap g t) (ap g u) (ap g r) (ap g s)
homotopy-conjugate-Square {B = B} H {r = r} {s} {t} {u} sq i j 
  = hcomp (∂ i ∨ ∂ j) faces
  where
    faces : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) B
    faces k (j = i0) = H (r i) k
    faces k (j = i1) = H (s i) k
    faces k (i = i0) = H (t j) k
    faces k (i = i1) = H (u j) k
    faces k (k = i0) = sq i j
```

::: Aside:
Alternatively, produce a path

      Square (ap f t) (ap f u) (ap f r) (ap f s) 
    ≡ Square (ap g t) (ap g u) (ap g r) (ap g s)

and apply ``transport``.
:::

```
isSet-retract : B RetractOnto A → isSet B → isSet A
isSet-retract r sB x y p q 
  = homotopy-conjugate-Square (r .section .proof) (ap-Square (r .map) (sB _ _ _ _))

isSet-equiv : A ≃ B → isSet B → isSet A
isSet-equiv = isSet-retract ∘ equiv→retract
```

And ``isSet-equiv`` lets us easily clear up ``ℤ``, without fussing
with defining an observational equality type `≡ℤ`:

```
isSet-ℤ : isSet ℤ
-- Exercise: (Hint: Find a useful equivalence in Lecture 2-X)
isSet-ℤ = isSet-equiv {!!} {!!}
```


## Hedberg's Theorem

There's a very slick criterion for when a type is a set: Hedberg's
Theorem, which states that any type with *decidable equality* is a
set. A type has decidable equality whenever the type of paths between
any two points is decidable:

```
Dec≡ : Type ℓ → Type ℓ
Dec≡ A = (x y : A) → Dec (x ≡ y)
```

We are assuming that the path types are all decidable, but
not that they are decidable *propositions*. (After all, if we already
knew they were propositions then we would already know our type is a
set.)

Here's a simple example. We have seen that not all propositions are
decidable, but all propositions have decidable equality. Given two
elements of a proposition it is easy to decide whether they are equal,
the answer is always ``yes``!

```
isProp→Dec≡ : isProp A → Dec≡ A
-- Exercise:
isProp→Dec≡ pA = {!!}
```

Inductive types often have decidable equality. The proofs are much
like the (very similarly named) ``Dec-≡Bool`` and ``Dec-≡ℕ``
definitions from earlier, which we wrote before we had the notion of
paths.

```
Dec≡-Bool : Dec≡ Bool
-- Exercise:
Dec≡-Bool = {!!}

Dec≡-ℕ : Dec≡ ℕ
-- Exercise:
Dec≡-ℕ = {!!}
```

We will prove Hedberg's Theorem using a slick argument that we learned
from [Favonia]. Here is the idea. Start with a path `p : x ≡ y`. By
assumption, `x ≡ y` is decidable, so we also have an element of `Dec
(x ≡ y)`. This can't be ``no``, because that would cause a
contradiction: after all, we already know that `x ≡ y` via `p`.

[Favonia]: https://favonia.org/courses/hdtt2020/

So we have `yes q : Dec (x ≡ y)`, where `q : x ≡ y` is also a path
between the same points. But here is the key: this path `q` is the
*same*, regardless of which `p` we start with.

Start by defining a function that either replaces a path `p` with the `q`
from `Dec (x ≡ y)` or derives a contradiction.

```
Dec≡-bad-replacement : {x y : A} → Dec (x ≡ y) → x ≡ y → x ≡ y
-- Exercise:
Dec≡-bad-replacement d p = {!!}
```

Next, we want to show that this replacement is equal to the path that
we started with. The plan is to do this using ``J``, but for that
to work we need the replacement to equal ``refl`` when `p` is
itself ``refl``. Right now it isn't: instead, the replacement is
just `Dec≡-bad-replacement (dec x x) refl : x ≡ x`, which doesn't
simplify.

This is easily fixed. Define a function that gives a good replacement
path, by composing the old definition with the inverse of the path
`Dec≡-bad-replacement (dec x x) refl` that we want to get rid of:

```
Dec≡-good-replacement : Dec≡ A → {x y : A} → x ≡ y → x ≡ y
-- Exercise:
Dec≡-good-replacement dec {x} {y} p = {!!}

Dec≡-replacement-undo : (dec : Dec≡ A) → {x y : A} → (p : x ≡ y) → Dec≡-good-replacement dec p ≡ p
-- Exercise:
Dec≡-replacement-undo dec {x} {y} p = J (λ y p → Dec≡-good-replacement dec p ≡ p) {!!} {!!}
```

The final lemma is that these good replacements are all equal to each
other, regardless of what path you start with. This is easy after
pattern-matching on `Dec (x ≡ y)`.

```
Dec≡-replacement-same : (dec : Dec≡ A) → {x y : A} → (p₁ p₂ : x ≡ y)
  → Dec≡-good-replacement dec p₁ ≡ Dec≡-good-replacement dec p₂
-- Exercise:
Dec≡-replacement-same dec {x} {y} p₁ p₂ = {!!}

  where helper : (w : Dec (x ≡ y)) →
            sym (Dec≡-bad-replacement (dec x x) refl) ∙ Dec≡-bad-replacement w p₁
          ≡ sym (Dec≡-bad-replacement (dec x x) refl) ∙ Dec≡-bad-replacement w p₂
--      Exercise:
        helper d = {!!}
```

Now glue these pieces together to finish the proof.

```
hedberg : Dec≡ A → isSet A
hedberg dec x y p₁ p₂ =
-- Exercise:
     p₁                           ≡⟨ {!!} ⟩
     Dec≡-good-replacement dec p₁ ≡⟨ {!!} ⟩
     Dec≡-good-replacement dec p₂ ≡⟨ {!!} ⟩
     p₂ ∎
```


## Higher Types

You may have noticed a pattern developing in the last couple of
Lectures. We start with the simplest possible types, the ones
satisfying ``isContr``. These contain no information at all.

More complicated are the propositions identified by ``isProp``. In
``isProp→isContr≡`` and ``isContr≡→isProp``, we observed that these
are the types whose path types are contractible. More complicated
again are the sets, identified by ``isSet``. By definition these are
the types whose path types are propositions. We can continue this
pattern inductively, stratifying types by what is known as their
*h-level*.

```
isHLevel : ℕ → Type ℓ → Type ℓ
isHLevel zero    X = isContr X
isHLevel (suc n) X = (x y : X) → isHLevel n (x ≡ y)
```

So types with h-level 0 are contractible, with h-level 1 are
propositions, and with h-level 2 are sets.

This definition doesn't exactly match ``isProp`` when `n = 1`, but as
we saw in ``isProp→isContr≡`` and ``isContr≡→isProp``, it is
equivalent. An alternative definition would specify

    isHLevel (suc zero) X = isProp X

directly rather than leaving that to the inductive case. We'll stick
with the simpler definition so that we have one fewer case to deal
with in our proofs. It is easy enough to patch over the difference.

```
isProp→isHLevel1 : isProp A → isHLevel 1 A
isProp→isHLevel1 = isProp→isContr≡

isHLevel1→isProp : isHLevel 1 A → isProp A
isHLevel1→isProp = isContr≡→isProp

isSet→isHLevel2 : isSet A → isHLevel 2 A
isSet→isHLevel2 sA x y = isProp→isHLevel1 (sA x y)

isHLevel2→isSet : isHLevel 2 A → isSet A
isHLevel2→isSet hA x y = isHLevel1→isProp (hA x y)
```

::: Caution:
In homotopy theory, a different numbering system is used for h-levels,
so that the hierarchy shifted down by two. A set, i.e. a type with
h-level 2, is said to have "truncation level 0", and a proposition has
"truncation level -1". Sometimes this is shortened even further, so
that a set is a "0-type" and a proposition is a "(-1)-type". This is
just a difference in conventions, but will be necessary to keep in
mind when reading other resources.
:::

```
isHLevel-suc : (n : ℕ) → isHLevel n A → isHLevel (suc n) A
-- Exercise:
isHLevel-suc n = {!!}

isProp-isHLevel : (n : ℕ) → isProp (isHLevel n A)
-- Exercise:
isProp-isHLevel n = {!!}
```

```
isHLevel-retract : (n : ℕ) → B RetractOnto A → isHLevel n B → isHLevel n A
-- Exercise:
isHLevel-retract n = {!!}

isHLevel-equiv : (n : ℕ) → (A ≃ B) → isHLevel n B → isHLevel n A
-- Exercise:
isHLevel-equiv = {!!}

isHLevel-Σ : {A : Type ℓ} → {B : A → Type ℓ'} 
  → (n : ℕ) 
  → isHLevel n A 
  → ((x : A) → isHLevel n (B x))
  → isHLevel n (Σ[ x ∈ A ] B x)
-- Exercise:
isHLevel-Σ n = {!!}

isHLevel-Π : {B : A → Type ℓ}  
  → (n : ℕ)
  → ((x : A) → isHLevel n (B x))
  → isHLevel n ((x : A) → B x)
-- Exercise:
isHLevel-Π n = {!!}

isHLevel-≡ : (n : ℕ)
  → isHLevel n A
  → (x y : A) → isHLevel n (x ≡ y)
isHLevel-≡ zero hA = isContr→isContr≡ hA
isHLevel-≡ (suc n) hA x y = isHLevel-suc n (hA x y)

isHLevel-PathP : {A : I → Type ℓ}
  → (n : ℕ)
  → ((i : I) → isHLevel n (A i))
  → (x : A i0) → (y : A i1) → isHLevel n (PathP A x y)
isHLevel-PathP zero hA = isContr→isContr-PathP (hA i1)
isHLevel-PathP (suc n) hA x y = isHLevel-equiv (suc n) (PathP≃Path _) (isHLevel-≡ n (hA i1 _ _))
```

```
isConnected-S¹ : (s : S¹) → ∃ (base ≡ s)
isConnected-S¹ base = in-∃ refl 
isConnected-S¹ (loop i) = squash (in-∃ λ j → loop (i ∧ j)) (in-∃ λ j → loop (i ∨ ~ j)) i

isHLevel3-S¹ : isHLevel 3 S¹
isHLevel3-S¹ = step-3
  where 
    step-1 : isHLevel 2 (base ≡ base)
    step-1 = isSet→isHLevel2 (isSet-equiv ΩS¹≃ℤ isSet-ℤ)

    step-2 : (y : S¹) → isHLevel 2 (base ≡ y)
    step-2 y = ∃-rec (isProp-isHLevel 2) (λ q → subst (λ t → isHLevel 2 (base ≡ t)) q step-1) (isConnected-S¹ y)

    step-3 : (x y : S¹) → isHLevel 2 (x ≡ y)
    step-3 x y = ∃-rec (isProp-isHLevel 2) (λ p → subst (λ x → isHLevel 2 (x ≡ y)) p (step-2 y)) (isConnected-S¹ x)
```

```
record Prop (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor propData
  field
    witness : Type ℓ
    witnessIsProp : isProp witness
open Prop public
```

mvrnote: good examples?


Univalence allows us to prove that the type of propositions is a set.

First, being an equivalence between propositions it itself a
proposition. (In fact, this is true for functions between any types,
as we prove with a lot more effort in Lecture 2-X, but it is easy
enough to prove directly for the case we need it here.)

```

-- isProp-isEquiv-for-Props : isProp P → isProp Q → (f : P → Q) → isProp (IsEquiv f)
-- -- Exercise: (Hint: Combine `isProp-Σ` and `isProp-Π` a few times.)
-- isProp-isEquiv-for-Props pP pQ f = {!!}
isProp-isEquiv-for-Props pP pQ f = isProp× (isPropΣ (isProp→ pP) (λ s → isPropΠ λ b → isProp→isSet pQ _ _))
                                              (isPropΣ (isProp→ pP) (λ r → isPropΠ λ a → isProp→isSet pP _ _))
```
mvrnote: missing?



## Suspensions

mvrnote: where should this go? all the suspension examples work fine once we have composition

```
data Susp {ℓ : Level} (A : Type ℓ) : Type ℓ where
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
Susp∅≃Bool : Susp ∅ ≃ Bool
-- Exercise (trivial):
-- Susp∅≃Interval = {!!}
Susp∅≃Bool = inv→equiv fun inv to-fro fro-to
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
Susp⊤≃Interval : Susp ⊤ ≃ Interval
-- Exercise (also trivial):
-- Susp⊤≃Interval = {!!}
Susp⊤≃Interval = inv→equiv fun inv to-fro fro-to
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

And we have seen that the ``Interval`` type is contractible.

```
isContr→isContr-Susp : isContr A → isContr (Susp A)
isContr→isContr-Susp cA .center = north
isContr→isContr-Susp cA .contraction north = refl ∙ refl
isContr→isContr-Susp cA .contraction south = (merid (cA .center)) ∙ refl
isContr→isContr-Susp cA .contraction (merid a i) = connection∧ (merid (cA .center)) i ∙ ap (λ t → merid t i ) (cA .contraction a)
```

```
-- eg: https://1lab.dev/Homotopy.Space.Suspension.Properties.html
-- isProp→isSet-Susp : isProp A → isSet (Susp A)
-- isProp→isSet-Susp pA x y p q = {!!}
```

Finally something interesting happens once we try ``Bool``.

```
SuspBool≃S¹ : Susp Bool ≃ S¹
-- Exercise:
SuspBool≃S¹ = {!!}
```


```
data S∞ : Type where
  snorth : S∞
  ssouth : S∞
  smerid : S∞ → snorth ≡ ssouth

S∞SelfSusp : S∞ ≃ Susp S∞
S∞SelfSusp = inv→equiv to fro to-fro fro-to
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

isContr-S∞ : isContr S∞
isContr-S∞ .center = snorth
isContr-S∞ .contraction = go
  where go : (y : S∞) → snorth ≡ y
        go snorth = refl ∙ refl
        go ssouth = smerid snorth ∙ refl
        go (smerid s i) = connection∧ (smerid snorth) i ∙ ap (λ t → smerid t i) (go s)
```

## Even Higher types

```
EH-base : {ℓ : Level} {A : Type ℓ} {x : A}
  → (α β : refl {x = x} ≡ refl)
  → Square (λ i → refl ∙ β i) 
           (λ i → refl ∙ β i) 
           (λ i → α i ∙ refl) 
           (λ i → α i ∙ refl)
EH-base α β i j = α i ∙ β j

EH : {ℓ : Level} {A : Type ℓ} {x : A}
  → (α β : refl {x = x} ≡ refl)
  → Square β β α α
EH α β i j = hcomp (∂ i ∨ ∂ j) (λ k → λ
    { (i = i0) → ∙-idl (β j) (~ k)
    ; (i = i1) → ∙-idl (β j) (~ k)
    ; (j = i0) → ∙-idr (α i) (~ k)
    ; (j = i1) → ∙-idr (α i) (~ k)
    ; (k = i0) → EH-base α β i j})
```

Egbert exercises:

Show that a type 𝑋 is a set if and only if the map
𝜆𝑥. 𝜆𝑡. 𝑥 : 𝑋 → (S1 → 𝑋)
is an equivalence.

mvrnote: general hlevels?

## References and Further Reading

mvrnote:

Hedberg's Theorem: https://doi.org/10.1017/S0956796898003153

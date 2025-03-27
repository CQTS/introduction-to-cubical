<!--
```
module 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' B B' C D : Type ℓ
    x y : A
```
-->


# Lecture 2-2: Equivalences and Path Algebra

mvrnote: intro

## Sections and Retracts

A function `f : A → B` lets us transform data of type `A` into data of
type `B`, so we can see a function `f : A → B` as a way to represent
elements of `A` by elements of `B`.

For example, in many languages, it is common to represent Booleans by
numbers by representing ``false`` by `0` and ``true`` by `1`. In Agda,
we could write this a function `Bool → ℕ` that turns each Boolean into
its representation..

```
Bool→ℕ : Bool → ℕ
Bool→ℕ true = suc zero
Bool→ℕ false = zero
```

If this is going to be useful, it needs to faithfully represent
Boolean values, in that we are able to decode a natural number back
into a Boolean.

```
isPositive : ℕ → Bool
isPositive zero = false
isPositive (suc n) = true

isPositive-represents-Bool : (b : Bool) → isPositive (Bool→ℕ b) ≡ b
-- Exercise:
isPositive-represents-Bool b = {!!}
```

This is a common situation, where a function `f : A → B` has a
one-sided inverse `g : B → A` so that `f (g b) ≡ b`. The technical
name for this is that `g` is a *section* of `f`.

```
isSection : {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) 
  → (g : B → A)
  → Type ℓ'
isSection {B = B} f g = (b : B) → f (g b) ≡ b
```

So here, ``Bool→ℕ`` is a section of ``isPositive``; this is exactly
what ``isPositive-represents-Bool`` above is saying.

```
isSection-isPositive-Bool→ℕ : isSection isPositive Bool→ℕ
isSection-isPositive-Bool→ℕ = isPositive-represents-Bool
```

One way to justify the name "section" is thinking of the the type `B`
(here ``Bool``) as being smaller than the type `A` (here ``ℕ``). A
function is a section if it picks out a small part of `A` (a small
"section" of `A`) that has the shape of `B`.

This is a notion that is going to come up a lot, so we will package
the notion of section into a record type.

```
record SectionOf {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  constructor sectionData
  field
    map : B → A
    proof : isSection f map

open SectionOf public
```

While every Boolean `b` can be represented by the natural number
`Bool→ℕ b`, it is not the case that every natural number `a` can be
represented by a Boolean with respect to the function ``Bool→ℕ``.
A natural number gives more data than a Boolean.

But what about the following type ``RedOrBlue``?

```
data RedOrBlue : Type where
  red : RedOrBlue
  blue : RedOrBlue
```

It is quite apparent that ``RedOrBlue`` has the same data as ``Bool``:
each has two elements and nothing more. We can represent a ``Bool`` as
an element of ``RedOrBlue`` as follows:

```
Bool→RedOrBlue : Bool → RedOrBlue
Bool→RedOrBlue true = red
Bool→RedOrBlue false = blue
```

And we can show this is a faithful representation by giving a section
``RedOrBlue→Bool`` of ``Bool→RedOrBlue``.

```
RedOrBlue→Bool : RedOrBlue → Bool
RedOrBlue→Bool red = true
RedOrBlue→Bool blue = false

isSection-Bool-RedOrBlue : isSection Bool→RedOrBlue RedOrBlue→Bool
isSection-Bool-RedOrBlue red = refl
isSection-Bool-RedOrBlue blue = refl
```

But this time, the function ``RedOrBlue→Bool`` faithfully represents
an element of ``RedOrBlue`` as a Boolean too!

```
isSection-RedOrBlue-Bool : isSection RedOrBlue→Bool Bool→RedOrBlue
isSection-RedOrBlue-Bool true = refl
isSection-RedOrBlue-Bool false = refl
```

For this reversed situation, we say that `f : A → B` is a *retract*
when it *has* a section.

```
isRetract : {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) 
  → (g : B → A)
  → Type ℓ
isRetract f g = isSection g f

record RetractOf {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  constructor retractData
  field
    map : B → A
    proof : isRetract f map

open RetractOf public
```

So as well as ``isSection-Bool-RedOrBlue``, we also have:

```
isRetract-Bool-RedOrBlue : isRetract Bool→RedOrBlue RedOrBlue→Bool
isRetract-Bool-RedOrBlue = isSection-RedOrBlue-Bool
```

And another way of summarising the ``Bool`` and ``ℕ`` situation is that
``isPositive`` is a *retract* of ``Bool→ℕ``.

```
isRetract-Bool→ℕ-isPositive : isRetract Bool→ℕ isPositive
isRetract-Bool→ℕ-isPositive = isPositive-represents-Bool
```

Again, thinking of ``Bool`` as being smaller than ``ℕ``, a function is
a retract when it is describing a way to shrink, or "retract", the
larger type into the smaller type.


## Equivalences

When the function `f : A → B` has a section `g : B → A` *and* has a
retract `g' : B → A`, as is the case for ``RedOrBlue→Bool``, we say
that `f` is an *equivalence*.

In this situation, `f` faithfully represents elements of `A` as
elements of `B` (which we know because it has a section `g`), and `g'`
faithfully represents elements of `B` as elements of `A` (which we
know because it has a section `f`, i.e. is a retract of `f`). So, we
can represent elements of `B` by elements of `A` and vice-versa ---
the types describe equivalent data.

We will package all this information into some handy records.

```
record isEquiv {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  constructor isEquivData
  field
    section : SectionOf f
    retract : RetractOf f

open isEquiv public

record Equiv (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor equiv
  field
    map : A → B
    proof : isEquiv map

open Equiv public
```

To avoid typing ``Equiv`` out everywhere, we will use the syntax `A ≃
B` for the type of equivalences between `A` and `B`.

```
_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
_≃_ = Equiv

infix 4 _≃_
```

To make these less annoying to work with, we'll write some helpers for
constructing these ``Equiv``s.

```
pattern packIsEquiv sec isSec ret isRet
  = isEquivData (sectionData sec isSec) (retractData ret isRet)

pattern packEquiv fun sec isSec ret isRet
  = equiv fun (packIsEquiv sec isSec ret isRet)
```

We mentioned these pattern synonyms back in Lecture 1-X. Here, they
let us construct an element of an ``Equiv`` record by writing
`packEquiv fun sec isSec ret isRet` rather than the fully explicit 
`equiv fun (isEquivData (sectionData sec isSec) (retractData ret isRet))`.

An equivalence between two types says, in effect, that elements of
those types are different representations of the same data. Putting
together the maps we defined above, ``Bool`` is equivalent to
``RedOrBlue``

```
Bool≃RedOrBlue : Bool ≃ RedOrBlue
Bool≃RedOrBlue 
  = packEquiv Bool→RedOrBlue 
              RedOrBlue→Bool
              isSection-Bool-RedOrBlue
              RedOrBlue→Bool
              isRetract-Bool-RedOrBlue
```

Having the section of `f` and retract of `f` be the same map is a very
common situation, so we will use a helper to duplicate the backwards
map in this case.

```
inv→equiv : (fun : A → B)
      → (inv : B → A)
      → (isSec : isSection fun inv)
      → (isRet  : isRetract fun inv)
      → A ≃ B
inv→equiv fun inv isSec isRet = packEquiv fun inv isSec inv isRet
```

::: Aside:
It might seem strange that our notion of equivalence involves *two*
maps backwards rather than just one.

When a map has a single inverse map that is a both a section and a
retract, the map is called an *isomorphism*, a faux-Greek word meaning
"same shape". While every isomorphism gives rise to an equivalence
(via the function ``inv→equiv`` we just defined) and every equivalence
gives rise to an isomorphism (via ``invEquiv`` coming up in Lecture
2-X), the type of equivalences and the type of isomorphisms between
two types are not always the same! 

It will turn out that "equivalence" as we've defined it here is the
better notion, because the type `isEquiv f` is a *proposition* about
the function `f` (see ``isProp-isEquiv``), whereas being an "isomorphism"
sneaks in extra data (see ``¬isProp-isIso``). We will happily forget about
the term "isomorphism" from this point on and stick with equivalence.
:::

At the very least, we can show that the identity function on any type
is an equivalence.

```
isEquiv-idfun : isEquiv (idfun {A = A})
-- Exercise:
isEquiv-idfun .section .map = {!!}
isEquiv-idfun .section .proof x = {!!}
isEquiv-idfun .retract .map = {!!}
isEquiv-idfun .retract .proof x = {!!}

idEquiv : (A : Type ℓ) → A ≃ A
-- Exercise:
idEquiv = {!!}
```

Now, this isn't the only way we could have shown that ``Bool`` is
equivalent to ``RedOrBlue``; we could also have sent ``true`` to
``blue`` and ``false`` to ``red``. Define this other equivalence
below:

```
OtherBool≃RedOrBlue : Bool ≃ RedOrBlue
OtherBool≃RedOrBlue = inv→equiv to fro to-fro fro-to
  -- Exercise:
  where
    to : Bool → RedOrBlue
    to x = {!!}

    fro : RedOrBlue → Bool
    fro x = {!!}

    to-fro : isSection to fro
    to-fro x = {!!}

    fro-to : isRetract to fro
    fro-to x = {!!}
```

Not every function `Bool → RedOrBlue` is an equivalence. If we send
both ``true`` and ``false`` to ``red``, for example, then there is no
way we can find an inverse. Any section would have to send ``red`` to
``true`` and also to ``false``, but these aren't equal.

In Lecture 1-X, we had a few "bijections" between types. At the time,
all we could do is produce maps going each way. Now we can show that
these really are equivalences. Here's an especially easy one, where
the paths in the ``to-fro`` and ``fro-to`` functions can be
``refl`` for any argument.

```
-- mvrnote: unused
×-ump-≃ : (C → A) × (C → B) ≃ (C → A × B)
×-ump-≃ = inv→equiv to fro to-fro fro-to
  where
    -- We defined this way back in Lecture 1-1, but only for
    -- types in the lowest universe.
    to : (C → A) × (C → B) → (C → A × B)
    to (f , g) c = (f c , g c)

    fro : (C → A × B) → (C → A) × (C → B)
    fro h = (λ c → fst (h c)) , (λ c → snd (h c))

    to-fro : isSection to fro
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract to fro
--  Exercise:
    fro-to x = {!!}

-- mvrnote: unused
×-assoc-≃ : (A × (B × C)) ≃ ((A × B) × C)
×-assoc-≃ = inv→equiv to fro to-fro fro-to
  where
    to : (A × (B × C)) → ((A × B) × C)
    to (a , (b , c)) = (a , b) , c

    fro : ((A × B) × C) → (A × (B × C))
    fro ((a , b) , c) = (a , (b , c))

    to-fro : isSection to fro
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract to fro
--  Exercise:
    fro-to x = {!!}

-- mvrnote: unused
curry-≃ : {ℓ₁ ℓ₂ ℓ₃ : Level}
  → {A : Type ℓ₁}
  → {B : A → Type ℓ₂}
  → {C : (x : A) → B x → Type ℓ₃}
  → ((p : Σ[ x ∈ A ] B x) → C (p .fst) (p .snd))
  ≃ ((x : A) → (y : B x) → C x y)
-- We don't have to give names to the section and retract proofs at
-- all, if we prefer.
-- Exercise:
curry-≃ = int→equiv Σ-curry Σ-uncurry (λ x → {!!}) (λ x → {!!})

-- mvrnote: put somewhere?
funext-≃ : {A : Type ℓ} {B : A → Type ℓ'}
  → {f g : (a : A) → B a}
  → ((x : A) → f x ≡ g x)
  ≃ (f ≡ g)
funext-≃ = inv→equiv funext funext⁻ (λ _ → refl) (λ _ → refl)

funextP-≃ : {A : Type ℓ} {B : I → Type ℓ'}
  → {f : A → B i0} {g : A → B i1}
  → ((x : A) → PathP B (f x) (g x))
  ≃ PathP (λ i → A → B i) f g
funextP-≃ = inv→equiv funextP funextP⁻ (λ _ → refl) (λ _ → refl)
```

The above examples work because the composite of `to` and `fro` acts
like the identity on any argument.

Another place we'll want to do this is when pulling records apart. The
uniqueness rule for records means that the section and retraction
proofs are trivial.

```
explode-isEquiv : {f : A → B} → isEquiv f ≃ (SectionOf f × RetractOf f)
explode-isEquiv = inv→equiv 
  (λ e → e .section , e .retract) 
  (λ p → isEquivData (p .fst) (p .snd))
  (λ _ → refl)
  (λ _ → refl)

explode-Equiv : (A ≃ B) ≃ (Σ[ f ∈ (A → B)] isEquiv f)
-- Exercise:
explode-Equiv = {!!}
```

In the Lecture 2-X we gave descriptions of ``PathP``s in
various types. The functions involved are also definitional inverses
and so assemble into equivalences in a similar way.

```
-- mvrnote: is orienting these the other direction more natural?
×Path≃Path× : {x y : A × B} →
  (x .fst ≡ y .fst) × (x .snd ≡ y .snd)
  ≃ (x ≡ y)
×Path≃Path× = inv→equiv ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)

-- The same is true when everything is maximally dependent
ΣPath≃PathΣ : {A : I → Type ℓ}
                  {B : (i : I) → (a : A i) → Type ℓ'}
                  {x : Σ[ a ∈ A i0 ] B i0 a}
                  {y : Σ[ a ∈ A i1 ] B i1 a} →
  (Σ[ p ∈ PathP A (x .fst) (y .fst) ]
    (PathP (λ i → B i (p i)) (x .snd) (y .snd)))
  ≃ (PathP (λ i → Σ[ a ∈ A i ] B i a) x y)
ΣPath≃PathΣ = inv→equiv ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)
```

We will not always be so lucky and have definitional inverses to our
functions. For the following you will have to split into cases, like
we did for the function ``isPositive-represents-Bool``.

If the next equivalence doesn't work doesn't work, go back and check
that the definitions of ``Bool→⊤⊎⊤`` and ``⊤⊎⊤→Bool`` you
gave are actually inverses!

```
Bool≃⊤⊎⊤ : Bool ≃ (⊤ ⊎ ⊤)
Bool≃⊤⊎⊤ = inv→equiv Bool→⊤⊎⊤ ⊤⊎⊤→Bool to-fro fro-to
  where
    to-fro : isSection Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
    fro-to x = {!!}
```

The next few are similar.

```
ℤ≃ℕ⊎ℕ : ℤ ≃ (ℕ ⊎ ℕ)
ℤ≃ℕ⊎ℕ = inv→equiv ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ to-fro fro-to
  where
    to-fro : isSection ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
    fro-to x = {!!}

⊎-ump-≃ : (A → C) × (B → C) ≃ (A ⊎ B → C)
⊎-ump-≃ = inv→equiv ⊎-ump-to ⊎-ump-fro to-fro fro-to
  where
    to-fro : isSection ⊎-ump-to ⊎-ump-fro
--  Hint: You will need to case-split on the element of `A ⊎ B`, so
--  you can't use `refl` here immediately.
--  Exercise:
    to-fro f = {!!}

    fro-to : isRetract ⊎-ump-to ⊎-ump-fro
--  Exercise:
    fro-to x = {!!}

∅×≃∅ : (A : Type ℓ) → (∅ × A) ≃ ∅
∅×≃∅ A = inv→equiv (∅×-to A) (∅×-fro A) to-fro fro-to
  where
    to-fro : isSection (∅×-to A) (∅×-fro A)
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract (∅×-to A) (∅×-fro A)
--  Exercise:
    fro-to x = {!!}

Torus≃S¹×S¹ : Torus ≃ S¹ × S¹
Torus≃S¹×S¹ = inv→equiv Torus→S¹×S¹ S¹×S¹→Torus to-fro fro-to
  where
    to-fro : isSection Torus→S¹×S¹ S¹×S¹→Torus
--  Exercise:
    to-fro c = {!!}

    fro-to : isRetract Torus→S¹×S¹ S¹×S¹→Torus
--  Exercise:
    fro-to t = {!!}
```

All our type formers can be shown to respect equivalences, so that
equivalent inputs give equivalent outputs. This is harder to show for
some types than others, so we'll have to come back to them, but the
following few just involve rearranging the input data in simple ways.
For these, it is best to not use the ``inv→equiv`` helper: the input
equivalences have different sections and retracts, and so we should
combine these to produce separate sections and retracts for the output
equivalence.

```
-- mvrnote: make f/g vs e₁/e₂ consistent
×-map-≃ : (A ≃ A') → (B ≃ B') → (A × B) ≃ (A' × B')
×-map-≃ {A = A} {A' = A'} {B = B} {B' = B'} f g = packEquiv to sec to-fro ret fro-to
  where
    to : A × B → A' × B'
    to = ×-map (f .map) (g .map)

    sec : A' × B' → A × B
--  Exercise:
    sec (a' , b') = {!!}

    ret : A' × B' → A × B
--  Exercise:
    ret (a' , b') = {!!}

    to-fro : isSection to sec
--  Exercise:
    to-fro (a' , b') = {!!}

    fro-to : isRetract to ret
--  Exercise:
    fro-to (a , b) = {!!}

→-map-≃ : (A ≃ B) → (C ≃ D) → (B → C) ≃ (A → D)
→-map-≃ {A = A} {B = B} {C = C} {D = D} e₁ e₂ = packEquiv to sec to-fro ret fro-to
  where
    to : (B → C) → (A → D)
    to f a = e₂ .map (f (e₁ .map a))

    sec : (A → D) → (B → C)
--  Exercise:
    sec g b = {!!}

    ret : (A → D) → (B → C)
--  Exercise:
    ret g' b = {!!}

    to-fro : isSection to sec
--  Exercise:
    to-fro g = {!!}

    fro-to : isRetract to ret
--  Exercise:
    fro-to f = {!!}

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

⊎-map-≃ : (A ≃ A') → (B ≃ B') → (A ⊎ B) ≃ (A' ⊎ B')
⊎-map-≃ {A = A} {A' = A'} {B = B} {B' = B'} f g = packEquiv to sec to-fro ret fro-to
  where
    to : A ⊎ B → A' ⊎ B'
    to = ⊎-map (f .map) (g .map)

    sec : A' ⊎ B' → A ⊎ B
--  Exercise:
    sec t = {!!}

    ret : A' ⊎ B' → A ⊎ B
--  Exercise:
    ret t = {!!}

    to-fro : isSection to sec
--  Exercise:
    to-fro t = {!!}

    fro-to : isRetract to ret
--  Exercise:
    fro-to t = {!!}
```

Equivalences do not necessarily go between different types. A type can
be equivalent to itself in a non-trivial way!

```
not-≃ : Bool ≃ Bool
not-≃ = inv→equiv not not to-fro fro-to
  where
    to-fro : isSection not not
--  Exercise:
    to-fro x = {!!}

    fro-to : isSection not not
--  Exercise:
    fro-to x = {!!}

sucℤ-≃ : ℤ ≃ ℤ
-- Exercise:
sucℤ-≃ = inv→equiv sucℤ {!!} {!!} {!!}
```


## Path Algebra

In the last lecture we saw what could be done with paths using only
the fact that they are functions `I → A`. In this lecture, we'll
introduce some more axioms for the interval which will let us prove
more.

So far, we have only used that the interval has endpoints ``i0`` and
``i1``. But the actual unit interval $[0, 1]$ has a lot more structure
than just its endpoints. We'll add axioms to ``I`` that corresponds to
this structure, and those operations on ``I`` will lead to new
operations on ``Path``s.

First, there is the function $r(x) = 1 - x : [0, 1] → [0, 1]$ that
reverses the interval. If $p : [0, 1] → S$ is a path in the space $X$
from $p(0)$ to $p(1)$, then $p ∘ r : [0, 1] → X$ is a path in $X$ from
$p(1)$ to $p(0)$ --- since $(p ∘ r)(0) = p(1)$ and $(p ∘ r)(1) = p(0)$.

Cubical Agda has a primitive operation on elements of the interval:
`~_ : I → I`, which we think of as reversal, and by definition it
holds that `~ i0 = i1` and `~ i1 = i0`. You can test this by
normalising `~ i0` via `C-c C-n`.

We can use this operation to reverse a path.

```
sym : x ≡ y → y ≡ x
sym p i = p (~ i)
```

And we can upgrade this principle to also apply to ``PathP``s. We have
to flip the path of types `A` too, so that the endpoints lie in the
correct types.

```
symP : {A : I → Type ℓ} → {x : A i0} → {y : A i1}
  → PathP A x y
  → PathP (λ i → A (~ i)) y x
symP p j = p (~ j)
```

Now, there's a evident question we can ask: what happens if we flip a
path twice? Agda takes it as an axiom that `~ (~ i) = i`, so the
answer is that we get the same path again by definition.

```
symP-inv : (p : PathP _ x y) → symP (symP p) ≡ p
symP-inv p = refl
```

And so ``symP`` is an equivalence.

```
symP-≃ : {A : I → Type ℓ} → {x : A i0} → {y : A i1}
  → PathP A x y ≃ PathP (λ i → A (~ i)) y x
symP-≃ = inv→equiv symP symP symP-inv symP-inv
```

To define some interesting ``Square``s, we'll axiomatize some more
structure from the unit interval $[0, 1]$. Mathematically, the
functions $\max, \min : [0, 1] × [0, 1] → [0, 1]$ are quite useful for
constructing homotopies: if $p : [0, 1] → X$ is a path in $X$, then $p
∘ \max$ is a homotopy between $p$ and the constant path at $p(1)$,
because $p(\max(0, i)) = p(i)$ and $p(\max(1, i)) = p(1)$. For similar
reasons, $p ∘ \min$ is a homotopy between the constant path at $p(0)$
and $p$.

We will axiomatize these with two more in-built interval operations
``∨`` and ``∧``, for $\max$ and $\min$ respectively. Agda computes the
values of ``∨`` and ``∧`` when either side is known to be an endpoint
``i0`` or ``i1``.

Uncomment this block and try normalising the following expressions.

```
{-
_ : I
_ = {! i0 ∨ i0 !}

_ : I
_ = {! i0 ∨ i1 !}

_ : I
_ = {! i0 ∧ i0 !}

_ : I
_ = {! i0 ∧ i1 !}
-}
```

There are a few additional equalities which hold for $\max$ and $\min$
that Agda makes true for ``∧`` and ``∨``. (You don't have to memorise
these.)

* Top and Bottom:
  $$
  \begin{align*}
  i0 ∧ j &= i0   &  i0 ∨ j &= j \\
  i1 ∧ j &= j    &  i1 ∨ j &= i1
  \end{align*}
  $$
* Idempotence:
  $$
  \begin{align*}
  i ∧ i &= i     & i ∨ i &= i
  \end{align*}
  $$
* Commutativity:
  $$
  \begin{align*}
  i ∧ j &= j ∧ i & i ∨ j &= j ∨ i
  \end{align*}
  $$
* Associativity:
  $$
  \begin{align*}
  (i ∧ j) ∧ k &= i ∧ (j ∧ k) & (i ∨ j) ∨ k &= i ∨ (j ∨ k)
  \end{align*}
  $$
* Distributivity:
  $$
  \begin{align*}
  i ∧ (j ∨ k) &= (i ∧ j) ∨ (i ∧ k) & i ∨ (j ∧ k) &= (i ∨ j) ∧ (i ∨ k)
  \end{align*}
  $$
* Symmetry:
  $$
  \begin{align*}
  ∼ (∼ i) &= i
  \end{align*}
  $$
* The De Morgan Laws:
  $$
  \begin{align*}
  ∼ (i ∧ j) &= (∼ i) ∨ (∼ j) & ∼ (i ∨ j) = (∼ i) ∧ (∼ j)
  \end{align*}
  $$

::: Aside:
For a pen-and-paper exercise: Convince yourself that all of these
axioms are true for the actual unit interval $[0, 1]$ where `∨ = max`,
`∧ = min`, and `~ i = 1 - i`.
:::

These laws make the interval ``I`` into an algebraic structure known
as a *De Morgan algebra*. We saw a version of the "De Morgan laws"
earlier for types when we proved ``DeMorgan-law-1``,
``DeMorgan-law-2`` and ``DeMorgan-law-3``. Unlike for types, the
algebra on the interval also satisfies the missing fourth law which we
mentioned there.

::: Aside:
De Morgan was a British mathematician and contemporary of Boole (from
whom we get *Boolean algebra* and the name of the type ``Bool``).
He was the first to state the laws which have his name, coined the
term "mathematical induction" and was the first to formally state the
induction principle for natural numbers. De Morgan, like Boole, was
concerned with turning logic into algebra.
:::

We can use the De Morgan algebra structure ``∨`` and ``∧`` to build
some squares that were unavailable to us before. The following two are
called *connections*. The way we are drawing these, the arguments to
``Square`` are `Square left right bottom top`.

             p
         x — — — > y
         ^         ^                  ^    
    refl |         | p              j |    
         |         |                  ∙ — >
         x — — — > x                    i  
            refl                  
```
connection∧ : (p : x ≡ y) → Square refl p refl p
connection∧ p i j = p (i ∧ j)
```

          refl
       y — — — > y
       ^         ^                    ^     
     p |         | refl             j |     
       |         |                    ∙ — > 
       x — — — > y                      i   
           p                     
```
connection∨ : (p : x ≡ y) → Square p refl p refl
connection∨ p i j = p (i ∨ j)
```

Below we have drawn some more squares for you to fill in as practice.

           p⁻¹
       y — — — > x
       ^         ^                    ^    
     p |         | refl             j |           
       |         |                    ∙ — >       
       x — — — > x                      i         
          refl                  

```
connectionEx1 : (p : x ≡ y) → Square p refl refl (sym p)
-- Exercise:
connectionEx1 p i j = {!!}
```

            p
        x — — — > y
        ^         ^                   ^    
    p⁻¹ |         | refl            j |    
        |         |                   ∙ — >
        y — — — > y                     i  
           refl                   

```
connectionEx2 : (p : x ≡ y) → Square (sym p) refl refl p
-- Exercise:
connectionEx2 p i j = {!!}
```

As an immediate application of connections, we can show that the
``ℤ→ℤˢ`` and ``ℤˢ→ℤ`` maps we defined earlier are an
equivalence. You will need to use a connection in the case for
``zeroˢ≡``.

```
ℤ≃ℤˢ : ℤ ≃ ℤˢ
ℤ≃ℤˢ = inv→equiv ℤ→ℤˢ ℤˢ→ℤ to-fro fro-to
  where
    to-fro : isSection ℤ→ℤˢ ℤˢ→ℤ
--  Exercise:
    to-fro z = {!!}

    fro-to : isRetract ℤ→ℤˢ ℤˢ→ℤ
--  Exercise:
    fro-to z = {!!}
```

::: Aside:
When you reach the `to-fro (zeroˢ≡ i)` case, the goal should look
like:

    Goal: posˢ zero ≡ zeroˢ≡ i
    ———— Boundary (wanted) —————————————————————————————————————
    i = i0 ⊢ λ i₁ → posˢ zero
    i = i1 ⊢ zeroˢ≡
    ————————————————————————————————————————————————————————————
    i : I

This is asking us for a path between paths, i.e. a square, but it is a
little difficult to read in that form. If you accept an additional
argument `j` (by adding it manually or pressing `C-c C-c`), the goal
becomes

    Goal: ℤˢ
    ———— Boundary (wanted) —————————————————————————————————————
    j = i0 ⊢ posˢ zero
    j = i1 ⊢ zeroˢ≡ i
    i = i0 ⊢ posˢ zero
    i = i1 ⊢ zeroˢ≡ j
    ————————————————————————————————————————————————————————————
    j : I
    i : I

which tells us exactly what square we need to construct.
:::


## References and Further Reading
https://arxiv.org/pdf/2408.11501

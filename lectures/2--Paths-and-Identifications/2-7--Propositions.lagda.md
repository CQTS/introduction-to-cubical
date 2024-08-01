
```
module 2--Paths-and-Identifications.2-7--Propositions where
```


# Lecture 2-7: Propositions

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport

private
  variable
    ℓ ℓ' : Level
    A B P : Type ℓ
    x y z : A
```
-->

In Lecture 1-3, we saw how we can use types to represent propositions.
But not all types have a sensible interpretation as propositions: an
element of ``ℕ`` in some sense contains more information than the
fact of a proposition being true. How can we characterise which types
should be thought of as propositions?


## Contractible Types

A singleton is a type consisting of exactly one element. In ordinary
set theory, if $a$ is an element of a set $A$, then the singleton
subset containing $a$ is $\{ a \}$, which we could write more
pedantically as the set $\{ x ∈ A ∣ a = x \}$. This is the notion of
singleton we are going to use as our definition of singletons in type
theory. For an element of a type `a : A`, the singleton type at `a`
is:

```
singl : {A : Type ℓ} → (a : A) → Type ℓ
singl {A = A} a = Σ[ x ∈ A ] a ≡ x
```

There is a unique element of `singl a`, namely the pair `(a, refl)`
which says that `a` is identical to itself.

```
singlBase : (a : A) → singl a
singlBase a = (a , refl)
```

We would like to say in type theory that `singl a` has a unique
element, so we need a way of expressing "has a unique element"
type-theoretically. For this, we use:

```
∃! : Type ℓ → Type ℓ
∃! A = Σ[ x ∈ A ] ((y : A) → x ≡ y)
```

So, to give a proof of `∃! A` we give an element `x : A` and a
function assigning to every `y : A` a path `x ≡ y`. In other words,
`A` has a unique element, and all elements of `A` are equal to it.

Homotopically speaking, this means that the type `A` *contracts onto
the point `x`*. If we have an element of `∃! A` we say that `A` is
*contractible*. This terminology is more common in homotopy type
theory, so we record it here as well.

```
isContr : Type ℓ → Type ℓ
isContr A = ∃! A

center : isContr A → A
center c = fst c

contraction : (c : isContr A) (a : A) → center c ≡ a
contraction c = snd c
```

We should expect that singletons should be have a unique element,
which is to say that singletons should be contractible.

```
isContrSingl : (a : A) → isContr (singl a)
-- Exercise: (Hint: You will need a connection square.)
isContrSingl a = {!!}
```

The type ``⊤`` was defined to have only the single element
``tt``, so it is easy to show it is contractible.

```
isContr⊤ : isContr ⊤
-- Exercise:
isContr⊤ = {!!}
```

On the other hand, ``∅`` is not contractible: it doesn't have any
elements at all.

```
¬isContr∅ : ¬ isContr ∅
-- Exercise:
¬isContr∅ = {!!}
```

And neither is ``Bool``, because it does not have a unique
element:

```
¬isContrBool : ¬ isContr Bool
-- Exercise: (Hint: `true≢false`.)
¬isContrBool (x , p) = {!!}
```

But there are data-types other than `⊤` that we can show are
contractible. As a somewhat contrived example, consider the type
defined by

```
data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one
```

This interval contains no interesting information at all:

```
isContrInterval : isContr Interval
isContrInterval = (zero , contr)
  where
  contr : (x : Interval) → zero ≡ x
  contr zero      = refl
  contr one       = seg
  contr (seg i) j = connection∧ seg i j
```

::: Aside:
This ``Interval`` is an ordinary type, in contrast to the
built-in interval ``I``. We can therefore use it like any other
type; form functions into it, look at paths in it, and so on. It does
not contain any of the magic that ``I`` does, however, so we
can't make a corresponding ``Path`` or ``hcomp``.
:::

Any two contractible types are equivalent.

```
isContr→Equiv : isContr A → isContr B → A ≃ B
-- Exercise:
isContr→Equiv c c' = {!!}
```

So, in fact, every contractible type is equivalent to ``⊤``.

```
isContrEquiv⊤ : isContr A → A ≃ ⊤
isContrEquiv⊤ c = isContr→Equiv c isContr⊤
```

The converse is true: if `A` is equivalent to ``⊤``, then `A` is
contractible. To prove this, we will use an argument that we will
repeat, with variations, in a couple of other proofs in this section.

Many properties of types are preserved by equivalences, but it turns
out that often just half of the data of an equivalence is enough. We
say a map *is* a retraction when it *has* a section.

```
_RetractionOnto_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
B RetractionOnto A = Σ[ r ∈ (B → A) ] sectionOf r
```

Certainly `A` is equivalent to `B` then `B` retracts onto `A`, just
forgetting the other part of an equivalence.

```
equivRetracts : {A : Type ℓ} {B : Type ℓ'} → (A ≃ B) → B RetractionOnto A
equivRetracts e = equivRet e , equivFun e , equivIsRet e
```

Now if ``⊤`` retracts onto `A`, then `A` is contractible.

```
Retract⊤IsContr : ⊤ RetractionOnto A → isContr A
-- Exercise:
Retract⊤IsContr (r , (s , p)) = ?

Equiv⊤IsContr : (A ≃ ⊤) → isContr A
-- Exercise:
Equiv⊤IsContr = {!!}
```

mvrnote: Move to extras? There is a unique map from ``∅`` to any type.

```
¬-isEquiv : (f : A → ∅) → isEquiv f
fst (fst (¬-isEquiv f)) ()
snd (fst (¬-isEquiv f)) ()
fst (snd (¬-isEquiv f)) ()
snd (snd (¬-isEquiv f)) a = ∅-rec (f a)

¬→≃∅ : ¬ A → (A ≃ ∅)
¬→≃∅ ¬a = _ , ¬-isEquiv ¬a

∅-rec-unique : isContr (∅ → A)
-- Exercise:
∅-rec-unique = {!!}
```

As a final, slightly trickier exercise for contractibility, show that
path types in a contractible type are always contractible themselves.
This will involve an ``hcomp`` in both components.

mvrnote: draw the square and cube?

```
isContr→isContr≡ : (c : isContr A) → (a b : A) → isContr (a ≡ b)
-- Exercise:
fst (isContr→isContr≡ (c , h) a b) = {!!}
snd (isContr→isContr≡ (c , h) a b) = {!!}
```


## Propositions

When thinking of a type `A` as a proposition, an element `a : A` is a
witness to the fact that the proposition `A` is true. For propositions
we only care about whether `A` has an element at all, whereas for
ordinary data-types it matters which particular element we have.

We turn this observation into a definition: propositions are types
which have *at most* one element. In other words, a type is a
proposition when we can give a path between any two elements.

```
isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y
```

mvrnote: where does this go?

```
Prop : (ℓ : Level) → Type (ℓ-suc ℓ)
Prop ℓ = Σ[ X ∈ Type ℓ ] isProp X
```

The type ``⊤`` is contractible and represents a proposition with
a proof ``tt`` --- truth.

```
isProp⊤ : isProp ⊤
-- Exercise:
isProp⊤ = {!!}
```

As we saw in Lecture 1-3, ``∅`` represents the proposition with
no proof --- falsity. If a type has no elements at all then it
certainly has at most one element:

```
isProp∅ : isProp ∅
-- Exercise:
isProp∅ = {!!}
```

Using these two facts, we can show that the equality relations defined
in Lecture 1-3 are all propositions.

```
isProp-≡Bool : (a b : Bool) → isProp (a ≡Bool b)
isProp-≡Bool true true = isProp⊤
isProp-≡Bool true false = isProp∅
isProp-≡Bool false true = isProp∅
isProp-≡Bool false false = isProp⊤

isProp-≡ℕ : (n m : ℕ) → isProp (n ≡ℕ m)
-- Exercise:
isProp-≡ℕ n m = {!!}
```

Contractible types may be thought of as types with a unique element.
Of course, a type with *exactly* one element also has *at most* one
element, so contractible types are also propositions.

```
isContr→isProp : isContr A → isProp A
-- Exercise:
isContr→isProp (c , h) a b = {!!}
```

The same is not true the other way, of course, as we have just seen
that ``∅`` is a propostion but isn't contractible. In some sense,
not being inhabited is the only thing missing for a proposition to be
contractible: if a proposition has an element then that element is
unique. In other words, if a proposition has a proof then it is
contractible.

```
isProp→with-point-isContr : isProp A → (A → isContr A)
-- Exercise:
isProp→with-point-isContr p = {!!}
```

Conversely, if assuming that a type is inhabited causes it to be
contractible, then that type must be a proposition to being with:

```
with-point-isContr→isProp : (A → isContr A) → isProp A
-- Exercise:
with-point-isContr→isProp c = {!!}
```

Of course, the point of having a definition like ``isProp`` is
that not all types are propositions. Use ``true≢false`` to show
that ``Bool`` is not a proposition, and similarly for ``ℕ``.

```
¬isPropBool : ¬ isProp Bool
-- Exercise:
¬isPropBool pBool = {!!}

¬isPropℕ : ¬ isProp ℕ
-- Exercise:
¬isPropℕ pℕ = {!!}
```

If two propositions imply each other, then they are in fact
equivalent. This is known as "proposition extensionality".

```
propExt : isProp A → isProp B
        → (A → B) → (B → A)
        → A ≃ B
-- Exercise:
propExt pA pB f g = equiv f g {!!} {!!}
```


## Being a Proposition is a Proposition

The fact of being contractible is a proposition. That is, `isContr A`
is a proposition for any type `A`: it is the proposition that `A` has
a unique element.

The proof is a bit tricky. Suppose we have two elements `(c0, h0)` and
`(c1, h1)` of `isContr A`, seeking to give a path `(c0, h0) ≡ (c1, h1)`.
Because these are pairs, it suffices to give two paths, one in the first
component and the other in the second component lying over the first.
(We are basically inlining ``ΣPathP→PathPΣ`` in the following
definition.)

```
isPropIsContr : isProp (isContr A)
fst (isPropIsContr (c0 , h0) (c1 , h1) j) = h0 c1 j
```

For the first component, we use one of the witnesses of
contractibility to get `h0 c1 : c0 ≡ c1`. For the second, we need to
construct a path-over showing that for any `y : A` we have
"`h0 y ≡ h1 y1` over `h0 c1'". This is the square on the top of the
following cube:

                       h1 y
               c1 - - - - - - - - > y
              / ^                 / ^
     h0 c1  /   |               /   |
          /     | h0 y        /     |
       c0 - - - - - - - - > y       |
        ^       |           ^       | h0 y               ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |      c0 - - - - - | - - > c0
        |     /             |     /
        |   /               |   /
        | /                 | /
       c0 - - - - - - - - > c0

mvrnote: experiment:
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXG1hdGh0dHtjMX0iXSxbMywwLCJcXG1hdGh0dHt5fSJdLFswLDEsIlxcbWF0aHR0e2MwfSJdLFsyLDEsIlxcbWF0aHR0e3l9Il0sWzAsMywiXFxtYXRodHR7YzB9Il0sWzIsMywiXFxtYXRodHR7YzB9Il0sWzEsMiwiXFxtYXRodHR7YzB9Il0sWzMsMiwiXFxtYXRodHR7YzB9Il0sWzAsMSwiXFxtYXRodHR7aDF9XFwsIFxcbWF0aHR0e3l9Il0sWzIsMywiXFxtYXRodHR7aDB9XFwsIFxcbWF0aHR0e3l9IiwwLHsibGFiZWxfcG9zaXRpb24iOjcwfV0sWzMsMSwiXFxtYXRodHR7eX0iLDAseyJsYWJlbF9wb3NpdGlvbiI6NDB9XSxbMiwwLCJcXG1hdGh0dHtoMH1cXCwgXFxtYXRodHR7YzF9IiwwLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzQsMl0sWzUsM10sWzYsMF0sWzUsN10sWzQsNl0sWzQsNV0sWzYsN10sWzcsMV1d&embed" width="560" height="560" style="border-radius: 8px; border: none;"></iframe>

To fill this square, use an ``hcomp`` on the open box depicted
above. The bottom of this box will be constant at c0, while the sides
will be filled in using `h0` and `h1`.

```
-- Exercise:
snd (isPropIsContr (c0 , h0) (c1 , h1) j) y i = {!!}
```

Similarly, `isProp A` is itself a proposition, which we can show using
another cube. The key fact is that in a proposition, we can fill any
square at all, regardless of what the sides are.

As a warmup,  about paths `B : I → Prop` of propositions is that
we also have a ``PathP`` between any two elements of the endpoints.

```
isProp→Square : isProp A
             → {a b c d : A}
             → (r : a ≡ c) (s : b ≡ d)
             → (t : a ≡ b) (u : c ≡ d)
             → Square t u r s
-- Exercise:
isProp→SquareP isPropA {a = a} r s t u i j = {!!}

isPropIsProp : isProp (isProp A)
-- Exercise:
isPropIsProp isProp1 isProp2 i a b
     = isProp→Square {!!} {!!} {!!} {!!} {!!} i
```

We also state that fact about squares in full, painful generality,
because we will need to use it later. mvrnote: can we remove its use later?

As a warmup, show that for any line of propositions, we can produce a
path-over that line between any endpoints.

```
isProp→PathP : {A : I → Type ℓ} → ((i : I) → isProp (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
-- Exercise:
isProp→PathP {A = A} hB a0 a1 = {!!}
```

And now extend this to squares of propositions. You may want to go
back to the definition of ``toPathP``, you will need to use a
similar ``hcomp``.

mvrnote: too hard?

```
isProp→SquareP : {A : I → I → Type ℓ} → ((i j : I) → isProp (A i j))
               → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}

               → (r : PathP (λ j → A j i0) a c) (s : PathP (λ j → A j i1) b d)
               → (t : PathP (λ j → A i0 j) a b) (u : PathP (λ j → A i1 j) c d)
               → SquareP A t u r s
-- Exercise:
isProp→SquareP {A = A} isPropB {a = a} r s t u i j = {!!}
```


mvrnote: we can't do this until we have covered bijections
There's one more important type that is a proposition: the fact that a
map is an equivalence.


## Paths in Propostions are Contractible

mvrnote: being a proposition is the same as paths being contractible
Strategy from egbert:

```
isFaithful : (A → B) → Type _
isFaithful {A = A} f = (x y : A) → isEquiv {A = x ≡ y} (cong f)

-- mvrnote: todo
-- isEquiv→isFaithful : {f : A → B} → isEquiv f → isFaithful f
-- isEquiv→isFaithful e x y = {!!}

with-point-Faithful→Faithful : (f : A → B) → (A → isFaithful f) → isFaithful f
with-point-Faithful→Faithful f g x y = g x x y
```


## Closure Properties

Propositions are closed under most of our usual type operations. As we
saw in Lecture 1-3, when we use ordinary type formers on propositions,
the result is often the logical version of that operation.

First, we have implication. If `A` and `B` are propositions then the
type of functions `A → B` is a proposition --- namely, the proposition
that `A` implies `B`.

```
isProp→ : isProp B → isProp (A → B)
-- Exercise:
isProp→ p f g i a = {!!}
```

This can be extended to dependent functions. If `B : A → Type` is a
family of propositions depending on `A`, then the type of functions
`(a : A) → B a` is a proposition; specifically, the proposition that
"for all `a : A`, the proposition `B a` holds".

```
isPropΠ : {A : Type ℓ} {B : A → Type ℓ'}
        → (p : (a : A) → isProp (B a))
        → isProp ((a : A) → B a)
-- Exercise:
isPropΠ p f g = {!!}
```

As a special case of implication, we find that type negation `¬ A` is
always a proposition even when `A` itself isn't, since we made the
definition `¬ A = A → ∅`.

```
isProp¬ : isProp (¬ A)
isProp¬ = isProp→ isProp∅
```

If `B` is true, then `A → B` is always true. Considering true
propositions as contractible types, this means that `A → B` is
contractible as soon as `B` is contractible.

More generally, if `B : A → Type` is a family of contractible types
depending on `A`, then the type `(a : A) → B a` of functions is
contractible.

```
isContrΠ : {A : Type ℓ} → {B : A → Type ℓ'}
         → ((a : A) → isContr (B a))
         → isContr ((a : A) → B a)
-- Exercise:
fst (isContrΠ c) = {!!}
snd (isContrΠ c) f i a = {!!}

isContr→ : isContr B → isContr (A → B)
isContr→ p = isContrΠ (λ _ → p)
```

The "and" of two propositions `A` and `B` is the type of pairs `A × B`.

```
isProp× : isProp A → isProp B → isProp (A × B)
-- Exercise:
isProp× pA pB = {!!}
```

The upgraded, dependent version of this states that if `A` is a
proposition and `B : A → Type` is a family of propositions depending
on `a : A` then the type of pairs `Σ[ a ∈ A ] B a` is also a
proposition. Really, `Σ[ a ∈ A ] B a` still represents the proposition
"`A` and `B`" --- but we can use it in a situation where the
proposition `B` only makes sense if `A` is already true.

```
isPropΣ : {A : Type ℓ} {B : A → Type ℓ'}
        → isProp A
        → ((a : A) → isProp (B a))
        → isProp (Σ[ a ∈ A ] B a)
-- Exercise: (Hint: use `isProp→PathP`.)
isPropΣ pA pB (a1 , b1) (a2 , b2) i = {!!}
```

And if `A` and `B` are true (contractible), then `A × B` should also be
contractible.

```
isContr× : isContr A → isContr B → isContr (A × B)
-- Exercise:
fst (fst (isContr× (cA , hA) (cB , hB))) = {!!}
snd (fst (isContr× (cA , hA) (cB , hB))) = {!!}
fst (snd (isContr× (cA , hA) (cB , hB)) (a , b) i) = {!!}
snd (snd (isContr× (cA , hA) (cB , hB)) (a , b) i) = {!!}
```

The same is true for Σ-types. If `A` is contractible and `B : A →
Type` is a type family where each type is also contractible, then the
entire Σ-type is contractible. This is similar to the `×` case, but
will require a ``transp`` in the last component.

```
isContrΣ : {B : A → Type ℓ} → isContr A → ((x : A) → isContr (B x)) → isContr (Σ A B)
-- Exercise:
fst (fst (isContrΣ (c , h) q)) = {!!}
snd (fst (isContrΣ (c , h) q)) = {!!}
fst (snd (isContrΣ (c , h) q) (a , b) i) = {!!}
snd (snd (isContrΣ {B = B} (c , h) q) (a , b) i) = {!!}
```

In fact, needing each type in the family to be contractible is more
than is necessary: it's enough for the type over the center of
contraction of `A` to be contractible.

```
isContrΣ' : {B : A → Type ℓ} → (ca : isContr A) → isContr (B (fst ca)) → isContr (Σ A B)
-- Exercise: (Hin: Use `subst` to move the proof `cB` around)
isContrΣ' cA cB = isContrΣ {!!} {!!}
```

For contractibility, the converse of `isContr×` holds: if the product
is contractible then the inputs must have been.

```
isContr×-conv : isContr (A × B) → isContr A × isContr B
-- Exercise:
isContr×-conv cAB = {!!}
```

By contrast, disjoint unions of contractible types are not
contractible, and similarly for propositions. We have already seen an
example of this: we showed in ``¬isPropBool`` that ``Bool``
is not a proposition, and we previous established via
``Bool-⊤⊎⊤-≃`` that ``Bool`` is equivalent to the disjoint
union `⊤ ⊎ ⊤`.

```
¬isProp⊤⊎⊤ : ¬ isProp (⊤ ⊎ ⊤)
-- Exercise:
¬isProp⊤⊎⊤ = {!!}
```

But! If we know that two propositions are mutually exclusive, then
their disjoint union is still a proposition.

```
isPropExclusive⊎ : isProp A → isProp B → ¬ (A × B) → isProp (A ⊎ B)
-- Exercise:
isPropExclusive⊎ pA pB dis x y = {!!}
```

If `B' retracts onto `A`, then in some sense `A` is a continuous
shrinking of `B`. And so if `B` is a proposition then `A` must be
too:

```
isPropRetract : B RetractionOnto A → isProp B → isProp A
-- Exercise:
isPropRetract (r , s , p) isPropB x y i = {!!}
```

In particular, any type equivalent to a proposition is also a
propositon.

```
isPropEquiv : A ≃ B → isProp B → isProp A
-- Exercise:
isPropEquiv = {!!}
```

And the same is true for contractible types:

```
isContrRetract : B RetractionOnto A → isContr B → isContr A
-- Exercise:
isContrRetract (r, s, p) (c , h) = {!!}

isContrEquiv : A ≃ B → isContr B → isContr A
isContrEquiv = isContrRetract ∘ equivRetracts
```

Contrary to contractibility, a product of types being a proposition
does not imply that the two components are.

```
¬isProp×-conv : ¬ ((A B : Type) → isProp (A × B) → isProp A × isProp B)
-- Exercise: (Hint: ∅)
¬isProp×-conv = {!!}
```

mvrnote: remove?
```
isProp→≃Diag : isProp A → isEquiv (λ a → a , a)
-- Exercise:
isProp→≃Diag pA = ?

≃Diag→isProp : sectionOf (λ a → a , a) → isProp A
-- Exercise:
≃Diag→isProp (g , s) = {!!}
```

mvrnote: more possible exercises from the HoTT book:
Exercise 3.4. Show that A is a mere proposition if and only if A → A is contractible.
Exercise 3.9. Show that if LEM holds, then the type Prop :≡ ∑(A:U) isProp(A) is equivalent to 2.


## Subtypes

With our definition of proposition, we can define a good notion of
"subtype". If `B : A → Type` is a family of propositions on a type
`A`, then the *subtype* of `A` carved out by `B` is simply the type of
pairs `Σ[ a ∈ A ] B a`. So, an element of the subtype is pair `(a , b)` of an
`a : A` and a witness `b : B a` that `B` is true about `a`.

mvrnote: good examples?

The main fact to prove about subtypes is that they have the same paths
as the types they came from. That is, `(a1 , b1) ≡ (a2 , b2)` is
equivalent to `a1 ≡ a2` whenever `B` is a family of propositions. To
foreshadow a little mvrnote: link, this is extremely useful when we
start looking at algebraic structures such as groups, rings, and so
on. These come with some data, like addition and multiplcation
operators, together with a bunch of axioms, like associativity,
commutativity, and so on. The lemma we prove tells us that to build a
path between two groups, it's enough to build a path just between the
underlying data, ignoring all the axioms.


mvrnote: exercise is too annoying?

```
≡Subtype : {A : Type ℓ} {B : A → Type ℓ'}
           (p : (a : A) → isProp (B a))
           (x y : Σ[ a ∈ A ] B a)
         → (fst x ≡ fst y) ≃ (x ≡ y)
≡Subtype {A = A} {B = B} p x y = equiv to (cong fst) to-fro fro-to
  where
    to : fst x ≡ fst y → x ≡ y
    -- Exercise: (Hint: `isProp→PathP`)
    fst (to e i) = {!!}
    snd (to e i) = {!!}

    to-fro : isSection to (cong fst)
    -- Exercise: (Hint: `isProp→SquareP`)
    fst (to-fro e i j) = {!!}
    snd (to-fro e i j) = {!!}

    fro-to : isRetract to (cong fst)
    fro-to e i j = e j
```


## Propositional Truncation

We are still missing two important logical operations, the same two
that we had trouble with back in Lecture 1-3: "exists" and "or". For
these, we use another inductive type: the *propositional truncation*.
This takes any type `A` and forms a proposition `∃ A` --- the
proposition that "there exists some element of A". An element of `∃ A`
will be a proof that `A` has some element, though it won't actually
provide us any particular element of `A`.

We define `∃ A` as an inductive type with two constructors.

```
data ∃_ (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∃ A
  squash : (x y : ∃ A) → x ≡ y

infix 3 ∃_
```

The first, written ``|_|``, says that to prove that there exists
an element in `A`, it suffices to have an actual element of `A`. The
second constructor forces `∃ A` to be a proposition. This is a
recursive constructor (like ``suc`` is for ``ℕ``).

That second constructor is exactly stating that `isProp (∃ A)`.

```
isProp-∃ : isProp (∃ A)
isProp-∃ = squash
```

::: Aside:
In fact, Agda would even let us declare the ``squash``
constructor to have type `isProp (∃ A)`, and realise that this is the
same as asking for a path constructor.
:::

::: Aside:
The usual terminology for propositional truncation in
homotopy type theory is `∥ A ∥`, though this can get confusing if we
are doing mathematics where the same bars denote the norm of a vector
or operator.
:::

The recursion principle for `∃ A` says that to prove that `∃ A`
implies some proposition `P`, it suffices to assume we have an actual
element `a : A` and then prove `P`. That is, given a function `A → P`,
we can get an implication `∃ A → P` whenever `P` is a proposition.

```
∃-rec : (isProp P)
      → (A → P)
      → (∃ A → P)
∃-rec pP f ∣ x ∣ = f x
∃-rec pP f (squash x y i) = pP (∃-rec pP f x) (∃-rec pP f y) i
```

This definition is actually recursive --- we use ``∃-rec`` in its
own definition. If we had given the ``squash`` constructor the
type `(x y : A) → ∣ x ∣ ≡ ∣ y ∣` then we wouldn't be able to recurse
in this way and we wouldn't be able to define ``∃-rec``. Even
worse, with that change we wouldn't even be able to prove that
``∃-rec`` was a proposition.

mvrnote: elimination principle

In fact, all maps into a proposition are of this form, that is,
``∃-rec`` is an equivalence.

```
∃-rec-≃ : (isProp P)
        → (A → P) ≃ (∃ A → P)
-- Exercise: (Use `propExt`!)
∃-rec-≃ = {!!}
```

``∃`` is functorial, that is, if we have a function from `A` to
`B` then `A` having an element implies `B` has an element.

```
∃-map : (A → B) → (∃ A → ∃ B)
-- Exercise:
∃-map f = {!!}
```

If `P` is already a proposition, truncating it should do nothing:

```
isProp→≃∃ : isProp P → P ≃ (∃ P)
-- Exercise: (Hint: use `propExt`)
isProp→≃∃ isPropP = {!!}
```

In particular, truncating twice is the same as truncating once.

```
∃≃∃∃ : (∃ P) ≃ (∃ ∃ P)
∃≃∃∃ = isProp→≃∃ isProp-∃
```

mvrnote: more exercises:

```
∃×∃→∃× : ((∃ A) × (∃ B)) → ∃ (A × B)
∃×∃→∃× (a , b) = ∃-rec isProp-∃ (λ a → ∃-rec isProp-∃ (λ b → ∣ a , b ∣) b) a
```

With propositional truncation, we can finally define the proposition
representing "or" which eluded us in Lecture 1-3. Our guess was that
"or" is represented by `A ⊎ B`, but this is not generally a
proposition even when `A` and `B` are propositions, as we saw in
``¬isProp⊤⊎⊤``.

However, it is true that `A ⊎ B` has some element if and only if `A`
has some element or `B` has some element (or both have elements).
Therefore, we can define `A orP B` as the proposition that there
exists an element in `A ⊎ B`.

```
_orP_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A orP B = ∃ (A ⊎ B)
```

Here's how we can justify that this is the correct definition. First
of all, clearly `A orP B` is always a proposition, via
``isProp-∃``. And, it has the correct universal property with
respect to other propositions: `P orP Q → R` exactly when `P → R` and
`Q → R`.

```
orP-ump-≃ : {P Q R : Type ℓ}
     → isProp P → isProp Q → isProp R
     → (P orP Q → R) ≃ (P → R) × (Q → R)
-- Exercise:
orP-ump-≃ pP pQ pR = {!!}
```

mvrnote: global choice implies excluded middle
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#global-choice

mvrnote: prose

```
¬→¬∃ : ¬ A → ¬ ∃ A
-- Exercise:
¬→¬∃ = {!!}
```

```
¬¬∃≃¬¬ : (¬ ¬ ∃ A) ≃ (¬ ¬ A)
-- Exercise: (Hint: use `propExt`)
¬¬∃≃¬¬ = {!!}
```


## Propositions and Decidability

mvrnote: prose

```
isProp-Dec : {ℓ : Level} {A : Type ℓ} → isProp A → isProp (Dec A)
-- Exercise:
isProp-Dec pA = {!!}

Dec∃≃∃Dec : (Dec (∃ A)) ≃ (∃ (Dec A))
-- Exercise: Hint: use `propExt`
Dec∃≃∃Dec = {!!}

Dec→SplitSupport : Dec A → (∃ A → A)
-- Exercise:
Dec→SplitSupport d = {!!}
```


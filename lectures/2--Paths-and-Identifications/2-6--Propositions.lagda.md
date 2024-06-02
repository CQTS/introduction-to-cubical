
```
module 2--Paths-and-Identifications.2-6--Propositions where
```


# Lecture 2-6: Propositions

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J
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
element of `ℕ`{.Agda} in some sense contains more information than the
fact of a proposition being true. How can we characterise which types
should be thought of as propositions?

## Contractible Types

mvrnote: prose... this section needs some rearrangement. one option is
to merge with the proposition section, another option is to split the
contractible stuff to another file

A singleton is a type consisting of just one element. In set theory,
if $a$ is an element of a set $A$, then the singleton set is $\{a\}$,
which we could write more explicitly as $\{ x ∈ A ∣ a = x \}$. We can
give an analogous definition of singletons in type theory using pair
types.

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
∃! A = Σ[ x ∈ A ] (∀ y → x ≡ y)
```

In words, to give an element of `∃! A` we must give an element `x : A`
and then a function assigning to every `y : A` a path `x ≡ y`. This
means that `A` has a unique element, where we are saying two elements
are the same by virtue of the paths between them.

Homotopically speaking, this means that the type `A` *contracts onto
`x`*. So, if we have an element of `∃! A` we say that `A` is
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

Hint: A square is necessary in the second component, draw it and
complete the definition.

<!--
Super Hint: It's exactly the connection square
             p
         y - - - > y
         ^         ^
    refl |         | p            ^
         |         |            j |
         x — — — > y              ∙ — >
            refl                    i
-->

```
isContrSingl : (a : A) → isContr (singl a)
-- Exercise:
isContrSingl a = ?
```

We show that our type `⊤`{.Agda}, which was defined to have only a
single element `tt`{.Agda}, is contractible.

```
isContr⊤ : isContr ⊤
-- Exercise:
isContr⊤ = ?
```

On the other hand, `∅`{.Agda} is not contractible: it doesn't have any
elements at all.

```
¬isContr∅ : ¬ isContr ∅
-- Exercise:
¬isContr∅ = ?
```

Any two contractible types are isomorphic.

```
isContr→Iso : {A : Type ℓ} {B : Type ℓ'} → isContr A → isContr B → Iso A B
-- Exercise:
isContr→Iso c c' = ?

isContrIso⊤ : {A : Type}  → isContr A → Iso A ⊤
isContrIso⊤ c = isContr→Iso c isContr⊤
```

As a corollary, any contractible type is isomorphic to `⊤`{.Agda}. The
converse is true: if `A` is isomorphic to `⊤`{.Agda}, then `A` is
contractible.

```
Iso⊤IsContr : {A : Type ℓ} → Iso A ⊤ → isContr A
-- Exercise:
Iso⊤IsContr iso = {!!}
```

mvrnote: Move to extras? There is a unique map from `∅`{.Agda} to any type.

```
∅-rec-unique : {A : Type ℓ} → isContr (∅ → A)
-- Exercise:
∅-rec-unique = ?
```

If `B : A → Type` is a family of contractible types depending on `A`,
then the type `(a : A) → B a` of functions is contractible.

```
isContrFun : ∀ {A : Type ℓ} {B : A → Type ℓ}
           → ((a : A) → isContr (B a))
           → isContr ((a : A) → B a)
-- Exercise:
fst (isContrFun c) = ?
snd (isContrFun c) f i a = ?
```

In particular, the map `(λ _. tt) : A → ⊤` (which always exists for
any `A`) is the unique map `A → ⊤`.

As a final exercise for contractibility, show that path types in a
contractible type are always contractible themselves. This will
involve some `hcomp`{.Agda}s.

```
isContrisContr≡ : {A : Type ℓ} (c : isContr A) (a b : A) → isContr (a ≡ b)
-- Exercise:
fst (isContrisContr≡ (c₀ , c) a b) = ?
snd (isContrisContr≡ (c₀ , c) a b) = ?
```

## Aside: Equational Reasoning

We will sometimes produce a path by chaining together several simpler
ones. There is a common pattern that is used to give this process some
nice syntax.

```
infix  3 _∎
infixr 2 step-≡ _≡⟨⟩_

step-≡ : (x : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

syntax step-≡ x y p = x ≡⟨ p ⟩ y

_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_∎ : (x : A) → x ≡ x
_ ∎ = refl
```

Here are some examples of how to use it. mvrnote: 1lab hides the paths, need to switch the default

```
private
  example1 : (w x y z : A)
    → (p : w ≡ x)
    → (q : x ≡ y)
    → (r : y ≡ z)
    → w ≡ z
  example1 w x y z p q r =
    w ≡⟨ p ⟩
    x ≡⟨ q ⟩
    y ≡⟨ r ⟩
    z ∎

  example2 : (f : A → B) (g : B → A)
           → (η : (x : A) → x ≡ g (f x))
           → (ε : (y : B) → f (g y) ≡ y)
           → (x : A) → f x ≡ f x
  example2 f g η ε x =
    f x         ≡⟨ cong f (η x) ⟩
    f (g (f x)) ≡⟨ ε (f x) ⟩
    f x         ∎
```

We encourage you to use this syntax when chaining paths together, it
makes it a lot easier to see what's going on!

## Propositions

Recall that when thinking of a type `A` as a proposition, an element
`a : A` is a witness to the fact that `A` is true. For propositions
`A`, we only care about whether `A` has an element at all, whereas for
data types, it matters which particular element we have. We turn this
observation into a definition: propositions are types which have at
most one element. In other words, a type is a proposition when we can
give a path between any two elements.

```
isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y
```

If a type has no elements at all then it certainly has at most one
element, so we should expect `∅`{.Agda} to be a proposition. As we saw in
Lecture 1-3, `∅`{.Agda} represents the proposition with no proof --- false.

```
isProp∅ : isProp ∅
isProp∅ ()
```

Contractible types may be thought of as types with a unique element.
Of course, a type with exactly one element also at most one element,
so we should expect contractible types to be propositions.

```
isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b =
  a ≡⟨ sym (p a) ⟩
  x ≡⟨ p b ⟩
  b ∎
```

The type `⊤`{.Agda} is contractible and represents a proposition with
a proof `tt`{.Agda} --- truth.

```
isProp⊤ : isProp ⊤
isProp⊤ = isContr→isProp isContr⊤
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
```

The ordering on the natural numbers is also a proposition.

```
isProp-≤ℕ : (n m : ℕ) → isProp (n ≤ℕ m)
isProp-≤ℕ zero m = isProp⊤
isProp-≤ℕ (suc n) zero = isProp∅
isProp-≤ℕ (suc n) (suc m) = isProp-≤ℕ n m
```

Of course, the point of having a definition like `isProp`{.Agda} is
that not all types are propositions. Use `true≢false`{.Agda} to show
that `Bool`{.Agda} is not a proposition.

```
¬isPropBool : ¬ isProp Bool
-- Exercise:
¬isPropBool pBool = ?
```

mvrnote: and do similarly for `ℕ`?

If two propositions imply each other, then they are in fact
isomorphic. This is known as "proposition extensionality". mvrnote:
prose, this is an argument for prop being a good notion? the
particular evidence isn't important.

```
propExt : isProp A → isProp B
        → (A → B) → (B → A)
        → Iso A B
-- Exercise:
propExt pA pB f g = {!!}
```

mvrnote: We could in fact show that `A iffP B` is isomorphic to `Iso A B`.

## Being a Proposition is a Proposition

The fact of being contractible is a proposition. That is, `isContr A`
is a proposition for any type `A`: the proposition that `A` has a
unique element.

The proof is a bit tricky. Suppose we have two elements `(c0, h0)` and
`(c1, h1)` of `isContr A`, seeking to give a path `(c0, h0) ≡ (c1, h1)`.
As these are pairs, it suffices to give two paths, one in the first
component and the other in the second component lying over the first.

```
isPropIsContr : isProp (isContr A)
fst (isPropIsContr (c0 , h0) (c1 , h1) j) = h0 c1 j
```

For the first component, we can use one of the witnesses of
contractibility to get `h0 c1 : c0 ≡ c1`. For the second, then, we
need to construct a path over this showing that for any `y : A` we
have "`h0 y ≡ h1 y1` over `h0 c1'", which is the square on the top of
the following cube:

                       h1 y
               c1 - - - - - - - - > y
              / ^                 / ^
     h0 c1  /   |               /   |
          /     | h0 y        /  y  |
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
<!-- https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXG1hdGh0dHtjMX0iXSxbMywwLCJcXG1hdGh0dHt5fSJdLFswLDEsIlxcbWF0aHR0e2MwfSJdLFsyLDEsIlxcbWF0aHR0e3l9Il0sWzAsMywiXFxtYXRodHR7YzB9Il0sWzIsMywiXFxtYXRodHR7YzB9Il0sWzEsMiwiXFxtYXRodHR7YzB9Il0sWzMsMiwiXFxtYXRodHR7YzB9Il0sWzAsMSwiXFxtYXRodHR7aDF9XFwsIFxcbWF0aHR0e3l9Il0sWzIsMywiXFxtYXRodHR7aDB9XFwsIFxcbWF0aHR0e3l9IiwwLHsibGFiZWxfcG9zaXRpb24iOjcwfV0sWzMsMSwiXFxtYXRodHR7eX0iLDAseyJsYWJlbF9wb3NpdGlvbiI6NDB9XSxbMiwwLCJcXG1hdGh0dHtoMH1cXCwgXFxtYXRodHR7YzF9IiwwLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzQsMl0sWzUsM10sWzYsMF0sWzUsN10sWzQsNl0sWzQsNV0sWzYsN10sWzcsMV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXG1hdGh0dHtjMX0iXSxbMywwLCJcXG1hdGh0dHt5fSJdLFswLDEsIlxcbWF0aHR0e2MwfSJdLFsyLDEsIlxcbWF0aHR0e3l9Il0sWzAsMywiXFxtYXRodHR7YzB9Il0sWzIsMywiXFxtYXRodHR7YzB9Il0sWzEsMiwiXFxtYXRodHR7YzB9Il0sWzMsMiwiXFxtYXRodHR7YzB9Il0sWzAsMSwiXFxtYXRodHR7aDF9XFwsIFxcbWF0aHR0e3l9Il0sWzIsMywiXFxtYXRodHR7aDB9XFwsIFxcbWF0aHR0e3l9IiwwLHsibGFiZWxfcG9zaXRpb24iOjcwfV0sWzMsMSwiXFxtYXRodHR7eX0iLDAseyJsYWJlbF9wb3NpdGlvbiI6NDB9XSxbMiwwLCJcXG1hdGh0dHtoMH1cXCwgXFxtYXRodHR7YzF9IiwwLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzQsMl0sWzUsM10sWzYsMF0sWzUsN10sWzQsNl0sWzQsNV0sWzYsN10sWzcsMV1d&embed" width="560" height="560" style="border-radius: 8px; border: none;"></iframe>

To fill this square, we will use an `hcomp`{.Agda} on the open box
above. The bottom of this box will be constant at c0, while the sides
will be filled in using `h0` and `h1`.

```
snd (isPropIsContr (c0 , h0) (c1 , h1) j) y i =
   hcomp {φ = ∂ i ∨ ∂ j} (λ k →
     λ { (i = i0) → h0 (h0 c1 j) k;  -- We could do h0 c1 (j ∧ k)
         (i = i1) → h0 y k;
         (j = i0) → h0 (h0 y i) k;   -- and h0 y (i ∧ k)
         (j = i1) → h0 (h1 y i) k})
     c0
```

Similarly, `isProp A` is itself a proposition, as we can show using
another cube. The key fact is that in a proposition, you can fill any
square that you want regardless of what the sides are. We state this
in full generality, because we are going to use it later.

mvrnote: exercise?

```
isProp→SquareP : ∀ {A : I → I → Type ℓ} → ((i j : I) → isProp (A i j))
             → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
             → (r : PathP (λ j → A j i0) a c) (s : PathP (λ j → A j i1) b d)
             → (t : PathP (λ j → A i0 j) a b) (u : PathP (λ j → A i1 j) c d)
             → SquareP A t u r s
isProp→SquareP {A = A} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → A i j
    base i j = transport (λ k → A (i ∧ k) (j ∧ k)) a

isPropIsProp : isProp (isProp A)
isPropIsProp isProp1 isProp2 i a b
  = isProp→SquareP (λ _ _ → isProp1) refl refl (isProp1 a b) (isProp2 a b) i
```

mvrnote: prose, one more fact which is used later. does it follow from
something we already have? Where should this go?
```
isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP B b0 b1
isProp→PathP {B = B} hB b0 b1 = toPathP (hB i1 (transp B i0 b0) b1)
```

## Closure Properties

Propositions are closed under most of our usual type operations. In
fact, when we use the ordinary type formers on propositions, the
result is often the logical version of that operation. For example if
`B : A → Type` is a family of propositions depending on `A`, then the
type of functions `(a : A) → B a` is a proposition; specifically, this
is the proposition that "for all `a : A`, the proposition `B a` holds".

```
isPropΠ : {A : Type ℓ} {B : A → Type ℓ'}
            (p : ∀ a → isProp (B a))
          → isProp (∀ a → B a)
-- Exercise:
isPropFun p f g = ?
```

As a special case of this, we get "implies". If `A` and `B` are
propositions, then the type of functions `A → B` is a proposition ---
namely, the proposition that `A` implies `B`.

```
isProp→ : isProp B → isProp (A → B)
isProp→ p = isPropΠ (λ _ → p)
```

If `B` is true, then `A → B` is also true. Thinking of true
propositions as contractible types, this means that `A → B` is
contractible as soon as `B` is contractible.

```
isContr→ : isContr B → isContr (A → B)
-- Exercise:
isContr→ (cB , hB) = ?
```

As a special case of implication, we find that type negation `¬ A` is
always a proposition even when `A` itself isn't, since we defined `¬ A
= A → ∅`.

```
isProp¬ : isProp (¬ A)
isProp¬ = isProp→ isProp∅
```

The "and" of two proposition `A` and `B` is the type of pairs `A × B`.
```
isProp× : isProp A → isProp B → isProp (A × B)
-- Exercise:
isProp pA pB = ?
```

Similarly to `→`, if `A` and `B` are true (contracible), then `A × B` should
also be contractible.

```
isContr× : isContr A → isContr B → isContr (A × B)
-- Exercise:
isContr cA cB = ?
```

For contractibility, the converse holds: if the product is
contractible then the inputs must have been.
```
isContr×-conv : isContr (A × B) → isContr A × isContr B
-- Exercise:
isContr×-conv cAB = ?
```

By contrast, disjoint unions of contractible types are not
contractible, and similarly for propositions. We have seen an example
of this: we just showed in `¬isPropBool`{.Agda} that `Bool`{.Agda} is
not a proposition, and we previous established in
`Bool-⊤⊎⊤-Iso`{.Agda} that `Bool`{.Agda} is equivalent to the disjoint
union `⊤ ⊎ ⊤`.

If we happen to know that two propositions are mutually exclusive,
then their disjoint union is still a proposition.

```
isPropExclusive⊎ : isProp A → isProp B → ¬ (A × B) → isProp (A ⊎ B)
-- Exercise:
isPropExclusive⊎ pA pB disjoint x y = ?
```

If `A` is a retract of `B`, then in some sense `A` is a continuous
shrinking of `B`. And so if `B` is a contractible then `A` must be
too:

```
isPropRetract :
  (f : A → B) (g : B → A)
  → (h : retract f g)
  → isProp B → isProp A
-- Exercise:
isPropRetract f g h isPropB x y i = {!!}
```

In particular, any type equivalent to a proposition is also a
propositon.

```
isPropIso : Iso A B → isProp B → isProp A
isPropIso f pB = isPropRetract (isoFun f) (isoInv f) (isoLeftInv f) pB
```

And the same is true for contractible types:
```
isContrRetract :
    (f : A → B) (g : B → A)
  → (h : retract f g)
  → isContr B → isContr A
-- Exercise
-- fst (isContrRetract f g h (center , contr)) = ?
-- snd (isContrRetract f g h (center , contr)) x = ?
fst (isContrRetract f g h (center , contr)) = g center
snd (isContrRetract f g h (center , contr)) x =
  g center ≡⟨ cong g (contr (f x)) ⟩
  g (f x)  ≡⟨ h x ⟩
  x ∎

isContrIso : Iso A B → isContr B → isContr A
isContrIso f pB = isContrRetract (isoFun f) (isoInv f) (isoLeftInv f) pB
```

Contrary to contractibility, a product of types being a proposition
does not imply that the two components are.

```
¬isProp×-conv : ¬ (∀ (A B : Type) → isProp (A × B) → isProp A × isProp B)
-- Exercise: (Hint: ∅)
¬isProp×-conv = ?
```

mvrnote: prose. the other direction is annoying to state without something like isIso
```
isProp→IsoDiag : isProp A → Iso A (A × A)
-- Exercise:
isProp→IsoDiag pA = ?
```

If a type has at most one element and also has an element, then that
element is unique. In other words, if a proposition has a proof then
it is contractible.

```
Prop-with-point-isContr : Iso (isProp A) (A → isContr A)
-- Exercise: (use propExt)
Prop-with-point-isContr = ?

    fro : (A → isContr A) → isProp A
    fro c x y =
          x         ≡⟨ sym (snd (c x) x) ⟩
          fst (c x) ≡⟨ (snd (c x) y) ⟩
          y         ∎
```

HoTT book:
Exercise 3.4. Show that A is a mere proposition if and only if A → A is contractible.
Exercise 3.9. Show that if LEM holds, then the type Prop :≡ ∑(A:U) isProp(A) is equivalent to 2.

## Subtypes and Predicates

With this definition of proposition, we can define a good notion of
"subtype". If `B : A → Type` is a family of propositions on a type
`A`, then the subtype of `A` carved out by `B` will be the type of
pairs `Σ[ a ∈ A ] B a` whose elements are pairs `(a , b)` where
`a : A` and `b : B a` is a witness that `B` is true about `a`.

Shuffling the data of "a family of propositions" around leads us to
the following definition, which we call a *predicate*
on `A`.

```
isPred : {A : Type ℓ} (B : A → Type ℓ')
        → Type (ℓ-max ℓ ℓ')
isPred {A = A} B =
    (a1 a2 : A) (p : a1 ≡ a2) (b1 : B a1) (b2 : B a2)
  → PathP (λ i → B (p i)) b1 b2
```

A predicate is a type family `B : A → Type` where for any path `p : a1
≡ a2` we can give a path over `p` from `b1 : B a1` to `b2 : B a2`.
This is an equivalent notion to a family of propositions, which we can
show with a little work.

It is not difficult to show we can go from one to the other.

```
isPred→∀isProp : {A : Type ℓ} {B : A → Type ℓ'}
               → isPred B → ∀ a → isProp (B a)
-- Exercise:
isPred→∀isProp p = ?

∀isProp→isPred : {A : Type ℓ} {B : A → Type ℓ'}
               → (∀ a → isProp (B a)) → isPred B
-- mvrnote: does this need a hint?
-- Exercise:
∀isProp→isPred p = ?
```

This lets us easily prove an upgraded, dependent version of
`isProp×`{.Agda}. If `A` is a proposition and `B : A → Type` is a
family of propositions depending on `a : A` (we could think of `B` as
a hypothetical proposition, which only actually exists if `A` is true,
as witnessed by some element `a : A`), then the type of pairs `Σ[ a ∈
A ] B a` is also a proposition. Really, `Σ[ a ∈ A ] B a` represents
"`A` and `B`" - but the proposition `B` only makes sense if `A` is
already true.

```
isPropΣ : {A : Type ℓ} {B : A → Type ℓ'}
          (q : isProp A) (p : ∀ a → isProp (B a))
        → isProp (Σ[ a ∈ A ] B a)
isPropΣ q p (a1 , b1) (a2 , b2) i =
  q a1 a2 i , ∀isProp→isPred p a1 a2 (q a1 a2) b1 b2 i
```

The main lemma to prove about subtypes is that they have the same
paths as the types they came from. That is, `(a1 , b1) ≡ (a2 , b2)` is
equivalent to `a1 ≡ a2` whenever `B` is a family of propositions. To
foreshadow a little, this is extremely useful when we start looking at
algebraic structures such as groups, rings, and so on. These come with
some data, together with a bunch of axioms, like associativity,
commutativity, and so on. The lemma we prove tells us that to build a
path between two groups, it's enough to build a path just between the
underlying data, ignoring all the axioms.

```
Σ≡PropIso : {A : Type ℓ} {B : A → Type ℓ'}
            (p : isPred B)
            (x y : Σ[ a ∈ A ] B a)
          → Iso (fst x ≡ fst y) (x ≡ y)
Σ≡PropIso {A = A} {B = B} p x y = iso to (cong fst) to-fro fro-to
  where
    to : fst x ≡ fst y → x ≡ y
    to e = ΣPathP→PathPΣ (e , p (fst x) (fst y) e (snd x) (snd y))

    to-fro : section to (cong fst)
    to-fro e i = ΣPathP→PathPΣ (cong fst e , to-fro-snd i)
      where
        to-fro-snd : SquareP (λ i j → B (fst (e j))) (p (fst x) (fst y) (cong fst e) (snd x) (snd y)) (λ j → snd (e j)) refl refl
        to-fro-snd = isProp→SquareP (λ i j → isPred→∀isProp p (fst (e j))) _ _ _ _

    fro-to : retract to (cong fst)
    fro-to e i j = e j
```

mvrnote: work this in?
```
Prop : ∀ ℓ → Type (ℓ-suc ℓ)
Prop ℓ = Σ[ X ∈ Type ℓ ] isProp X
```

## Propositional Truncation

We are still missing two important logical operations: "there exists" and
"or". For these, we will need another construction: the *propositional
truncation*, which takes any type `A` and forms a proposition `∃ A` ---
the proposition that "there exists some element of A". An element of
`∃ A` will be a proof that `A` has some element, though it won't be
any particular element of `A`.

We define `∃ A` as an inductive type with two constructors.

```
infix 3 ∃_
data ∃_ (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∃ A
  squash : (x y : ∃ A) → x ≡ y
```

The first, written `|_|`{.Agda}, says that to prove that there exists
an element in `A`, it suffices to have an actual element of `A`. The
second constructor forces `∃ A` to be a proposition. This is a
recursive constructor (like `suc`{.Agda} is for `ℕ`{.Agda}).

That second constructor is exactly what is needed to prove `isProp (∃ A)`.

```
isProp-∃ : isProp (∃ A)
isProp-∃ = squash
```

(In fact, Agda would have let us get away with specifying the type of
`squash`{.Agda} as `isProp (∃ A)` rather than its expanded form.)

The usual terminology for propositional truncation in homotopy type
theory is `∥ A ∥`, though this can get confusing if we are doing
quantum mechanics where the same bars denote the norm of a vector or
operator. We'll record it here anyway.

```
∥_∥ : Type ℓ → Type ℓ
∥ A ∥ = ∃ A
```

The recursion principle for `∃ A` says that to prove that `∃ A`
implies some proposition `P`, it suffices to assume we have an actual
element `a : A` and then prove `P`. That is, given a function `A → P`,
we can get an implication `∃ A → P` whenever `P` is a proposition.

```
∃-rec : (isProp P)
      → (A → P)
      → (∃ A → P)
∃-rec Pprop f ∣ x ∣ = f x
∃-rec Pprop f (squash x y i) = Pprop (∃-rec Pprop f x) (∃-rec Pprop f y) i
```

`∃` should be "functorial", that is, if we have a function from `A` to
`B`, then `A` having an element implies `B` has an element.

```
∃-map : (A → B) → (∃ A → ∃ B)
-- Exercise:
∃-map f = ?
```

When `P` is already a proposition, truncating it should do nothing:

```
isProp→Iso∃ : isProp P → Iso P (∃ P)
-- Exercise:
isProp→Iso∃ isPropP = ?
Hint: use `propExt`
```

If `P : A → Type` is a family of propositions on `A` --- that is, a
proposition concerning elements of `A` --- then we often like to write
something like "$∃ a : A , P a$" to say that there is an `a : A` such
that `P a` is true. Type theoretically, this is saying that there is
some pair `(a , p)` where `a : A` and `p : P a`. For this reason, we
can define a special syntax that resembles the usual mathematical
notation for existential quantification.

```
∃-syntax : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax A B = ∃ (Σ A B)

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
```

With propositional truncation, we can finally define the proposition
that represents "or" which eluded us in Lecture 1-3. There, our guess
was that "or" is be represented by `A ⊎ B`, but this is not generally
a proposition even when `A` and `B` are propositions.

```
¬isProp⊤⊎⊤ : ¬ isProp (⊤ ⊎ ⊤)
¬isProp⊤⊎⊤ p =
  let uhoh = p (inl tt) (inr tt)
  in  subst is-inl uhoh tt
  where
      is-inl : ⊤ ⊎ ⊤ → Type
      is-inl (inl _) = ⊤
      is-inl (inr _) = ∅
```

However, it is true that `A ⊎ B` has some element if and only if `A`
has some element or `B` has some element (or both have
elements). Therefore, we can define `A orP B` as the proposition that
there exists an element in `A ⊎ B`.

```
_orP_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A orP B = ∃ (A ⊎ B)
```

mvrnote: prose

```
¬→¬∃ : ¬ A → ¬ ∃ A
-- Exercise:
¬→¬∃ = {!!}
```

```
¬¬-∃-Iso : Iso (¬ ¬ ∃ A) (¬ ¬ A)
-- Exercise: Hint: use `propExt`
¬¬-∃-Iso = ?

    fro : ¬ ¬ A → ¬ ¬ ∃ A
    fro ¬¬a ¬∃a = ¬¬a (λ x → ¬∃a ∣ x ∣)
```


mvrnote: delete these?
Challenges:
```
-- ∃-Idem-×-L-Iso : Iso (∃ (∃ A) × B) (∃ (A × B))
-- ∃-Idem-×-L-Iso = {!!}

-- ∃-Idem-×-R-Iso : Iso (∃ A × (∃ B)) (∃ (A × B))
-- ∃-Idem-×-R-Iso = {!!}

-- ∃-×-Iso : Iso ((∃ A) × (∃ B)) (∃ (A × B))
-- ∃-×-Iso = {!!}
```

## Decidable Types

mvrnote: move to an extras file? I don't think we use this in the S^1 proof

mvrnote: add prose on classical logic

If we have a generic proposition `P` we are not allowed to split into
cases for whether `P` is true or false: this would be saying that we
always have an element of `P ⊎ ¬ P` telling us whether `P` holds or
not.

For some types, we do in fact have `P ⊎ ¬ P`; we call such types
"decidable".  The folllowing type is equivalent to `P ⊎ ¬ P`, but with
more meaningful constructor names.

```
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

Here are the simplest examples:
```
Dec⊤ : Dec ⊤
-- Exercise:
Dec⊤ = {!!}

Dec∅ : Dec ∅
-- Exercise:
Dec∅ = {!!}

DecPt : A → Dec A
-- Exercise:
DecPt = {!!}
```

Predicates defined on data-types are often decidable.

```
Dec-isEvenP : (n : ℕ) → Dec (isEvenP n)
-- Exercise:
Dec-isEvenP n = {!!}
```

Admittedly, decidable types will not be so important for us in the
future, but they are an excellent font of exercises involving
propositions and truncations:

```
Dec→¬¬Stable : {A : Type ℓ} → Dec A → (¬ ¬ A → A)
-- Exercise:
Dec→¬¬Stable d = {!!}

Dec-extract : Dec B → ¬ ¬ (A → B) → (A → B)
-- Exercise:
Dec-extract d f = {!!}

Dec-Idem : Dec (Dec A) → Dec A
-- Exercise:
Dec-Idem d = ?

isProp-Dec : isProp A → isProp (Dec A)
-- Exercise:
isProp-Dec isPropA = ?

∃-Dec-Iso : Iso (Dec (∃ A)) (∃ (Dec A))
-- Exercise: Hint: use `propExt`
∃-Dec-Iso = ?

    fro-lemma : Dec A → Dec (∃ A)
    fro-lemma (yes p) = yes ∣ p ∣
    fro-lemma (no ¬p) = no (∃-rec isProp∅ ¬p)

    fro : ∃ (Dec A) → Dec (∃ A)
    fro = ∃-rec (isProp-Dec isProp-∃) fro-lemma

Dec→SplitSupport : Dec A → (∃ A → A)
-- Exercise:
Dec→SplitSupport d = ?
```

mvrnote: would be good to extend this to Hedberg's theorem, but that
needs some more technology


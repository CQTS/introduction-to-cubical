```
module 2--Paths-and-Identifications.2-8--Equivalences where
```

# Lecture 2-8: Equivalences

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
open import 2--Paths-and-Identifications.2-6--Propositions
open import 2--Paths-and-Identifications.2-7--Sets

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
```
-->

In this lecture, we will revisit `transport`{.Agda}, and see that
paths in `Type`{.Agda} are equivalences between types.

## Equivalences

In set theory, a bijection between sets $A$ and $B$ is a function
$f : A → B$ where for every $b ∈ B$, there is a unique $a ∈ A$ such
that $f(a) = b$. We can define an analogous notion in type theory:

```
isBijection : {A B : Type ℓ} (f : A → B) → Type ℓ
isBijection {A = A} f = ∀ b → ∃! (Σ[ a ∈ A ] (b ≡ f a))
```

First, we define the `fiber`{.Agda} of a function $f : A → B$, which
is the type theoretic name for the inverse image of an element. In
homotopy theory, this would be called the "homotopy fiber".

```
fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] (y ≡ f x)
```

Then, instead of saying that a function is a "bijection", we will say
that it is an *equivalence* when it has contractible fibers.

```
isEquiv : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isEquiv {B = B} f = (y : B) → isContr (fiber f y)
```

Bijection and equivalence are the exact same notion, just packaged
together slightly different. In fact, they line up precisely and are
definitionally equal:

```
isBijection≡isEquiv : {A B : Type ℓ} (f : A → B) → isBijection f ≡ isEquiv f
isBijection≡isEquiv f = refl
```

We will use the syntax `A ≃ B` for the type of equivalences between
`A` and `B`. (The symbol `≃`{.Agda} is input as `\simeq`.)

```
infix 4 _≃_

_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] isEquiv f
```

Given an equivalence, the underlying function is just the first
component.

```
equivFun : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B
equivFun e = fst e
```

The identity function is an equivalence. This comes down to fact that
the fiber of the identity function over a point `a` is the singleton
at `a` (mvrnote: or it would be, if the Cubical library hadn't made
the inscrutable choice to flip the direction of the path in the
definition of fiber...).

```
idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
idIsEquiv A = λ y → isContrSingl y

idEquiv : (A : Type ℓ) → A ≃ A
idEquiv A = idfun A , idIsEquiv A
```

mvrnote: prose
As we noted at the end of Lecture 2-5, paths in subtypes can be
computed in the underlying type. Since the type `A ≃ B` of
equivalences is a subtype of the type of functions `A → B` (since `A ≃
B` is by definition `Σ[ f ∈ A → B ] isEquiv f` and `isEquiv f` is a
proposition), we may compute paths between equivalences on their
underlying functions. We recall this here:

```
isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
isPropIsEquiv f u0 u1 i y = isPropIsContr (u0 y) (u1 y) i

equivEq : {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
equivEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i
```
mvrnote: compare this to `Σ≡PropIso`{.Agda}?

mvrnote: The following could have direct proofs, check 1lab?
```
-- congEquiv : (x ≡ y) ≃ (equivFun e x ≡ equivFun e y)
-- compEquiv : A ≃ B → B ≃ C → A ≃ C
-- invEquiv : A ≃ B → B ≃ A
```

mvrnote: Exercise from the HoTT book: Exercise 2.13. Show that (2 ≃ 2) ≃ 2.

## Equivalence vs. Isomorphism

From any equivalence, we can extract an isomorphism.

```
invFun : A ≃ B → B → A
invFun e b = fst (center (snd e b))

equivToIso : A ≃ B → Iso A B
equivToIso e = iso (fst e) (invFun e) (s e) (r e)
  where
    s : (e : A ≃ B) → section (fst e) (invFun e)
--  Exercise:
--  s e = ?
    s (e , is-equiv) y = sym (is-equiv y .fst .snd)

    r : (e : A ≃ B) → retract (fst e) (invFun e)
--  Exercise:
--  r e = ?
    r (e , is-equiv) x i = contraction (is-equiv (e x)) (x , refl) i .fst
```

Going the other way, we can turn any isomorphism into an equivalence,
but the process is much more involved. We will take it as a black box
for now.

<!--
```
module _ (i : Iso A B) where
  private
    f = isoFun i
    g = isoInv i
    s = isoRightInv i
    t = isoLeftInv i

    module _ (y : B) (x0 x1 : A) (p0 : y ≡ f x0) (p1 : y ≡ f x1) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 i)))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 i)))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 j) k
                               ; (i = i0) → s (p0 j) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i j

  isoToIsEquiv : isEquiv f
  isoToIsEquiv y .fst .fst = g y
  isoToIsEquiv y .fst .snd = sym (s y)
  isoToIsEquiv y .snd z = lemIso y (g y) (fst z) (sym (s y)) (snd z)
```
-->

```
isoToEquiv : Iso A B → A ≃ B
fst (isoToEquiv f) = isoFun f
snd (isoToEquiv f) = isoToIsEquiv f
```

You might naturally wonder if `Iso A B` and `A ≃ B` are themselves
isomorphic. This turns out not to be the case! The reason is that
there are types with where some pairs of elements have multiple paths
between them --- we will sometimes call these "higher types", and
we'll see them later on.

Consider the type of ways to show that the identity function `idfun X
: X → X` is an isomorphism: that is, functions `f : X → X` with `s :
(x : X) → f x ≡ x` and `r : (x : X) → f x ≡ x`. If `X` is a higher
type, then it may be that there are two different paths `p q : f x ≡
x` --- that is, that the type `p ≡ q` of paths between `p` and `q` is
empty. In this case, we might end up with different ways of giving
functions `s` and `r`.

On the other hand, no matter how complicated the type `X` is, `isEquiv
(idfun X)` is always contractible; that is, the identity function is
an equivalence in exactly one way.
mvrnote: this is `isPropIsEquiv`{.Agda}


## Equivalent types have the same properties

mvrnote: direct proofs?
```
isContrEquiv : A ≃ B → isContr B → isContr A
isContrEquiv f pB = isContrIso (equivToIso f) pB

isPropEquiv : A ≃ B → isProp B → isProp A
isPropEquiv f pB = isPropIso (equivToIso f) pB
```

## Every type family is the fibers of its projection

mvrnote: and fiberwise equivalences https://1lab.dev/1Lab.Equiv.Fibrewise.html
mvrnote: worth working out/including?


## Relations

mvrnote: why did we have this section again?

A (type-valued) *relation* between two types `A` and `B` is a type
family `R : A → B → Type` depending on both `A` and `B`. We interpret
the type `R a b` as "the type of ways that `a` relates to `b`".

(There is some futzing around with universe levels, since `Rel A B` is
a type of type families and so must live at a higher universe level
than both of the input types.)

```
Rel : ∀ {ℓ} {ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Rel {ℓ} {ℓ'} A B = A → B → Type (ℓ-max ℓ ℓ')
```

Any function `f : A → B` induces a relation `graph f : Rel A B` known
as the graph of `f`. You might be familiar with the graph of a
function as defined in ordinary math: this is the subset of $A × B$ so
where $f(a) = b$.

```
graph : {A B : Type ℓ} → (A → B) → Rel A B
graph f a b = (f a ≡ b)
```

This says that the ways we relate `a : A` and `b : B` via the graph of
`f` are precisely the paths from `f a` to `b` (in `B`). The graph is a
special sort of relation: it is a "functional relation". A relation
`R : Rel A B` is functional if for every `a : A`, there is a unique `b :
B` and way `r : R a b` that `a` relates with `b`.

```
isFunctional : {A B : Type ℓ} → Rel A B → Type ℓ
isFunctional {B = B} R = ∀ a → ∃! (Σ[ b ∈ B ] (R a b))
```

The graph of a function is a functional relation --- hence the name.

```
isFunctionalGraph : {A B : Type ℓ} (f : A → B) → isFunctional (graph f)
-- Exercise:
isFuncationalGraph f a = ?
```

On the other hand, any functional relation gives rise to a function.

```
isFunctional→Fun : {A B : Type ℓ} (R : Rel A B) (c : isFunctional R)
                 → A → B
-- Exercise:
isFunctional→Fun R c a = ?
```

We can show that the function we extract out of the graph of a
function `f` is just `f`:
```
section-isFunctionalGraph→Fun : {A B : Type} (f : A → B)
      → isFunctional→Fun (graph f) (isFunctionalGraph f) ≡ f
-- Exercise:
section-isFunctionalGraph→Fun f = ?
```

In the other direction, we get an isomorphism between `R a b` and
`(graph (isFunctional→Fun R c)) a b` whenever `R` is a functional
relation. We don't quite have the tools yet to prove this, we'll have
to revisit it in the next lecture.

For every relation `R : Rel A B`, there is a relation `flip R : Rel B
A` defined by `(flip R) b a = R a b`. In fact, for this we can use the
function `flip`{.Agda} defined way back in Lecture 1-1. A relation is
said to be a *one-to-one correspondence* if both it and its flip are
functional; that is, if for every `a` there is a unique `b` and `r : R
a b` and for every `b` there is a unique `a` and `r : R a b`.

```
isOneToOne : {A B : Type} (R : Rel A B) → Type _
isOneToOne R = isFunctional R × isFunctional (flip R)
```

If `e : A ≃ B` is an equivalence, then its graph is a one-to-one
correspondence.

```
-- mvrnote: fix
-- graphEquivIsOneToOne : {A B : Type} (e : A ≃ B)
--                      → isOneToOne (graph (fst e))
-- -- Exercise:
graphEquivIsOneToOne e = ?
graphEquivIsOneToOne (e , p) = (isFunctionalGraph e) , p
```

It is also possible to go the other way, but again we'll come back to
this.

## Transport is an Equivalence

The function `transport p : A → B` for a path `p : A ≡ B` is an
equivalence between `A` and `B`. We can prove this by a sneaky trick,
`transport`{.Agda}ing the proof that the identity function is an
equivalence.

```
isEquivTransport : {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} p =
  transport (λ i → isEquiv (λ x → transport-filler p x i)) (idIsEquiv A)

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
fst (pathToEquiv p) = transport p
snd (pathToEquiv p) = isEquivTransport p
```

An easy application mvrnote: of `equivEq`{.Agda} is that the constant path `refl` at a type `A`
becomes us the identity equivalence on `A`.

```
pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq (λ i x → transp (λ _ → A) i x)
```


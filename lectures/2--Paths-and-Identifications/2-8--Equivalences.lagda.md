```
module 2--Paths-and-Identifications.2-8--Equivalences where
```

# Lecture 2-8: Equivalences

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
open import 2--Paths-and-Identifications.2-7--Sets

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
```
-->

In this lecture, we will revisit `transport`{.Agda}, and see that
paths in `Type`{.Agda} are equivalences between types. mvrnote: we don't do univalence here actually

## Bijections

In set theory, a bijection between sets $A$ and $B$ is a function
$f : A → B$ where for every $b ∈ B$, there is a unique $a ∈ A$ such
that $f(a) = b$. We can define an analogous notion in type theory:

```
isBijection : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isBijection {A = A} f = ∀ b → ∃! (Σ[ a ∈ A ] (b ≡ f a))

Bijection : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Bijection A B = Σ[ f ∈ (A → B) ] isBijection f
```

The type inside the `∃!` comes up a lot, so let's name it. The
`fiber`{.Agda} of a function $f : A → B$ over an element $y : B$ is
its inverse image of that element. In homotopy theory, this would be
called the "homotopy fiber".

```
fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] (y ≡ f x)
```

Then, a bijection is exactly a map that has contractible fibers.

```
isBijection≡isContrFibers : {A B : Type ℓ} (f : A → B) → isBijection f ≡ ((y : B) → isContr (fiber f y))
isBijection≡isContrFibers f = refl
```

-- The identity function is an equivalence. This comes down to fact that
-- the fiber of the identity function over a point `a` is the singleton
-- at `a` (mvrnote: or it would be, if the Cubical library hadn't made
-- the inscrutable choice to flip the direction of the path in the
-- definition of fiber...).

```
-- idIsEquiv : (A : Type ℓ) → isEquiv (idfun A)
-- idIsEquiv A = λ y → isContrSingl y

-- idEquiv : (A : Type ℓ) → A ≃ A
-- idEquiv A = idfun A , idIsEquiv A
```

mvrnote: prose
As we noted at the end of Lecture 2-5, paths in subtypes can be
computed in the underlying type. Since the type `A ≃ B` of
equivalences is a subtype of the type of functions `A → B` (since `A ≃
B` is by definition `Σ[ f ∈ A → B ] isEquiv f` and `isEquiv f` is a
proposition), we may compute paths between equivalences on their
underlying functions. We recall this here:

```
isPropIsBijection : (f : A → B) → isProp (isBijection f)
isPropIsBijection f u0 u1 i y = isPropIsContr (u0 y) (u1 y) i

bijectionEq : {e f : Bijection A B} → (h : e .fst ≡ f .fst) → e ≡ f
bijectionEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsBijection (h i)) (e .snd) (f .snd) i
```
mvrnote: compare this to `Σ≡PropIso`{.Agda}?

mvrnote: The following could have direct proofs, check 1lab?
```
-- congEquiv : (x ≡ y) ≃ (equivFun e x ≡ equivFun e y)
-- compEquiv : A ≃ B → B ≃ C → A ≃ C
-- invEquiv : A ≃ B → B ≃ A
```

mvrnote: Exercise from the HoTT book: Exercise 2.13. Show that (2 ≃ 2) ≃ 2.

## Bijection vs. Equivalence

From any bijection we can extract an equivalence.

```
-- bijectionInvFun : Bijection A B → B → A
-- bijectionInvFun e b = fst (center (snd e b))

bijectionToEquiv : Bijection A B → Equiv A B
bijectionToEquiv {A = A} {B = B} (f , isb) = equiv f inv to-fro fro-to
  where
    inv : B → A
    inv y = fst (center (isb y))

    to-fro : isSection f inv
--  Exercise:
    to-fro = {!!}

    fro-to : isRetract f inv
--  Exercise:
    fro-to = {!!}
```

Going the other way, we can turn any isomorphism into a bijection,
but the process is more involved.

```
module _ {f : A → B} (isI : isEquiv f) where
  private
    g = fst (fst isI)
    s : isSection f g
    s = snd (fst isI)
    g' = fst (snd isI)
    t : isSection g' f
    t = snd (snd isI)

    module _ (y : A) (x0 x1 : B) (p0 : y ≡ g x0) (p1 : y ≡ g x1) where
      fill0 : I → I → B
      fill0 i = hfill (λ k → λ { (i = i1) → s x0 k
                               ; (i = i0) → f y })
                      (inS (f (p0 i)))

      fill1 : I → I → B
      fill1 i = hfill (λ k → λ { (i = i1) → s x1 k
                               ; (i = i0) → f y })
                      (inS (f (p1 i)))

      fill2 : I → I → B
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (f y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → B
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → s (fill2 i i1) (~ k)
                              ; (j = i0) → f y })
                     (fill2 i j)

      sq1 : I → I → A
      sq1 i j = hcomp (λ k → λ { (i = i1) → t (p1 j) k
                               ; (i = i0) → t (p0 j) k
                               ; (j = i1) → t (g (p i)) k
                               ; (j = i0) → t y k })
                      (g' (sq i j))

      lemEquiv : (x0 , p0) ≡ (x1 , p1)
      lemEquiv i .fst = p i
      lemEquiv i .snd = λ j → sq1 i j

  isEquiv→secIsBijection : isBijection g
  isEquiv→secIsBijection y = isProp→with-point-isContr (λ (x0 , p0) (x1 , p1) → lemEquiv y x0 x1 p0 p1) (f y , sym (t y) ∙ sym (equivSec≡Ret (f , isI) (f y)))

Equiv→Bijection : A ≃ B → Bijection A B
Equiv→Bijection (f , isE) = (f , isEquiv→secIsBijection (snd (invEquiv (f , isE))))
```

mvrnote: out of date
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

## Bijections vs Equivalences

isEquivPostComp : {f : A → B} → isEquiv f → isEquiv (λ (d : C → A) → f ∘ d)
isEquivPostComp ((g , s) , (g' , r)) = ((λ d → g ∘ d) , λ d i c → s (d c) i) , ((λ d → g' ∘ d) , λ d i c → r (d c) i)

isEquivPreComp  : {f : A → B} → isEquiv f → isEquiv (λ (d : B → C) → d ∘ f)
isEquivPreComp ((g , s) , (g' , r)) = {!((λ d → d ∘ g') , λ d i a → d (r a i)) , ((λ d → d ∘ g) , λ d i b → d (s b i))!}

sectionOf≃fiber : (f : A → B) → (sectionOf f) ≃ (fiber (λ (d : B → A) → f ∘ d) (idfun _))
sectionOf≃fiber f = equiv (λ (g , s) → g , λ i b → s b (~ i)) (λ (g , s) → g , λ b i → s (~ i) b) (λ _ → refl) (λ _ → refl)

retractOf≃fiber : (f : A → B) → (retractOf f) ≃ (fiber (λ (d : B → A) → d ∘ f) (idfun _))
retractOf≃fiber f = equiv (λ (g , s) → g , λ i b → s b (~ i)) (λ (g , s) → g , λ b i → s (~ i) b) (λ _ → refl) (λ _ → refl)

isEquiv→isContrSectionOf : {f : A → B} → isEquiv f → isContr (sectionOf f)
isEquiv→isContrSectionOf {f = f} isE = isContrEquiv (sectionOf≃fiber f) (isEquiv→isBijection (isEquivPostComp isE) (idfun _))

isEquiv→isContrRetractOf : {f : A → B} → isEquiv f → isContr (retractOf f)
isEquiv→isContrRetractOf {f = f} isE = isContrEquiv (retractOf≃fiber f) (isEquiv→isBijection (isEquivPreComp isE) (idfun _))

isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
isPropIsEquiv f = with-point-isContr→isProp λ isE → isContr× (isEquiv→isContrSectionOf isE) (isEquiv→isContrRetractOf isE)

```
postulate 
  isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
```


mvrnote: important application. it's possible `pathToEquivRefl` can be
defined directly through `transp` manipulation, need to check

```
equivEq : {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
equivEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i

pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq (λ i x → transp (λ _ → A) i x)
```

## Every type family is the fibers of its projection

mvrnote: and fiberwise equivalences https://1lab.dev/1Lab.Equiv.Fibrewise.html
mvrnote: worth working out/including?

## Relations

mvrnote: why did we have this section again?

mvrnote: GCD would be a cool exercise here!

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
isFunctionalGraph f a = {!!}
```

On the other hand, any functional relation gives rise to a function.

```
isFunctional→Fun : {A B : Type ℓ} (R : Rel A B) (c : isFunctional R)
                 → A → B
-- Exercise:
isFunctional→Fun R c a = {!!}
```

We can show that the function we extract out of the graph of a
function `f` is just `f`:
```
section-isFunctionalGraph→Fun : {A B : Type} (f : A → B)
      → isFunctional→Fun (graph f) (isFunctionalGraph f) ≡ f
-- Exercise:
section-isFunctionalGraph→Fun f = {!!}
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
-- graphEquivIsOneToOne e = {!!}
graphEquivIsOneToOne (e , p) = (isFunctionalGraph e) , p
```

It is also possible to go the other way, but again we'll come back to
this.

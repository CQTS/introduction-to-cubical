<!--
```
module 2--Paths-and-Identifications.2-9--Contractible-Maps where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C A' : Type ℓ
```
-->


# Lecture 2-9: Contractible Maps

In this Lecture we prove four crucial facts about equivalences:

* Being an equivalence is a *proposition* about a map, rather than
  extra structure. That is:

```
isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
```

* As an easy consequence, ``path→equiv`` is an equivalence,
  completing the proof of univalence we started in Lecture 2-X:

```
univalence : (A ≡ B) ≃ (A ≃ B)
```

* Forming Σ-types respects equivalences. That is, if the inputs to
  ``Σ-map`` are equivalences then the resulting function is an
  equivalence.

```
Σ-map-≃ : {B : A → Type ℓ'} {B' : A' → Type ℓ'}
        → (e₁ : A ≃ A')
        → (e₂ : (a : A) → (B a) ≃ (B' (e₁ .map a)))
        → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')
```

  We showed this fact for the non-dependent ``×`` way back in
  ``×-map-≃``, the dependent version is surprisingly difficult!

* A partial converse to the previous: if `Σ-map idfun f₂ : (Σ[ a ∈ A ]
  B a) → (Σ[ a ∈ A ] B' a)` is an equivalence for a family of maps `f₂
  : (a : A) → B a → B a'`, then each of the `f₂ a : B a → B' a` must
  be an equivalence.

To prove each of these facts, it turns out to be easiest to detour
through an alternative definition of equivalences: the notion of
"contractible map".

mvrnote: This lecture is unfortunately a bit technical and fiddly. Is
there anything we can do about that? Are there slicker proofs of some
of the things here?


## Contractible Maps

In set theory, a bijection between sets $A$ and $B$ is a function $f :
A → B$ where for every $b ∈ B$, there exists a unique $a ∈ A$ so that
$f(a) = b$. We can translate this definition directly into type
theory:

```
isBijection : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isBijection {A = A} {B = B} f = (b : B) → isContr (Σ[ a ∈ A ] (b ≡ f a))
```

That type inside ``∃!`` comes up a lot, so it is given a name. The
``fiber`` of a function $f : A → B$ over an element $b : B$ is the
inverse image of that element, so all elements of $A$ that are mapped
to $b$ by $f$. In homotopy theory, this would be called the "homotopy
fiber".

```
fiber : {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f b = Σ[ a ∈ A ] (b ≡ f a)
```

Then, a bijection is exactly a map that has contractible fibers (just
unfolding the definitions).

```
_ : {A B : Type ℓ} → (f : A → B)
  → isBijection f ≡ ((y : B) → isContr (fiber f y))
_ = λ f → refl
```

This shape of definition comes up fairly often where we have a
property of types (in this case contractibility), and we use it to
define a property of maps by testing that property on all the fibers.
So, looking forward to other definitions of this kind, we're going to
rename the property of a map being a bijection to being
*contractible*.

```
-- mvrnote: make record
isContractibleMap : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isContractibleMap = isBijection

ContractibleMap : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
ContractibleMap A B = Σ[ f ∈ (A → B) ] isContractibleMap f
```

Now, because a type being contractible is a proposition, a map being
contractible is also a proposition.

```
isPropIsContractibleMap : (f : A → B) → isProp (isContractibleMap f)
-- Exercise:
isPropIsContractibleMap f = {!!}
```


## Equivalences are Contractible Maps

It is easy to show that any contractible map is an equivalence. Each
fiber is contractible, in particular, each fiber has a point, and we
can use these to define a function `B → A`.

```
isContractibleMap→isEquiv : {f : A → B} → isContractibleMap f → isEquiv f
isContractibleMap→isEquiv {A = A} {B = B} {f = f} isc = packIsEquiv inv to-fro inv fro-to
  where
    inv : B → A
--  Exercise:
    inv b = {!!}

    to-fro : isSection f inv
--  Exercise: (Hint: Use the path provided by the ``fiber``.)
    to-fro = {!!}

    fro-to : isRetract f inv
--  Exercise: (Hint: Use the path provided by ``isContr``.)
    fro-to = {!!}
```

We can also show that any equivalence is a contractible map, but the
process is more involved.

Here's the setup: starting with an equivalence `e : A ≃ B`, we are
going to show that the provided *section* of `e` is a contractible
map. Then at the end, we'll use this to show that `e` itself is a
contractible map.

The crucial step that we're going to prove first is that the fiber of
`equivSec e` over any point `y : A` is a proposition.

So begin by supposing we have `y : A`, and two elements of the
fiber over it, `(x₀, p₀)` and `(x₁ , p₁)`:

```
private module _ (e : A ≃ B) (y : A) (x₀ : B) (p₀ : y ≡ e .proof .section .map x₀) (x₁ : B) (p₁ : y ≡ e .proof .section .map x₁) where
```

Our goal is to show that `(x₀, p₀)` and `(x₁ , p₁)` are equal. Let's
give shorter names to the components of the equivalence `e`.

```
  private
    f : A → B
    f = e .map

    g : B → A
    g = e .proof .section .map

    s : isSection f g
    s = e .proof .section .proof

    g' : B → A
    g' = e .proof .retract .map

    r : isRetract f g'
    r = e .proof .retract .proof
```

First we need to produce a path `x₀ ≡ x₁` to use in the first
component. This is easy enough, using the fact that `g` is a section of
`f`.

```
  path₀ : f y ≡ x₀
  -- Exercise:
  path₀ = {!!}

  path₁ : f y ≡ x₁
  -- Exercise:
  path₁ = {!!}

  path : x₀ ≡ x₁
  -- Exercise:
  path₂ = {!!} ∙∙ refl ∙∙ {!!}
```

You'll see very shortly why defining `path₂` in this symmetrical way
is beneficial.

Now, a path between the points `x₀` and `x₁` in `B` is not enough, we
also need a path-over showing that the paths `p₀` and `p₁` are equal.
That is, we need a square

```
  square : Square refl (ap g path) p₀ p₁
```

We'll do this in two steps. First, we'll compose the following cube:

                        f p₁
               f y  — — — — — — > f g x₁
              / ^                 / ^
            /   |               /   |
          /     | f p₀        /     |
       f y  — — — — — — > f g x₀    | s x₁
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           | s x₀  |                    ∙ — >
        |       |           |       |                      i
        |      f y  — — — — | — — > x₁
        |     /       path₁ |     /
        |   /               |   / path
        | /                 | /
       f y  — — — — — — — > x₀
                path₀

The left square and right square are easy: constantly `f y` on the
left, and using the fact that `g` is a section on the right. For the
front, back, and bottom squares, observe that `path₀`, `path₁` and
`path` are defined as compositions, so we can use ``∙-filler`` and
``∙∙-filler`` for the filled squares as appropriate.

```
  square-f-faces : (i j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) B
  -- Exercise:
  square-f-faces i j k (i = i0) = {!!}
  square-f-faces i j k (i = i1) = {!!}
  square-f-faces i j k (j = i0) = {!!}
  square-f-faces i j k (j = i1) = {!!}

  square-f : Square (ap f refl) (ap f (ap g path)) (ap f p₀) (ap f p₁)
  -- Exercise:
  square-f i j = hcomp (square-f-faces i j) {!!}
```

This square is very nearly what we want: we just need to kill the
extra `ap f` on all the sides. For this, we use the fact that `g'`
is a retract of `f`: we'll add an extra `g'`, then use `r` to cancel
both `g'` and `f` out. (There are multiple ways to do this, via
``transport`` or filling another cube.)

```
  -- square : Square refl (ap g path) p₀ p₁ (Given above.)
  -- Exercise:
  square i j = {!!}
```

So combining `path` and `square`, we get the path of between pairs
that we wanted.

```
  lemEquiv : (x₀ , p₀) ≡ (x₁ , p₁)
  -- Exercise:
  lemEquiv i = {!!}
```

Now the hard work is done: every fiber of `equivSec e` is a
proposition. And we can easily find a point of every fiber, so in fact
every fiber is contractible, via ``isProp-with-point→isContr``.

```
isEquiv→secIsContractibleMap : (e : A ≃ B) → isContractibleMap (e .proof .section .map)
-- Exercise:
isEquiv→secIsContractibleMap e y = isProp-with-point→isContr {!!} {!!}
```

Now, we usually want to know that the actual function underlying an
equivalence is a contractible map, rather than the section. To get
this, we just invert the equivalence, because the section used for the
inverse is exactly the original map!

```
isEquiv→isContractibleMap : {f : A → B} → isEquiv f → isContractibleMap f
isEquiv→isContractibleMap isE = isEquiv→secIsContractibleMap (invEquiv (equiv _ isE))

Equiv→ContractibleMap : A ≃ B → ContractibleMap A B
Equiv→ContractibleMap (equiv f isE) = (f , isEquiv→isContractibleMap isE)
```


## Fact 1: Being an Equivalence is a Proposition

We now turn to the first of the goals that we listed up at the top:
showing that `isEquiv f` is always a proposition. We'll do this by
showing that if we do have an element of `isEquiv f`, then in fact
`isEquiv f` is contractible. Our definition of ``isEquiv`` is as
the pair of a section and a retract, so this will mean showing that
those two pieces are contractible separately.

First, some generalities about equivalences. These can both be proven
by defining an equivalence directly.

```
isEquiv→isEquivPostComp : {f : A → B} → isEquiv f → isEquiv (λ (d : C → A) → f ∘ d)
-- Exercise:
isEquiv→isEquivPostComp e = {!!}

sectionOf≃fiber : (f : A → B) → (SectionOf f) ≃ (fiber (λ (d : B → A) → f ∘ d) idfun)
-- Exercise:
sectionOf≃fiber f = {!!}
```

Now the strategy shoudl be clear: `sectionOf f` is equivalent to one
of the fibers of an equivalence, and because any equivalence is a
contractible map, that fiber is contractible. You should be able to
put it together:

```
isEquiv→isContrSectionOf : {f : A → B} → isEquiv f → isContr (SectionOf f)
-- Exercise:
isEquiv→isContrSectionOf {f = f} isE = {!!}
```

A symmetrical argument works for the retract, feel free to
copy and paste as necessary.

```
isEquiv→isEquivPreComp  : {f : A → B} → isEquiv f → isEquiv (λ (d : B → C) → d ∘ f)
-- Exercise:
isEquiv→isEquivPreComp e = {!!}

retractOf≃fiber : (f : A → B) → (RetractOf f) ≃ (fiber (λ (d : B → A) → d ∘ f) idfun)
-- Exercise:
retractOf≃fiber f = {!!}

isEquiv→isContrRetractOf : {f : A → B} → isEquiv f → isContr (RetractOf f)
-- Exercise:
isEquiv→isContrRetractOf {f = f} isE = {!!}
```

Now just glue them together!

```
-- mvrnote: move earlier
isEquiv≃× : (f : A → B) → isEquiv f ≃ (SectionOf f × RetractOf f)
isEquiv≃× f .map (isEquivData s r) = s , r
isEquiv≃× f .proof .section .map (s , r) = isEquivData s r
isEquiv≃× f .proof .section .proof (s , r) = refl
isEquiv≃× f .proof .retract .map (s , r) = isEquivData s r
isEquiv≃× f .proof .retract .proof (isEquivData s r) = refl

-- Exercise:
isProp-isEquiv f = with-point-isContr→isProp {!!}
```

As we showed in `≡Subtype` at the end of Lecture 2-X, paths in subtypes
can be calculated in the underlying type. Since the type `A ≃ B` of
equivalences is a subtype of the type of functions `A → B` (because we
just showed `isEquiv f` is a proposition), we can compute paths
between equivalences on their underlying functions.

```
Equiv≃Σ : (A ≃ B) ≃ (Σ[ f ∈ (A → B)] isEquiv f)
Equiv≃Σ .map (equiv f e) = f , e
Equiv≃Σ .proof .section .map (f , e) = equiv f e
Equiv≃Σ .proof .section .proof (f , e) = refl
Equiv≃Σ .proof .retract .map (f , e) = equiv f e
Equiv≃Σ .proof .retract .proof (equiv f e) = refl

equivEq : {e f : A ≃ B} → (h : e .map ≡ f .map) → e ≡ f
-- Exercise:
equivEq {e = e} {f = f} h = {!!}
```

We knew already that univalence ``ua`` has a retract
``au``. But we can now use ``equivEq`` to easily show that
``au`` is also a section, and so ``ua`` is an equivalence.

```
au-ua : (e : A ≃ B) → au (ua e) ≡ e
-- Exercise: (Hint: ``ua-comp``)
au-ua e = {!!}
```

And prove univalence in all its glory:

```
-- univalence : (A ≡ B) ≃ (A ≃ B)
univalence = inv→equiv au ua au-ua ua-au
```


## Equivalence Induction
mvrnote:

```
isContr-singlEquiv : (A : Type ℓ) → isContr ( Σ[ T ∈ Type ℓ ] (A ≃ T) )
isContr-singlEquiv A .center = (A , idEquiv A)
isContr-singlEquiv A .contraction (B , e) i .fst = ua e i
isContr-singlEquiv A .contraction (B , e) i .snd .map a = Path→ua-PathP e {x = a} refl i
isContr-singlEquiv A .contraction (B , e) i .snd .proof = isProp→PathP (λ j → isProp-isEquiv (isContr-singlEquiv A .contraction (B , e) j .snd .map)) isEquiv-idfun (e .proof) i

EquivJ : {A : Type ℓ}
       → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
       → P A (idEquiv A)
       → {B : Type ℓ} (e : A ≃ B)
       → P B e
EquivJ P p e = subst (λ e → P (e .fst) (e .snd)) (isContr-singlEquiv _ .contraction (_ , e)) p

ap-isEquiv : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → isEquiv (ap {x = a₁} {a₂} (e .map) )
ap-isEquiv e {a₁} {a₂} = EquivJ (λ B e → isEquiv (ap {x = a₁} {a₂} (e .map))) isEquiv-idfun e

ap-≃ : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → (a₁ ≡ a₂) ≃ (e .map a₁ ≡ e .map a₂)
ap-≃ e .map = ap (e .map)
ap-≃ e .proof = ap-isEquiv e
```

## Being an Isomorphism is a Not Propositional

``isProp-isEquiv`` justifies our use of "equivalences" over
"isomorphisms". Recall that an isomorphism is a map with a single map going
the other way that is *both* a section and a retract.

```
-- mvrnote make record
isIso : {A : Type ℓ} → {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isIso f = Σ[ g ∈ _ ] isSection f g × isRetract f g
```

Sadly, this type is *not* always a proposition. This feels strange,
because in ordinary set-based mathematics, this defect is impossible
to see:

mvrnote: exercises?
```
isoInvUnique : {f : A → B} → (i₁ i₂ : isIso f) → (b : B) → fst i₁ b ≡ fst i₂ b
isoInvUnique {f = f} (g₁ , s₁ , r₁) (g₂ , s₂ , r₂) b
  = g₁ b          ≡⟨ sym (r₂ (g₁ b)) ⟩
    g₂ (f (g₁ b)) ≡⟨ ap g₂ (s₁ b) ⟩
    g₂ b ∎

isSet→isProp-isIso : (f : A → B)
  → isSet A → isSet B → isProp (isIso f)
isSet→isProp-isIso f isA isB iso₁ iso₂ i .fst b = isoInvUnique iso₁ iso₂ b i
isSet→isProp-isIso f isA isB iso₁ iso₂ i .snd .fst b
  = isB _ _
    (transport-filler  (λ j → f (isoInvUnique iso₁ iso₂ b j) ≡ b) (iso₁ .snd .fst b) i)
    (transport-filler' (λ j → f (isoInvUnique iso₁ iso₂ b j) ≡ b) (iso₂ .snd .fst b) i)
    i
isSet→isProp-isIso f isA isB iso₁ iso₂ i .snd .snd a
  = isA _ _
    (transport-filler  (λ j → isoInvUnique iso₁ iso₂ (f a) j ≡ a) (iso₁ .snd .snd a) i)
    (transport-filler' (λ j → isoInvUnique iso₁ iso₂ (f a) j ≡ a) (iso₂ .snd .snd a) i)
    i
```

In the world of homotopy type theory, however, the paths in
``isSection`` and ``isRetract`` could hold extra data.

Consider the type of ways to show that the identity function `X → X`
is an isomorphism: that is, the type of functions `f : X → X` such
that `s : (x : X) → f x ≡ x` and `r : (x : X) → f x ≡ x`. By gluing
these together, we can get a path `x ≡ x` for any `x : X`.

```
isIso→center : isIso idfun → (x : A) → (x ≡ x)
isIso→center (g , s , r) x = sym (s x) ∙ r x
```

For sets this poses no problem, but if `X` is a higher-dimensional type then
there may be lots of non-equal elements of `(x : A) → (x ≡
x)`. Indeed, we already encounter the problem when looking at the
simplest higher type, the circle ``S¹``.

```
refl≢rotate-loop : ¬ ((λ _ → refl) ≡ rotate-loop)
-- Exercise:
refl≢rotate-loop p = {!!}
```

But now, here are two ways of showing that the identity on ``S¹``
is an isomorphism.

```
S¹-refl-iso : isIso (idfun {A = S¹})
S¹-refl-iso .fst = idfun
S¹-refl-iso .snd .fst = λ _ → refl
S¹-refl-iso .snd .snd = λ _ → refl

S¹-rotate-loop-iso : isIso (idfun {A = S¹})
S¹-rotate-loop-iso .fst = idfun
S¹-rotate-loop-iso .snd .fst = λ _ → refl
S¹-rotate-loop-iso .snd .snd = rotate-loop
```

If `isIso idfun` were a proposition, then these would have to be
equal. This would imply that `(λ _ → refl) ≡ rotate-loop`, which we've
just shown cannot be.

```
¬isProp-isIso : ¬ isProp (isIso (idfun {A = S¹}))
-- Exercise:
¬isProp-isIso p = {!!}
```


## Fact 2: Σ-types Respect Equivalence

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

Σ-map-snd : {B : A → Type ℓ} {B' : A → Type ℓ}
  → (f₂ : (a : A) → B a → B' a)
  → Σ[ a ∈ A ] B a → Σ[ a ∈ A ] B' a
Σ-map-snd f₂ = Σ-map idfun f₂

module _ {A A' : Type ℓ} {B : A' → Type ℓ'} (e₁ : A ≃ A') where
  isEquiv-Σ-map-fst : isEquiv (Σ-map-fst {B = B} (e₁ .map))
  isEquiv-Σ-map-fst = EquivJ (λ A'' e → (B : A'' → Type ℓ') → isEquiv (Σ-map-fst {B = B} (e .map))) 
                             (λ _ → isEquiv-idfun) e₁ B

  Σ-map-fst-≃-ua : (Σ[ a ∈ A ] B (e₁ .map a)) ≃ (Σ[ a' ∈ A' ] B a')
  Σ-map-fst-≃-ua .map = Σ-map-fst (e₁ .map)
  Σ-map-fst-≃-ua .proof = isEquiv-Σ-map-fst

module _ {B : A → Type ℓ} {B' : A → Type ℓ} (e₂ : (x : A) → B x ≃ B' x) where
  Σ-map-snd-ua : (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] B' a)
  Σ-map-snd-ua = au λ i → Σ[ a ∈ A ] ua (e₂ a) i

  Σ-map-snd-ua-underlying : Σ-map-snd-ua .map ≡ Σ-map-snd (λ a → e₂ a .map)
  Σ-map-snd-ua-underlying i (a , b) .fst = ua-comp (idEquiv _) a i
  Σ-map-snd-ua-underlying i (a , b) .snd = transport-filler' (λ j → B' (transport-refl a j)) (e₂ a .map b) i

  Σ-map-snd-≃ : (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] B' a)
  Σ-map-snd-≃ .map = Σ-map-snd (λ a → e₂ a .map)
  Σ-map-snd-≃ .proof = subst isEquiv Σ-map-snd-ua-underlying (Σ-map-snd-ua .proof)
```


Now we handle the first component: we want to show that if `f₁ : A →
A'` is an equivalence, then the induced map `(Σ[ a ∈ A ] B (f₁ a)) →
(Σ[ a' ∈ A' ] B a')`

```
module _ {B : A' → Type ℓ} (f₁ : A → A') where
```

is also an equivalence.

This one is surprisingly difficult for such a simple statement. Here's
the key fact, and what makes the connection to contractible maps. You
will have to use the technology from Lecture 2-X on ``transport``
and ``transport-filler``.

```
  Σ-map-fst-fib-≃ : (t : Σ[ a' ∈ A' ] B a') → fiber (Σ-map-fst f₁) t ≃ fiber f₁ (fst t)
  Σ-map-fst-fib-≃ (a' , b') = inv→equiv to fro to-fro fro-to
    where
      to : fiber (Σ-map-fst f₁) (a' , b') → fiber f₁ a'
      -- Exercise:
      fst (to ((a , b) , p)) = {!!}
      snd (to ((a , b) , p)) = {!!}

      fro : fiber f₁ a' → fiber (Σ-map-fst f₁) (a' , b')
      -- Exercise:
      fst (fst (fro (a , p))) = {!!}
      snd (fst (fro (a , p))) = {!!}
      fst (snd (fro (a , p)) i) = {!!}
      snd (snd (fro (a , p)) i) = {!!}

      to-fro : isSection to fro
      to-fro (a , p) = refl

      fro-to : isRetract to fro
      -- Exercise:
      fst (fst (fro-to ((a , b) , p) i)) = {!!}
      snd (fst (fro-to ((a , b) , p) i)) = {!!}
      fst (snd (fro-to ((a , b) , p) i) j) = {!!}
      snd (snd (fro-to ((a , b) , p) i) j) = {!!} -- This can be done by a single, tricky use of `transport-fixing`. mvrnote: break this down
```

mvrnote: this could alternatively be done by using J everywhere

Now, we know that `fiber Σ-map-fst t` is contractible whenever `fiber
f₁ (fst t)` is. Use ``isContractibleMap→isEquiv`` and
``isEquiv→isContractibleMap`` to complete the proof.

```
  Σ-map-fst-isEquiv : isEquiv f₁ → isEquiv (Σ-map-fst f₁)
  -- Exercise:
  Σ-map-fst-isEquiv e = {!!}

Σ-map-fst-≃ : {B : A' → Type ℓ}
  → (e₁ : A ≃ A')
  → (Σ[ a ∈ A ] B (e₁ .map a)) ≃ (Σ[ a' ∈ A' ] B a')
Σ-map-fst-≃ e₁ = equiv (Σ-map-fst (e₁ .map)) (Σ-map-fst-isEquiv (e₁ .map) (e₁ .proof))
```

Finally, combine ``Σ-map-fst-≃`` with ``Σ-map-snd-≃`` to prove the
original result were looking for.

```
Σ-map-≃ {A = A} {A' = A'} {B = B} {B' = B'} e₁ e₂ =
  Σ[ a  ∈ A ]  B  a           ≃⟨ Σ-map-snd-≃ e₂ ⟩
  Σ[ a  ∈ A ]  B' (e₁ .map a) ≃⟨ Σ-map-fst-≃ e₁ ⟩
  Σ[ a' ∈ A' ] B' a'          ∎e
```


## Fact 3: Fiberwise Equivalences

mvrnote: In fact, the converse of this is true: if `Σ-map-snd f₂` is an
equivalence, then `f₂` must have been a fiberwise equivalence to begin with.


```
-- Σ-map-snd-fib-≃ : {B : A → Type ℓ} {B' : A → Type ℓ'} (f₂ : (a : A) → B a → B' a) → (t : Σ[ a ∈ A ] B' a) → fiber (Σ-map-snd f₂) t ≃ fiber (f₂ (fst t)) (snd t)
-- Σ-map-snd-fib-≃ {A = A} {B = B} {B' = B'} f₂ t = inv→equiv to fro to-fro fro-to
--   where
--     to : {(a , b') : Σ[ a ∈ A ] B' a} → fiber (Σ-map-snd f₂) (a , b') → fiber (f₂ a) b'
--     to ((x , v) , p) = transport (λ i → fiber (f₂ (fst (p (~ i)))) (snd (p (~ i)))) (v , refl)

--     fro : {(a , b') : Σ[ a ∈ A ] B' a} → fiber (f₂ a) b' → fiber (Σ-map-snd f₂) (a , b')
--     fro (b , p) = (_ , b) , (λ i → _ , (p i))

--     to-fro-refl : {(a , b) : Σ[ a ∈ A ] B a} → to (fro (b , refl)) ≡ (b , refl)
--     to-fro-refl {a , b} = transport-refl (b , refl)

--     to-fro : {t : Σ[ a ∈ A ] B' a} → isSection (to {t}) (fro {t})
--     to-fro (b , p) = J (λ y p → to (fro (b , sym p)) ≡ (b , sym p)) to-fro-refl (sym p)

--     fro-to-refl : {t : Σ[ a ∈ A ] B a} → fro (to (t , refl)) ≡ (t , refl)
--     fro-to-refl {t} = ap fro (transport-refl (snd t , refl))

--     fro-to : {t : Σ[ a ∈ A ] B' a} → isRetract (to {t}) (fro {t})
--     fro-to (t , p) = J (λ y p → fro (to (t , sym p)) ≡ (t , sym p)) fro-to-refl (sym p)

-- Σ-isEquiv-fiberwise : {B : A → Type ℓ} {B' : A → Type ℓ'} (f₂ : (a : A) → B a → B' a)
--   → isEquiv (Σ-map-snd f₂) → (a : A) → isEquiv (f₂ a)
-- Σ-isEquiv-fiberwise f₂ e a = isContractibleMap→isEquiv λ b' → isContrEquiv (invEquiv (Σ-map-snd-fib-≃ f₂ (a , b'))) (isEquiv→isContractibleMap e (a , b'))
```

::: Aside:
We could use ``Σ-map-snd-fib-≃`` to prove ``Σ-map-snd-≃``, but the
proof we suggested earlier is much more direct.
:::

I might seem intuitive that the same should be true in the first
component, so that if `Σ-map-fst f₁ : Σ[ a ∈ A ] B (f₁ a) → Σ[ a' ∈ A'
] B a'` is an equivalence then `f₁` must be an equivalence. But this
isn't true!

We've seen that `Σ[ a ∈ ⊤ ] B a` is equivalent to `B tt` and that `Σ[
a ∈ Bool ] B a` is equivalent to `B true ⊎ B false` (mvrnote: have we?
or did we remove it?). If we apply ``Σ-map-fst`` to the constant map
`Bool → ⊤` then we have a map `(Σ[ a ∈ Bool ] ∅) → (Σ[ a ∈ ⊤ ] ∅)`,
and we can arrange for this map to be an equivalence. All we need is
some type `X` for which `X ⊎ X ≃ X`. There are lots of these, but
choosing ``∅`` will be easiest. (You could also try `ℕ`.)

```
-- fold-∅ : (Σ[ a ∈ Bool ] ∅) → (Σ[ a ∈ ⊤ ] ∅)
-- -- Exercise:
-- fold-∅ = {!!}
fold-∅ = Σ-map-fst (λ (_ : Bool) → tt)

-- ¬Σ-isEquiv-base : ¬ ({A A' : Type} {f₁ : A → A'} {B : A' → Type} → isEquiv (Σ-map-fst {B = B} f₁) → isEquiv f₁)
-- -- Exercise:
-- ¬Σ-isEquiv-base p = ¬isContrBool {!!}
¬Σ-isEquiv-base p = ¬isContrBool (Equiv⊤→isContr (equiv (λ (_ : Bool) → tt) (p isEquiv-fold-∅)))

## References and Furthe Reading

https://cj-xu.github.io/faum/escardo.pdf

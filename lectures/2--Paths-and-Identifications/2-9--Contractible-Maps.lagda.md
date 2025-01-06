<!--
```
module 2--Paths-and-Identifications.2-9--Contractible-Maps where

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
open import 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C A' : Type ℓ
```
-->


# Lecture 2-9: Contractible Maps

In this Lecture we prove three crucial facts about equivalences:

* Being an equivalence is a *proposition* about a map, rather than
  extra structure. That is:

      isProp-isEquiv : (f : A → B) → isProp (isEquiv f)

* The funciton ``path→equiv`` is an equivalence, completing the proof
  of the univalence principle that we started in Lecture 2-X:

      univalence : (A ≡ B) ≃ (A ≃ B)

* Σ-types respects equivalences. That is, if the inputs to ``Σ-map``
  are equivalences then the resulting function is an equivalence.

      Σ-map-≃ : (e₁ : A ≃ A')
              → (e₂ : (a : A) → (B a) ≃ (B' (e₁ .map a)))
              → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')

  We showed this fact for the non-dependent ``×`` way back in
  ``×-map-≃``, the dependent version is surprisingly difficult!

To prove each of these facts, it turns out to be easiest to detour
through an alternative definition of equivalence: the notion of
"contractible map".


## Contractible Maps

In set theory, a bijection between sets $A$ and $B$ is a function $f :
A → B$ where for every $b ∈ B$, there is a unique $a ∈ A$ so that
$f(a) = b$. We can translate this definition directly into type
theory, using ``isContr`` as our interpretation of "unique existence".

```
isBijection : {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → Type (ℓ-max ℓ ℓ')
isBijection {A = A} {B = B} f = (b : B) → isContr (Σ[ a ∈ A ] (b ≡ f a))
```

That type inside ``isContr`` comes up a lot, so it is given a name.
The ``fiber`` of a function $f : A → B$ over an element $b : B$ is the
inverse image of that element, so all elements of $A$ whose image
under $f$ is equal to $b$. In homotopy theory, this would be more
accurately called the "homotopy fiber".

```
fiber : {A : Type ℓ} → {B : Type ℓ'}
  → (f : A → B) → (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f b = Σ[ a ∈ A ] (b ≡ f a)
```

Then, a bijection is exactly a map that has contractible fibers (just
unfolding the definitions).

```
_ = λ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → test-identical 
    (isBijection f)
    ((y : B) → isContr (fiber f y))
```

This shape of definition comes up fairly often. We have a property of
types (in this case contractibility), and we use it to define a
property of maps by testing that property is satisfied by all the
fibers. So, looking forward to other definitions of this sort, we're
going to rename the property of being a bijection to being a
*contractible map*.

```
-- mvrnote: make record?
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
can use these to define an inverse function `B → A`.

```
isContractibleMap→isEquiv : {f : A → B} → isContractibleMap f → isEquiv f
isContractibleMap→isEquiv {A = A} {B = B} {f = f} cf = packIsEquiv inv to-fro inv fro-to
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
map, and then use this to show that the original map underlying `e` is
contractible. 

Our strategy is to use ``isProp-with-point→isContr``, so our immediate
goal is to show that each fiber of `e .proof .section .map` is a
proposition. So fix an element `y : A`, and two elements of the fiber
over it, `(x₀, p₀)` and `(x₁ , p₁)`:

```
-- mvrnote: is there a way to split this line?
private module _ (e : A ≃ B) (y : A) (x₀ : B) (p₀ : y ≡ e .proof .section .map x₀) (x₁ : B) (p₁ : y ≡ e .proof .section .map x₁) where
```

Let's temporarily give shorter names to the components of the
equivalence `e`.

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
component. This is easy enough, using the fact that `g` is a section
of `f`.

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

You'll see very shortly why defining `path` in this symmetrical way
using ``∙∙`` is beneficial.

Now, a path between the points `x₀` and `x₁` in `B` is not enough, we
also need a path-over showing that `p₀` and `p₁` are equal. That is,
we need a square

    square : Square refl (ap g path) p₀ p₁

First, we'll compose the following cube, where the top face is nearly
what we want:

                        f p₁
               f y  — — — — — — > f (g x₁)
              / ^                 / ^
            /   |               /   |
          /     | f p₀        /     |
       f y  — — — — — — > f (g x₀)  | s x₁
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

```
  square-f : Square (ap f refl) (ap f (ap g path)) (ap f p₀) (ap f p₁)
  square-f i j = hcomp (∂ i ∨ ∂ j) faces
    where faces : (k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) B
          -- Exercise:
          faces k = {!!}
```

We just need to kill the extra `ap f` on all the sides. For this, we
use the fact that `g'` is a retract of `f`: we'll add an extra  `g'`,
then use `r` to cancel both `g'` and `f` out.

```
  square : Square refl (ap g path) p₀ p₁
  -- Exercise: (Hint: `homotopy-conjugate-Square` is nice here.)
  square = {!!}
```

So combining `path` and `square`, we get the path of between pairs
that we wanted.

```
  lemEquiv : (x₀ , p₀) ≡ (x₁ , p₁)
  -- Exercise:
  lemEquiv i = {!!}
```

The hard work is now done: every fiber of the section map is a
proposition. And we can easily find a point of each fiber, so every
fiber is contractible.

```
isEquiv→secIsContractibleMap : (e : A ≃ B) → isContractibleMap (e .proof .section .map)
-- Exercise:
isEquiv→secIsContractibleMap e y = isProp-with-point→isContr {!!} {!!}
```

We usually want to know that the actual map underlying an equivalence
is contractible, rather than the section map. To get this, we just
invert the equivalence and apply what we've just proven, because the
section used for the inverse is exactly the original map!

```
isEquiv→isContractibleMap : {f : A → B} → isEquiv f → isContractibleMap f
isEquiv→isContractibleMap isE = isEquiv→secIsContractibleMap (invEquiv (equiv _ isE))

Equiv→ContractibleMap : A ≃ B → ContractibleMap A B
Equiv→ContractibleMap (equiv f isE) = (f , isEquiv→isContractibleMap isE)
```


## Fact 1: Being an Equivalence is a Proposition

We now turn to the first of the goals that we listed up at the top:
showing that ``isEquiv`` is always a proposition. We'll do this by
showing that if we do have an element of `isEquiv f`, then in fact
`isEquiv f` is contractible. Our definition of ``isEquiv`` is as the
pair of a section and a retract, so the way we'll do it is showing
those two pieces are contractible separately.

First, some generalities about equivalences. These can both be proven
by defining an equivalence directly.

```
isEquiv→isEquiv-postComp : {f : A → B} → isEquiv f → isEquiv (λ (d : C → A) → f ∘ d)
-- Exercise:
isEquiv→isEquiv-postComp e = {!!}

-- mvrnote: exercise?
sectionOf≃fiber : (f : A → B) → SectionOf f ≃ (fiber (λ (d : B → A) → f ∘ d) idfun)
sectionOf≃fiber {A = A} {B = B} f = inv→equiv fun inv (λ _ → refl) (λ _ → refl)
  where
    fun : SectionOf f → (fiber (λ (d : B → A) → f ∘ d) idfun)
    fun s .fst = s .map 
    fun s .snd i b = s .proof b (~ i)

    inv : (fiber (λ (d : B → A) → f ∘ d) idfun) → SectionOf f 
    inv (g , s) .map = g 
    inv (g , s) .proof b i = s (~ i) b
```

The strategy should be clear: `sectionOf f` is equivalent to one of
the fibers of an equivalence, and because any equivalence is a
contractible map, that fiber is contractible. Put it together:

```
isEquiv→isContrSectionOf : {f : A → B} → isEquiv f → isContr (SectionOf f)
-- Exercise:
isEquiv→isContrSectionOf {f = f} isE = {!!}
```

::: Caution:
We have just shown that *if `f` is an equivalence*, its type of
sections is contractible. It is definitely not the case in general
that the type of sections of a map is contractible. 
:::

A symmetrical argument works for the retract, feel free to copy-paste
as appropriate.

```
isEquiv→isEquiv-preComp  : {f : A → B} → isEquiv f → isEquiv (λ (d : B → C) → d ∘ f)
-- Exercise:
isEquiv→isEquiv-preComp e = {!!}

retractOf≃fiber : (f : A → B) → RetractOf f ≃ (fiber (λ (d : B → A) → d ∘ f) idfun)
-- Exercise:
retractOf≃fiber f = {!!}

    inv : (fiber (λ (d : B → A) → d ∘ f) idfun) → RetractOf f 
    inv (g , s) .map = g
    inv (g , s) .proof b i = s (~ i) b

isEquiv→isContrRetractOf : {f : A → B} → isEquiv f → isContr (RetractOf f)
-- Exercise:
isEquiv→isContrRetractOf {f = f} isE = {!!}
```

Now just glue them together! (Using ``explode-isEquiv`` to pull it
apart will be helpful here).

```
isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
-- Exercise:
isProp-isEquiv f = with-point-isContr→isProp {!!}
```

As we showed in ``≡-in-subtype`` at the end of Lecture 2-X, paths in
subtypes can be calculated in the underlying type. Since the type `A ≃
B` of equivalences is a subtype of the type of functions `A → B`
(because now know``isEquiv`` is a proposition), we can compute paths
between equivalences on their underlying functions.

```
equiv≡ : {e f : A ≃ B} → (h : e .map ≡ f .map) → e ≡ f
-- Exercise:
equiv≡ {e = e} {f = f} h = {!!}
```

We knew already that univalence ``ua`` has a retract ``au``. But we
can now use ``equiv≡`` to show that ``au`` is also a section, and so
``ua`` is an equivalence.

```
au-ua : (e : A ≃ B) → au (ua e) ≡ e
-- Exercise: (Hint: ``ua-comp``)
au-ua e = {!!}
```

And prove univalence in all its glory:

```
univalence : (A ≡ B) ≃ (A ≃ B)
univalence = inv→equiv au ua au-ua ua-au
```


## Equivalence Induction

mvrnote: prose

```
isContr-singlEquiv : {A : Type ℓ} → isContr ( Σ[ T ∈ Type ℓ ] (A ≃ T) )
isContr-singlEquiv {A = A} .center = (A , idEquiv A)
isContr-singlEquiv .contraction (B , e) i .fst = ua e i
isContr-singlEquiv .contraction (B , e) i .snd .map a = Path→ua-PathP e {x = a} refl i
isContr-singlEquiv .contraction (B , e) i .snd .proof = isProp→PathP (λ j → isProp-isEquiv (λ a → Path→ua-PathP e refl j)) isEquiv-idfun (e .proof) i

Equiv-J : {B : Type ℓ}
  → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
  → P A (idEquiv A)
  → (e : A ≃ B)
  → P B e
Equiv-J {A = A} {B = B} P p e = subst (λ t → P (t .fst) (t .snd)) (isContr-singlEquiv .contraction (B , e)) p
```

```
ap-isEquiv : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → isEquiv (ap {x = a₁} {a₂} (e .map) )
ap-isEquiv e {a₁} {a₂} = Equiv-J (λ B e → isEquiv (ap {x = a₁} {a₂} (e .map))) isEquiv-idfun e

ap-≃ : {A B : Type ℓ} (e : A ≃ B) → {a₁ a₂ : A} → (a₁ ≡ a₂) ≃ (e .map a₁ ≡ e .map a₂)
ap-≃ e .map = ap (e .map)
ap-≃ e .proof = ap-isEquiv e
```

::: Aside:
Proving this kind of result using equivalence induction has the same
drawback as applying univalence directly (for example in
``×-map-≃-again``), in that the two input types *must* lie in the same
universe.

It is usually possible to give direct proofs, but for ``ap-≃`` the
direct proof is frankly a little fiddly and annoying, so we'll be
satisfied with the version using equivalence induction. mvrnote: reference
:::


## Being an Isomorphism is a Not Propositional

``isProp-isEquiv`` justifies our use of "equivalences" over
"isomorphisms". Recall that an isomorphism is a map with a single map going
the other way that is *both* a section and a retract.

```
record isIso {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  constructor isIsoData
  field
    inv : B → A
    sectionProof : isSection f inv -- hty?
    retractProof : isRetract f inv

open isIso
```

Sadly, this type is *not* always a proposition. This feels strange,
because in ordinary set-based mathematics, this defect is impossible
to see:

mvrnote: exercises?
```
iso-inv-unique : {f : A → B} → (i₁ i₂ : isIso f) 
  → (b : B) → i₁ .inv b ≡ i₂ .inv b
iso-inv-unique {f = f} i₁ i₂ b
  = i₁ .inv b               ≡⟨ sym (i₂ .retractProof (i₁ .inv b)) ⟩
    i₂ .inv (f (i₁ .inv b)) ≡⟨ ap (i₂ .inv) (i₁ .sectionProof b) ⟩
    i₂ .inv b ∎

isSet→isProp-isIso : {f : A → B}
  → isSet A → isSet B 
  → isProp (isIso f)
isSet→isProp-isIso isA isB iso₁ iso₂ i .inv b = iso-inv-unique iso₁ iso₂ b i
isSet→isProp-isIso {f = f} isA isB iso₁ iso₂ i .sectionProof b
  = isB _ _
    (transport-filler  (λ j → f (iso-inv-unique iso₁ iso₂ b j) ≡ b) (iso₁ .sectionProof b) i)
    (transport-filler' (λ j → f (iso-inv-unique iso₁ iso₂ b j) ≡ b) (iso₂ .sectionProof b) i)
    i
isSet→isProp-isIso {f = f} isA isB iso₁ iso₂ i .retractProof a
  = isA _ _
    (transport-filler  (λ j → iso-inv-unique iso₁ iso₂ (f a) j ≡ a) (iso₁ .retractProof a) i)
    (transport-filler' (λ j → iso-inv-unique iso₁ iso₂ (f a) j ≡ a) (iso₂ .retractProof a) i)
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
isIso→center i x = sym (i .sectionProof x) ∙ i .retractProof x
```

For sets this poses no problems, but if `X` is a higher-dimensional
type, there may be lots of non-equal elements of `(x : A) → (x ≡ x)`.
Indeed, we already encounter the problem when looking at the simplest
higher type, ``S¹``.

```
refl≢rotate-loop : ¬ ((λ _ → refl) ≡ rotate-loop)
-- Exercise:
refl≢rotate-loop p = {!!}
```

But now, here are two ways of showing that the identity function on
``S¹`` is an isomorphism.

```
S¹-refl-iso : isIso (idfun {A = S¹})
S¹-refl-iso .inv = idfun
S¹-refl-iso .sectionProof = λ _ → refl
S¹-refl-iso .retractProof = λ _ → refl

S¹-rotate-loop-iso : isIso (idfun {A = S¹})
S¹-rotate-loop-iso .inv = idfun
S¹-rotate-loop-iso .sectionProof = λ _ → refl
S¹-rotate-loop-iso .retractProof = rotate-loop
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

Σ-map-snd : {B : A → Type ℓ} {B' : A → Type ℓ'}
  → (f₂ : (a : A) → B a → B' a)
  → Σ[ a ∈ A ] B a → Σ[ a ∈ A ] B' a
Σ-map-snd f₂ = Σ-map idfun f₂
```

Dealing with the second component is easy, in fact, we could have done
it way back in Lecture 2-X.

```
Σ-map-snd-isEquiv : {B : A → Type ℓ} {B' : A → Type ℓ'} 
  → {f₂ : (a : A) → B a → B' a} 
  → ((a : A) → isEquiv (f₂ a)) 
  → isEquiv (Σ-map-snd f₂)
-- Exercise:
Σ-map-snd-isEquiv isE = {!!}

Σ-map-snd-≃ : {B : A → Type ℓ} {B' : A → Type ℓ'}
  → (e₂ : (x : A) → B x ≃ B' x)
  → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] B' a)
Σ-map-snd-≃ e₂ .map = Σ-map-snd (map ∘ e₂) 
Σ-map-snd-≃ e₂ .proof = Σ-map-snd-isEquiv (proof ∘ e₂)
```

The first component is the tough one, surprisingly difficult for such
a simple statement.

Here's the key fact, and what gives us the connection to contractible
maps. You will have to use the technology from Lecture 2-X on
``transport`` and ``transport-filler``.

```
Σ-map-fst-fib-≃ : {B : A' → Type ℓ}
  → (f₁ : A → A')
  → (t : Σ[ a' ∈ A' ] B a') 
  → fiber (Σ-map-fst f₁) t ≃ fiber f₁ (t .fst)
Σ-map-fst-fib-≃ {B = B} f₁ (a' , b') = inv→equiv to fro to-fro fro-to
  where
    to : fiber (Σ-map-fst f₁) (a' , b') → fiber f₁ a'
    -- Exercise:
    to ((a , b) , p) .fst = a

    fro : fiber f₁ a' → fiber (Σ-map-fst f₁) (a' , b')
    -- Exercise:
    fro (a , p) .fst .fst = a

    to-fro : isSection to fro
    to-fro (a , p) = refl

    fro-to : isRetract to fro
    -- Exercise:
    fro-to ((a , b) , p) i .fst .fst = a
```

mvrnote: this could alternatively be done by using J everywhere

Now, we know that `fiber (Σ-map-fst f₁) t` is contractible whenever
`fiber f₁ (t .fst)` is. Use ``isContractibleMap→isEquiv`` and
``isEquiv→isContractibleMap`` to complete the proof.

```
Σ-map-fst-isEquiv : {B : A' → Type ℓ}
  → (f₁ : A → A')
  → isEquiv f₁ 
  → isEquiv (Σ-map-fst {B = B} f₁)
-- Exercise:
Σ-map-fst-isEquiv f₁ e = isContractibleMap→isEquiv (λ t → isContr-equiv (Σ-map-fst-fib-≃ f₁ t) (isEquiv→isContractibleMap e (t .fst)))
```

Finally, combine ``Σ-map-fst-≃`` with ``Σ-map-snd-≃`` to prove the
original result were looking for.

```
Σ-map-≃ : {B : A → Type ℓ'} {B' : A' → Type ℓ'}
        → (e₁ : A ≃ A')
        → (e₂ : (a : A) → (B a) ≃ (B' (e₁ .map a)))
        → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')
Σ-map-≃ {A = A} {A' = A'} {B = B} {B' = B'} e₁ e₂ =
  Σ[ a  ∈ A  ] B  a           ≃⟨ Σ-map-snd-≃ e₂ ⟩
  Σ[ a  ∈ A  ] B' (e₁ .map a) ≃⟨ Σ-map-fst-≃ e₁ ⟩
  Σ[ a' ∈ A' ] B' a'          ∎e
```


## References and Further Reading

https://cj-xu.github.io/faum/escardo.pdf

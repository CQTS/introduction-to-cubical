```
module 2--Paths-and-Identifications.2-9--Contractible-Maps where
```


# Lecture 2-9: Contractible Maps

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
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C A' : Type ℓ
```
-->


In this Lecture we prove two crucial facts about equivalences:

* Being an equivalence is a *proposition* about a map, rather than
  extra structure. That is:

```
isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
```

* The formation of Σ-types respects equivalences. That is,

```
Σ-map-≃ : {B : A → Type ℓ} {B' : A' → Type ℓ'}
          → (e₁ : A ≃ A')
          → (e₂ : (x : A) → (B x) ≃ (B' (equivFun e₁ x)))
          → (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')
```

To prove both of these facts, it turns out to be easiest to detour
through an alternative definition of equivalences: contractible maps.


## Contractible Maps

In set theory, a bijection between sets $A$ and $B$ is defined to be a
function $f : A → B$ where for every $b ∈ B$, there is a unique $a ∈
A$ such that $f(a) = b$. We can turn this definition directly into
type theory:

```
isBijection : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isBijection {A = A} {B = B} f = (b : B) → ∃! (Σ[ a ∈ A ] (b ≡ f a))
```

The type inside the `∃!` comes up a lot, so it is given a name. The
``fiber`` of a function $f : A → B$ over an element $y : B$ is
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

This shape of definition comes up fairly often where we have a
property of types (in this case contractibility), and we use it to
define a property of maps by testing that property on all the fibers.
So, looking forward to other definitions of this kind, we're going to
rename the property of a map being a bijection to being
*contractible*.

```
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

-- ContractibleMapEq : {e f : ContractibleMap A B} → (h : e .fst ≡ f .fst) → e ≡ f
-- ContractibleMapEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsContractibleMap (h i)) (e .snd) (f .snd) i
```
mvrnote: compare this to ``Σ≡PropIso``?


## Equivalences are Contractible Maps

It is easy to show that any contractible map is an equivalence. Each
fiber is contractible, in particular, each fiber has a point, and we
can use these to define a function `B → A`.

```
isContractibleMap→isEquiv : {f : A → B} → isContractibleMap f → isEquiv f
isContractibleMap→isEquiv {A = A} {B = B} {f = f} isc = (inv , to-fro) , (inv , fro-to)
  where
    inv : B → A
--  Exercise:
    inv b = {!!}

    to-fro : isSection f inv
--  Exercise:
    to-fro = {!!}

    fro-to : isRetract f inv
--  Exercise:
    fro-to = {!!}
```

Going the other way, we can show that any equivalence is a
contractible map but the process is more involved.

Here's the setup: starting with an equivalence `e : A ≃ B`, we are
going to show that the provided *section* of `e` is a contractible
map. Then at the end, we'll use this to show that `e` itself is a
contractible map.

Here's the main Lemma that we're going to prove: the fiber of
`equivSec e` over any point `y : A` point is a proposition.

So we begin by supposing we have `y : A`, and two elements of the
fiber over it `(x0, p0)` and `(x1 , p1)`:

```
private module _ (e : A ≃ B) (y : A) (x₀ : B) (p₀ : y ≡ equivSec e x₀) (x₁ : B) (p₁ : y ≡ equivSec e x₁) where
```

And our goal is to show they are equal. First, we give shorter names
to the components of the equivalence `e`.

```
  private
    f = equivFun e
    g = equivSec e
    s : isSection f g
    s = equivIsSec e
    g' = equivRet e
    r : isSection g' f
    r = equivIsRet e
```

Our immediate goal is to produce a path `x₀ ≡ x₁`. This is easy enough
using the fact that `g` is a section of `f`.

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

You'll see immediately why defining `path₂` in that symmetrical way is
benificial.

Now, a path between the points `x₀` and `x₁` in `B` is not enough, we
also need a path-over between the paths `p₀` and `p₁` proving that
`x₀` and `x₁` are in the fiber over `y`, over the path we `x₀ ≡ x₁` we
just constructed. That is, we need a square

```
  square : Square refl (cong g path) p₀ p₁
```

We'll do this in two steps. First, we'll compose the following cube:

                        f p₁
               f y  - - - - - - > f g x₁
              / ^                 / ^
            /   |               /   |
          /     | f p₀        /     |
       f y  - - - - - - > f g x₀    | s x₁
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           | s x₀  |                    ∙ — >
        |       |           |       |                      i
        |      f y  - - - - | - - > x₁
        |     /       path₁ |     /
        |   /               |   / path
        | /                 | /
       f y  - - - - - - - > x₀
                path₀

The left square and right square are easy: constantly `f y` on the
left, and using the fact that `g` is a section on the right. For the
front, back, and bottom squares, observe that `path₀`, `path₁` and
`path` are defined as compositions, so we can use `∙-filler` and
`∙∙-filler` for the filled squares as appropriate.

```
  square-f-faces : (i : I) → (j : I) → (k : I) → Partial (∂ i ∨ ∂ j) B
  -- Exercise:
  square-f-faces i j k (i = i0) = {!!}
  square-f-faces i j k (i = i1) = {!!}
  square-f-faces i j k (j = i0) = {!!}
  square-f-faces i j k (j = i1) = {!!}

  square-f : Square (cong f refl) (cong f (cong g path)) (cong f p₀) (cong f p₁)
  -- Exercise:
  square-f i j = hcomp (square-f-faces i j) {!!}
```

This square is very nearly what we want: we just need to kill the
extra `cong f` on all the sides. For this, we use the fact that `g'`
is a retract of `f`: add an extra `g'`, then use `r` to cancel both
`g'` and `f` out. (There are multiple ways to do this, via
``transport`` or filling another cube.)

```
  -- square : Square refl (cong g path) p₀ p₁ (Given above.)
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
every fiber is contractible, via ``isProp→with-point-isContr``.

```
isEquiv→secIsContractibleMap : (e : A ≃ B) → isContractibleMap (equivSec e)
-- Exercise:
isEquiv→secIsContractibleMap e y = isProp→with-point-isContr {!!} {!!}
```

Now, we usually want to know that the actual function underlying an
equivalence is a contractible map, rather than the section. To get
this, we just invert the equivalence, because the section used for the
inverse is exactly the original map!

```
isEquiv→isContractibleMap : {f : A → B} → isEquiv f → isContractibleMap f
isEquiv→isContractibleMap isE = isEquiv→secIsContractibleMap (invEquiv (_ , isE))

Equiv→ContractibleMap : A ≃ B → ContractibleMap A B
Equiv→ContractibleMap (f , isE) = (f , isEquiv→isContractibleMap isE)
```


## Being an Equivalence is a Proposition

We now turn to the first of the goals that we listed up at the top:
showing that `isEquiv f` is always a proposition. We'll do this by
showing that if we do have an element of `isEquiv f`, then in fact
`isEquiv f` is contractible. Our definition of ``isEquiv`` is as
the pair of a section and a retraction, so this will mean showing that
those two pieces are contractible separately.

First, some generalities about equivalences. These can both be proven
by defining an equivalence directly.

```
isEquiv→isEquivPostComp : {f : A → B} → isEquiv f → isEquiv (λ (d : C → A) → f ∘ d)
-- Exercise:
fst (fst (isEquiv→isEquivPostComp ((g , s) , g' , r))) = {!!}
snd (fst (isEquiv→isEquivPostComp ((g , s) , g' , r))) = {!!}
fst (snd (isEquiv→isEquivPostComp ((g , s) , g' , r))) = {!!}
snd (snd (isEquiv→isEquivPostComp ((g , s) , g' , r))) = {!!}

sectionOf≃fiber : (f : A → B) → (sectionOf f) ≃ (fiber (λ (d : B → A) → f ∘ d) (idfun _))
-- Exercise:
sectionOf≃fiber f = {!!}
```

Now the strategy shoudl be clear: `sectionOf f` is equivalent to one
of the fibers of an equivalence, and because any equivalence is a
contractible map, that fiber is contractible. You should be able to
put it together:

```
isEquiv→isContrSectionOf : {f : A → B} → isEquiv f → isContr (sectionOf f)
-- Exercise:
isEquiv→isContrSectionOf {f = f} isE = {!!}
```

A symmetrical argument works for the retraction, feel free to
copy and paste as necessary.

```
isEquiv→isEquivPreComp  : {f : A → B} → isEquiv f → isEquiv (λ (d : B → C) → d ∘ f)
-- Exercise:
fst (fst (isEquiv→isEquivPreComp ((g , s) , g' , r))) d = {!!}
snd (fst (isEquiv→isEquivPreComp ((g , s) , g' , r))) d = {!!}
fst (snd (isEquiv→isEquivPreComp ((g , s) , g' , r))) d = {!!}
snd (snd (isEquiv→isEquivPreComp ((g , s) , g' , r))) d = {!!}

retractOf≃fiber : (f : A → B) → (retractOf f) ≃ (fiber (λ (d : B → A) → d ∘ f) (idfun _))
-- Exercise:
retractOf≃fiber f = {!!}

isEquiv→isContrRetractOf : {f : A → B} → isEquiv f → isContr (retractOf f)
-- Exercise:
isEquiv→isContrRetractOf {f = f} isE = {!!}
```

Now just glue them together!

```
-- Exercise:
isPropIsEquiv f = with-point-isContr→isProp {!!}
```

As we showed in `≡Subtype` at the end of Lecture 2-X, paths in subtypes
can be calculated in the underlying type. Since the type `A ≃ B` of
equivalences is a subtype of the type of functions `A → B` (because we
just showed `isEquiv f` is a proposition), we can compute paths
between equivalences on their underlying functions.

```
equivEq : {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
-- Exercise:
equivEq {e = e} {f = f} h = {!!}
```

We knew already that univalence ``ua`` has a retraction
``au``. But we can now use ``equivEq`` to easily show that
``ua`` is an equivalence.

```
au-ua : (e : A ≃ B) → au (ua e) ≡ e
-- Exercise: (Hint: `uaβ`)
au-ua e = {!!}
```

And state univalence in all its glory:

```
univalence : (A ≡ B) ≃ (A ≃ B)
univalence = equiv au ua au-ua ua-au
```


## Isomorphism is a Bad Definition

``isPropIsEquiv`` justifies our use of equivalences over
"isomorphisms", maps with a map going the other way that is *both* a
section and a retract.

```
isIso : {A : Type ℓ} → {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isIso f = Σ[ g ∈ _ ] isSection f g × isRetract f g
```

Sadly, this type is *not* always a proposition. This feels strange,
because in ordinary set-based mathematics, this defect is impossible
to see:

mvrnote: exercise?
```
isoInvUnique : {f : A → B} → (i₁ i₂ : isIso f) → (b : B) → fst i₁ b ≡ fst i₂ b
isoInvUnique {f = f} (g₁ , s₁ , r₁) (g₂ , s₂ , r₂) b =
                   g₁ b          ≡⟨ sym (r₂ (g₁ b)) ⟩
                   g₂ (f (g₁ b)) ≡⟨ cong g₂ (s₁ b) ⟩
                   g₂ b ∎

isSet→isPropIsIso : (f : A → B) → isSet A → isSet B → isProp (isIso f)
fst (isSet→isPropIsIso f isA isB iso₁ iso₂ i) b = isoInvUnique iso₁ iso₂ b i
fst (snd (isSet→isPropIsIso f isA isB iso₁ iso₂ i)) b
  = isB _ _
    (transport-filler  (λ j → f (isoInvUnique iso₁ iso₂ b j) ≡ b) (fst (snd iso₁) b) i)
    (transport-filler' (λ j → f (isoInvUnique iso₁ iso₂ b j) ≡ b) (fst (snd iso₂) b) i)
    i
snd (snd (isSet→isPropIsIso f isA isB iso₁ iso₂ i)) a
  = isA _ _
    (transport-filler  (λ j → isoInvUnique iso₁ iso₂ (f a) j ≡ a) (snd (snd iso₁) a) i)
    (transport-filler' (λ j → isoInvUnique iso₁ iso₂ (f a) j ≡ a) (snd (snd iso₂) a) i)
    i
```

In the world of homotopy type theory, however, the paths in
`isSection` and `isRetract` could hold extra data.

Consider the type of ways to show that the identity function `X → X`
is an isomorphism: that is, the type of functions `f : X → X` such
that `s : (x : X) → f x ≡ x` and `r : (x : X) → f x ≡ x`. By gluing
these together, we can get a path `x ≡ x` for any `x : X`.

```
isIso→center : isIso (idfun A) → (x : A) → (x ≡ x)
isIso→center (g , s , r) x = sym (s x) ∙ r x
```

For sets this poses no problem, but if `X` is a higher type, then
there may be lots of non-equal elements of that type `(x : A) → (x ≡
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
refl-iso : isIso (idfun S¹)
fst refl-iso = idfun S¹
fst (snd refl-iso) = λ _ → refl
snd (snd refl-iso) = λ _ → refl

rotate-loop-iso : isIso (idfun S¹)
fst rotate-loop-iso = idfun S¹
fst (snd rotate-loop-iso) = λ _ → refl
snd (snd rotate-loop-iso) = rotate-loop
```

If `isIso (idfun S¹)` were a proposition, then these would have to be
equal. This would imply that `(λ _ → refl) ≡ rotate-loop`, which we've
just shown cannot be.

```
¬isPropisIso : ¬ isProp (isIso (idfun S¹))
-- Exercise:
¬isPropisIso p = {!!}
```


## Σ-types Respect Equivalence

The second goal of this Lecture is to prove that an equivalence of the
components of a Σ-type extends to an equivalence of the entire Σ-type.

Dealing withthe second component is easier and only involves
rearranging some data, so let's do that first. The claim to prove is
that if we have a family of functions `(f₂ : (a : A) → B a → B' a)` so
that every `f₂ a` is an equivalence, then the map `(Σ[ a ∈ A ] B a) →
(Σ[ a ∈ A ] B' a)` is also an equivalence.

Proving this will involve a couple of lemmas about sections and
retractions, but at this point we trust you can put those together
yourself.

```
module _ {B : A → Type ℓ} {B' : A → Type ℓ'} (f₂ : (a : A) → B a → B' a) where
  Σ-map-snd : Σ[ a ∈ A ] B a → Σ[ a ∈ A ] B' a
  Σ-map-snd = Σ-map (idfun _) f₂

  Σ-map-snd-isEquiv : ((a : A) → isEquiv (f₂ a)) → isEquiv Σ-map-snd
  -- Exercise:
  Σ-map-snd-isEquiv e = {!!}

Σ-map-snd-≃ : {B : A → Type ℓ} {B' : A → Type ℓ'}
  (e₂ : (x : A) → B x ≃ B' x)
  → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] B' a)
Σ-map-snd-≃ e₂ = Σ-map-snd (equivFun ∘ e₂) , Σ-map-snd-isEquiv (fst ∘ e₂) (snd ∘ e₂)
```

Now, a similar fact for the first component: if `f₁ : A → A'` is an
equivalence, then the induced map
`(Σ[ a ∈ A ] B (f₁ a)) → (Σ[ a' ∈ A' ] B a')` is also an equivalene.

```
module _ {B : A' → Type ℓ} (f₁ : A → A') where
  Σ-map-fst : Σ[ a ∈ A ] B (f₁ a) → Σ[ a' ∈ A' ] B a'
  Σ-map-fst = Σ-map f₁ (λ x → idfun _)

  Σ-map-fst-isEquiv : isEquiv f₁ → isEquiv Σ-map-fst
```

This one is surprisingly difficult for such a simple statement. Here's
the key fact, and what makes the connection to contractible maps. You
will have to use the technology from Lecture 2-X on ``transport``
and ``transport-filler``.

```
  Σ-map-fst-fib-equiv : (t : Σ[ a' ∈ A' ] B a') → fiber Σ-map-fst t ≃ fiber f₁ (fst t)
  Σ-map-fst-fib-equiv (a' , b') = equiv to fro to-fro fro-to
    where
      to : fiber Σ-map-fst (a' , b') → fiber f₁ a'
      -- Exercise:
      fst (to ((a , b) , p)) = {!!}
      snd (to ((a , b) , p)) = {!!}

      fro : fiber f₁ a' → fiber Σ-map-fst (a' , b')
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
      snd (snd (fro-to ((a , b) , p) i) j) = {!!} -- This should can be done by a single, tricky use of `transp`
```

Now, we know that `fiber Σ-map-fst t` is contractible whenever `fiber
f₁ (fst t)` is. Use ``isContractibleMap→isEquiv`` and
``isEquiv→isContractibleMap`` to complete the proof.

```
  -- Exercise:
  Σ-map-fst-isEquiv e = {!!}

Σ-map-fst-≃ : {B : A' → Type ℓ}
  → (e₁ : A ≃ A')
  → (Σ[ a ∈ A ] B (fst e₁ a)) ≃ (Σ[ a' ∈ A' ] B a')
Σ-map-fst-≃ e₁ = Σ-map-fst (equivFun e₁) , Σ-map-fst-isEquiv (fst e₁) (snd e₁)
```

Finally, combine ``Σ-map-fst-≃`` with ``Σ-map-snd-≃`` to prove the
original result were looking for.

```
Σ-map-≃ e₁ e₂ = compEquiv (Σ-map-fst-≃ e₁) (Σ-map-snd-≃ e₂)
```

## mvrnote: to be sorted

Knowing what equivalences are in ``Σ`` types, we can
prove that `Σ[ a ∈ A ] B a` is a set whenever `A` is a set and `B a`
is a set for any `a : A`.

```
-- mvrnote: only place this is used
Σ-path-≃ :
  {A : Type ℓ} {B : A → Type ℓ'} (a b : Σ[ a ∈ A ] B a)
  → (a ≡ b) ≃ (Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b)
Σ-path-≃ {B = B} a b = compEquiv (Σ-map-snd-≃ (λ p → PathP≃Path (λ i → B (p i)) _ _)) (invEquiv ΣPath≃PathΣ)
```

compare `isSet×`

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


mvrnote: Exercise from the HoTT book:

```
-- table : (Bool → Bool) → Bool × Bool
-- table f = f true , f false

-- table-equiv : (f : Bool → Bool) → isEquiv f → (table f ≡ (true , false)) ⊎ (table f ≡ (false , true))
-- table-equiv = {!!}

-- test : (Bool ≃ Bool) ≃ Bool
-- test = equiv to fro to-fro fro-to
--   where to : (Bool ≃ Bool) → Bool
--         to e = equivFun e true
--         fro : Bool → (Bool ≃ Bool)
--         fro true = idEquiv Bool
--         fro false = not-≃
--         to-fro : isSection to fro
--         to-fro true = refl
--         to-fro false = refl

--         fro-to' : (f : Bool → Bool) → (e : isEquiv f) → (table f ≡ (true , false)) ⊎ (table f ≡ (false , true)) → fst (fro (to (f , e))) ≡ f
--         fro-to' f e (inl x) i true = {!!}
--         fro-to' f e (inl x) i false = {!!}
--         fro-to' f e (inr x) i b = {!!}

--         fro-to : isRetract to fro
--         fst (fro-to (f , (g , s) , g' , r) i) = {!!}
--         snd (fro-to (f , (g , s) , g' , r) i) = {!!}
```

## Relations

mvrnote: why did we have this section again?

mvrnote: GCD would be a cool exercise here!

A (type-valued) *relation* between two types `A` and `B` is a type
family `R : A → B → Type` depending on both `A` and `B`. We interpret
the type `R a b` as "the type of ways that `a` relates to `b`".

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
function ``flip`` defined way back in Lecture 1-1. A relation is
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

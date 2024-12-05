<!--
```
module 2--Paths-and-Identifications.2-6--Univalence where

open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import Library.Univalence

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' B B' C : Type ℓ
```
-->


# Lecture 2-6: Univalence

We've spent a lot of time characterising paths in the various types we
have available. The one type we haven't done this for is the universe
of types ``Type``.

Transport turns any path into an equivalence, as we showed in
``path→equiv``. But can every equivalence be produced this way? The
*univalence principle* says yes, that ``path→equiv`` is itself an
equivalence, and so every equivalence of types `A ≃ B` can be turned
back into a path of types `A ≡ B`.

In the original versions of Homotopy Type Theory, the univalence
principle is simply asserted as an axiom.

    univalence-axiom : {A B : Type ℓ} → isEquiv (path→equiv {A = A} {B = B})

If this principle is provided as an unproven axiom rather than
something with a definition, constructions involving it can't hope to
compute. For example, suppose we use this axiom to turn the
equivalence ``Bool≃RedOrBlue`` into a path `Bool ≡ RedOrBlue`. If we
transport ``true`` over this path, we would hope to get exactly
``red``, following the definition of the equivalence. But with the
above axiom, the transport expression is stuck and it has to be proven
manually that we indeed get ``red``.

Cubical Type Theory's central accomplishment is allowing the
univalence principle to compute in situations like this.

::: Aside:
Really, the original univalence axiom is defined in a setting that
uses "identity types" mvrnote: link (defined as the
inductive type that has the ``J`` rule as its eliminator) as its
notion of equality, rather than the cubical path types we have been
using. But the spirit is the same.
:::


## Glue Types

The feature of Cubical Type Theory needed for univalence is ``Glue``
types, a type constructor which has the following shape:

    Glue : (A : Type ℓ) {φ : I}
         → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
         → Type ℓ'

The type constructor ``Glue`` takes a type `A`, a formula `φ`, and a
partial element `Te : Partial φ (Σ[ T ∈ Type ] (T ≃ A))` of types
equipped with an equivalence to `A` (defined only when `φ` is ``i1``).

As usual, we should be thinking of ourselves in a context that already
has some interval variables in it, with `φ` a formula describing some
subcube.

Suppose we have an interval variable `i`, and let's fix the formula
`φ` to be `φ = ∂ i`. We can depict an element of the partial type `Te
: Partial (∂ i) (Σ[ T ∈ Type ℓ' ] T ≃ A)` as follows:

                 A i
         A i0  — — — > A i1
           ^             ^                ^
    Te i0  (             (  Te i1         )
           )             )                ∙ — >
         T i0          T i1                 i

where the vertical squiggly lines are equivalences rather than paths.
The type `A` is defined everywhere along the dimension `i`, but the
type `T` is only defined when `φ` holds, so on the left and right
sides.

This picture a lot like the kind of thing we were ``hcomp``ing over in
Lecture 2-X, except that it is open on the bottom rather than the top.
(This is a conventional choice --- the equivalences go into `A`,
rather than out of it.)

A ``Glue`` type enable us to "cap off" this open box of types, giving us a . That
is, if `φ = ∂ i`, then `Glue A Te : Type` is the line of types living
*under* `A` in the capped off version of the above square.

``Glue`` types come with some guarantees about how they compute in
special cases. Like ``hcomp``, the line we get agrees with the partial
input anywhere the formula `φ` holds. In the above case, this means

∙ `Glue A Te` is `T i0` when `i = i0` and
∙ `Glue A Te` is `T i1` when `i = i1`.

For any element of `Glue A Te`, regardless of whether `φ` holds, we
can extract an underlying element of `A`. This operation is called
`unglue φ`, and has type `Glue A Te → A`. Because of the above
guarantees, if `φ` does in fact hold then the domain of this function
is equal to `T`. Luckily, in this situation we have access to an
equivalence `T ≃ A`, because `Te` is defined when `φ` holds, and this
equivalence provides the necessary function `T → A`.

To summarise, `Glue A Te` is a version of `A` that has the types `T`
glued on wherever `φ` holds, using the provided equivalences `Te` to
extract an element of `A` whenever asked.

The first and most important example of a ``Glue`` type gives us an
inverse to the ``path→equiv`` map, building a path out of an
equivalence of types.

           B
      B — — — > B
      ^         ^                         ^
    e (         ( idEquiv                 )
      )         )                         ∙ — >
      A         B                           i


```
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B {φ = ∂ i}
  (λ { (i = i0) → (A , e)
     ; (i = i1) → (B , idEquiv B) })
```

That is, we use ``Glue`` to produce a version of `B` along a line in
the `i` dimension, but when `i` is `i0`, we glue `A` on using the
equivalence.

So how do we produce elements of ``Glue``? Thankfully, we will almost
never have to do so manually, but here's a place where it is useful:
converting between a path in `B` and a path-over `ua e` for some
equivalence.

```
Path→ua-PathP : (e : A ≃ B) {x : A} {y : B}
  → e .map x ≡ y
  → PathP (λ i → ua e i) x y
```

The ``glue`` constructor takes two arguments: first, a partial element
of the partial type `T` that we used in the ``Glue`` type itself.
After all, if we happen to be lying somewhere that `φ` equals `i1`,
the ``Glue`` type is supposed to turn into exactly `T`, so we have to
explain which value of `T` the ``glue`` is supposed to turn into.

The second argument is the value of `B` that will get used everywhere
that `φ` doesn't hold. Agda will check that the two arguments line up
with the equivalences you provided to the ``Glue`` type.

Annotating the above diagram, the values we are providing are

               p
   (e x) : B — — — > y : B
         ^             ^                  ^
       e (             ( idEquiv          )
         )             )                  ∙ — >
       x : A         y : B                 i

```
Path→ua-PathP e {x = x} {y = y} p i = glue {φ = ∂ i}
  (λ { (i = i0) → x ;
       (i = i1) → y })
  (p i)
```

The eliminator ``unglue`` works as you might expect on elements of
``Glue`` --- regardless of where we are in the ``Glue`` type, we can
extract an element of `B`.

```
ua-unglue : (e : A ≃ B) → (i : I) → (x : ua e i) → B
ua-unglue e i x = unglue (∂ i) x
```

When we happen to be somewhere that `φ` equals `i1`, this will mean
applying the equivalence that we provided to the ``Glue`` type
constructor.

```
module _ {ℓ : Level} {A B : Type ℓ} (e : A ≃ B) where
  _ = λ (x : ua e i0) → test-identical (ua-unglue e i0 x) (e .map x)
  _ = λ (x : ua e i1) → test-identical (ua-unglue e i1 x) x
```

Rearranging the arguments slightly, this is turned into an inverse to
``Path→ua-PathP``.

```
ua-PathP→Path : (e : A ≃ B) {x : A} {y : B}
 → PathP (λ i → ua e i) x y
 → e .map x ≡ y
ua-PathP→Path e p i = ua-unglue e i (p i)
```

These ``glue`` and ``unglue`` operations are inverses by definition,
and so no more work is necessary to show ``Path→ua-PathP`` is an
equivalence.

```
Path≃ua-PathP : (e : A ≃ B) {x : A} {y : B}
 → (e .map x ≡ y)
 ≃ (PathP (λ i → ua e i) x y)
Path≃ua-PathP e 
  = inv→equiv (Path→ua-PathP e) (ua-PathP→Path e) (λ _ → refl) (λ _ → refl)
```

When ``ua`` is applied to the identity equivalence on `A`, we get
the ``refl`` path from `A` to itself.

```
ua-idEquiv : ua (idEquiv A) ≡ refl
```

Written as a square, we are trying to construct the square of types
where on three of the sides we are constant at the type `A` and on the
remaining side we have `ua (idEquiv A)`.


                A — — — — — — — — > A
              / ^                 / ^
            /   )               /   )
          /     (             /     (
        A — — — — — — — — > A       )
        ^       (           ^       (                    ^   j
        )       )           )       )                    ) /
        (       (           (       (                    ∙ — >
        )       )           )       )                      i
        (       A — — — — — ( — — > A
        )                   )     /
        (                   (   /
        )                   ) /
        A — — — — — — — — > A

Using ``Glue`` again here with `(A , idEquiv A)` on all the
vertical faces gives us a square of types on the bottom. When `i =
i1`, `j = i0` or `j = i1`, this ``Glue``-type computes away to give
exactly `A`. When `i = i0`, we are left with the line of types 

    Glue A {φ = ∂ j} 
      (λ { (j = i0) → (A , idEquiv A)
         ; (j = i1) → (A , idEquiv A) })

but this is exactly the definition of `ua (idEquiv A)`.

```
ua-idEquiv {A = A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , idEquiv A)
```

Transporting over `ua e` is the same as applying the function
underlying the equivalence `e`. Really, we get a transport over
``refl``, which is cleared up by a use of ``transport-refl``. This is
an instance of the computation rule for ``transport`` on ``Glue``
types, which is very complicated in full generality.

```
ua-comp : (e : A ≃ B) → (x : A) → transport (ua e) x ≡ e .map x
ua-comp e x = transport-refl (e .map x)
```

For most types we encounter this holds definitionally the same way
that ``transport``ing over ``refl`` does, because in those cases the
``transport-refl`` above truly does become the reflexivity path. And
so Cubical Agda does achieve is the property we hoped for at the top
of this Lecture. 

```
_ = test-identical (transport (ua not-≃) true) false
_ = test-identical (transport (ua Bool≃RedOrBlue) true) red

_ = λ (e : Bool ≃ Bool) (x : Bool) 
  → test-identical (transport (ua e) x) (e .map x)

_ = λ (e : S¹ ≃ S¹) (x : S¹)
  → test-identical (transport (ua e) x) (e .map x)
```

Finally, univalence is inverse to ``path→equiv``. We show one half of
this now using ``J``, but will need to wait until Lecture 2-X to show
the other direction.

```
au : A ≡ B → A ≃ B
au = path→equiv

ua-au : (p : A ≡ B) → ua (au p) ≡ p
ua-au = J (λ _ p → ua (au p) ≡ p) path
  where path = ua (au refl)   ≡⟨ ap ua path→equiv-refl ⟩
               ua (idEquiv _) ≡⟨ ua-idEquiv ⟩
               refl ∎
```

Back in ``×-map-≃``, we saw that ``×`` respects equivalences.
Univalence gives us a second, much easier way to prove this:

```
×-map-≡ : {A A' B B' : Type ℓ}
  → (A ≡ A') → (B ≡ B') → (A × B) ≡ (A' × B')
-- Exercise:
×-map-≡ p q = {!!}

×-map-≃-ua : {A A' B B' : Type ℓ}
  → (A ≃ A') → (B ≃ B') → (A × B) ≃ (A' × B')
-- Exercise:
×-map-≃-ua f g = au {!!}
```

This is nice, but we now have to check that the underlying function of
this equivalence is the function we expect; that is, ``×-map``.
Thankfully, we checked in Lecture 2-X that transporting over a path
like ``×-map-≡`` computes to a transport in each of the components, so we
just have to use ``ua-comp`` on both sides to clear up those transports.

```
×-map-≃-underlying : {A A' B B' : Type ℓ} → (f : A ≃ A') → (g : B ≃ B')
  → (×-map-≃-ua f g) .map ≡ ×-map (f .map) (g .map)
-- Exercise:
×-map-≃-uat f g = {!!}
```

Then, we can transport the map proof that ``×-map-≃-ua`` is an
equivalence back over to the simpler map.

```
×-map-≃-again : {A A' B B' : Type ℓ}
  → (A ≃ A') → (B ≃ B') → (A × B) ≃ (A' × B')
×-map-≃-again f g .map = ×-map (f .map) (g .map)
×-map-≃-again f g .proof = subst isEquiv (×-map-≃-underlying f g) (×-map-≃-ua f g .proof)
```

There is a downside to proving this kind of equivalence using
univalence: ``×-map-≃-ua`` only works for types that all lie in the
same universe, whereas our original ``×-map`` is completely universe
polymorphic.


## Dependent Univalence

mvrnote: useful anywhere?

from Cubical.Foundations.Univalence.Dependent
```
-- module _
  -- {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'}
  -- (e : A ≃ B) (F : (a : A) → P a → Q (e .map a))
  -- (iseq : (a : A) → isEquiv (F a))
  -- where
  -- private
  --   -- Bundle `F` and `equiv` into a pointwise equivalence of `P` and `Q`:
  --   Γ : (a : A) → P a ≃ Q (e .map a)
  --   Γ a = equiv (F a) (iseq a)

  -- uaP : PathP (λ i → ua e i → Type ℓ') P Q
  -- uaP i x = Glue Base {∂ i} equiv-boundary where
  --   -- Like `ua`, `uaOver` is obtained from a line of
  --   -- Glue-types, except that they are glued
  --   -- over a line dependent on `ua e : A ≡ B`.

  --   -- `x` is a point along the path `A ≡ B` obtained
  --   -- from univalence, i.e. glueing over `B`:
  --   --
  --   --  A = = (ua e) = = B
  --   --  |                |
  --   -- (e)          (idEquiv B)
  --   --  |                |
  --   --  v                v
  --   --  B =====(B)====== B
  --   _ : Glue B {φ = i ∨ ~ i} (λ { (i = i0) → A , e ; (i = i1) → B , idEquiv B })
  --   _ = x

  --   -- We can therefore `unglue` it to obtain a term in the base line of `ua e`,
  --   -- i.e. term of type `B`:
  --   b : B
  --   b = unglue (∂ i) x

  --   -- This gives us a line `(i : I) ⊢ Base` in the universe of types,
  --   -- along which we can glue the equivalences `Γ x` and `idEquiv (Q x)`:
  --   --
  --   -- P (e x) = = = = = = Q x
  --   --    |                |
  --   --  (Γ x)        (idEquiv (Q x))
  --   --    |                |
  --   --    v                v
  --   --   Q x ===(Base)=== Q x
  --   Base : Type ℓ'
  --   Base = Q b

  --   equiv-boundary : Partial (∂ i) (Σ[ T ∈ Type ℓ' ] T ≃ Base)
  --   equiv-boundary (i = i0) = P x , Γ x
  --   equiv-boundary (i = i1) = Q x , idEquiv (Q x)

  --   -- Note that above `(i = i0) ⊢ x : A` and `(i = i1) ⊢ x : B`,
  --   -- thus `P x` and `Q x` are well-typed.
  --   _ : Partial i B
  --   _ = λ { (i = i1) → x }

  --   _ : Partial (~ i) A
  --   _ = λ { (i = i0) → x }
```

```
-- module _ {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'} (e₁ : A ≃ A') (e₂ : (x : A) → B x ≃ B' (e₁ .map x)) where
--   Σ-map-ua : (Σ[ a ∈ A ] B a) ≃ (Σ[ a' ∈ A' ] B' a')
--   Σ-map-ua = au λ i → Σ[ a ∈ ua e₁ i ] uaP e₁ (λ x → e₂ x .map) (λ x → e₂ x .proof) i a

--   Σ-map-ua-step1 : Σ-map-ua .map ≡ λ (a , b) → (transport (ua e₁) a) , transport (λ i → uaP {P = B} {Q = B'} e₁ (λ x → e₂ x .map) (λ x → e₂ x .proof) i (transport-filler (ua e₁) a i)) b
--   Σ-map-ua-step1 = refl

--   Σ-map-ua-underlying : Σ-map-ua .map ≡ Σ-map (e₁ .map) (λ a → e₂ a .map)
--   Σ-map-ua-underlying i (a , b) .fst = ua-comp e₁ a i
--   Σ-map-ua-underlying i (a , b) .snd = {!!}
```


## Addition as Path Composition

Here's a fun first application: we can implement addition in
``ℤ`` as composition of paths of type `ℤ ≡ ℤ`. This leads to a
one-line proof that addition is invertible.

We showed previously that ``sucℤ`` is an equivalence, and
univalence lets us turn this into a path `ℤ ≡ ℤ`.

```
sucℤ-≡ : ℤ ≡ ℤ
sucℤ-≡ = ua sucℤ-≃
```

This is the path that corresponds to adding 1, and by composing this
path with itself repeatedly we can produce a path that corresponds to
adding any fixed integer.

This iterated composition makes sense for any path starting and ending
at the same element, so we define it in general. For negative
integers, we simply compose with the inverse of the loop. There are
two ways to define it, repeatedly composing on the left or composing
on the right. This choice will matter for later definitions, so
compose on the ∙right∙.

```
iterateⁿ : {x : A} → x ≡ x → ℤ → x ≡ x
-- Exercise: (Remember to be careful with `negsuc`!)
iterateⁿ p z = {!!}

-- To make sure you composed the right way:
_ = λ {A : Type} {x : A} (p : x ≡ x) → test-identical (iterateⁿ p 2)    ((refl ∙ p) ∙ p)
_ = λ {A : Type} {x : A} (p : x ≡ x) → test-identical (iterateⁿ p (-2)) ((sym p) ∙ sym p)
```

Then the path corresponding to adding any fixed integer is:

```
add-ℤ-≡ : ℤ → ℤ ≡ ℤ
add-ℤ-≡ = iterateⁿ sucℤ-≡
```

Here's the upshot: we can define addition of integers by turning one
of them into a path using ``add-ℤ-≡`` and then transporting the other
integer along that path. Transport along a path created by univalence
applies the underlying function, which in this case is ``sucℤ``. And
so transporting along this path repeatedly indeed adds one integer to
the other!

```
_+ℤᵘ_ : ℤ → ℤ → ℤ
m +ℤᵘ n = transport (add-ℤ-≡ n) m

_ = test-identical (0 +ℤᵘ 0) 0
_ = test-identical (0 +ℤᵘ 1) 1
_ = test-identical (1 +ℤᵘ 0) 1
_ = test-identical (19 +ℤᵘ 34) 53
_ = test-identical (-19 +ℤᵘ 34) 15
```

It is easy to show that this always agrees with the ordinary addition
``+ℤ``, by case-splitting on `n`.

```
+ℤᵘ≡+ℤ : _+ℤᵘ_ ≡ _+ℤ_
-- Exercise:
+ℤᵘ≡+ℤ i m n = {!!}
```

Now, a nice trick. Because ``+ℤᵘ`` for a fixed `n` is defined via
``transport``, it is automatically an equivalence:

```
isEquiv-+ℤᵘ : (m : ℤ) → isEquiv (λ n → n +ℤᵘ m)
-- Exercise: (Hint: ``path→equiv``)
isEquiv-+ℤᵘ n = {!!}
```

And because we have just shown that ``+ℤᵘ`` is equal to
``+ℤ``, we get a proof that the same is true for ``+ℤ`` with
no extra effort.

```
isEquiv-+ℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
-- Exercise:
isEquiv-+ℤ = subst {!!} {!!} {!!}
```


## The Fundamental Group of the Circle

An amazing consequence of univalence is that it grants type theory
access to a lot of higher-dimensional homotopical structure. The
primary way it does this is by letting us construct interesting type
families.

Here's a first example: the "double cover" of the circle ``S¹``. This
is a type family with two elements over ``base``, for which
``transport``ing along the ``loop`` flips those two points.

```
not-Path : Bool ≡ Bool
not-Path = ua not-≃

double-cover : S¹ → Type
double-cover base = Bool
double-cover (loop i) = not-Path i
```

mvrnote: picture is mandatory here from hott game?

This type family lets us show that the circle is non-trivial, which is
a fact we didn't know for sure previously!

```
refl≢loop : ¬ (refl ≡ loop)
-- Exercise: (Hint: Use ``subst`` to prove `true ≡ false`.)
refl≢loop p = {!!}
```

::: Aside:
Without univalence or some other additional feature of type theory
beyond what we've seen so far, it is impossible to prove that ``S¹``
is nontrivial! With the bare constructions of type theory, it is
consistent to assume that ``S¹`` is contractible.
:::

There's nothing special about ``Bool`` here. Rather than placing
two points over each point of the circle, we could put an entire copy
of ``ℤ``:

```
helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤ-≡ i
```

In the remainder of this section we will prove a crucial fact about
``S¹``: that the type of paths from ``base`` to itself is equivalent
to the integers. That is, the following function is an equivalence:

```
loopⁿ : ℤ → base ≡ base
loopⁿ = iterateⁿ loop
```

This will be an encode-decode proof like those we did in Lecture 2-X,
with some slight differences which we will discuss when we encounter
them.

With the benefit of having done this before, we can tell you that the
following square is going to come in handy.

                              p
                         ∙ — — — — > ∙
                         ^           ^                      ^
    iterateⁿ p (predℤ n) |           | iterateⁿ p n       j |
                         |           |                      ∙ — >
                         ∙ — — — - > ∙                        i
                             refl

It can be constructed pretty easily by induction on `n`.

```
iterateⁿ-predℤ-square : {x : A} → (p : x ≡ x) → (n : ℤ) → Square (iterateⁿ p (predℤ n)) (iterateⁿ p n) refl p
-- Exercise: (Hint: `∙-filler`.)
iterateⁿ-predℤ-square p n i j = {!!}
```

Now let's jump straight into the proof.

```
ΩS¹≃ℤ : (base ≡ base) ≃ ℤ
ΩS¹≃ℤ = inv→equiv (encode base) (decode base) fro-to to-fro
  where
```

::: Aside:
In homotopy theory, the space of paths beginning and ending at a fixed
point of a space is called the *loop space* based at that point, and
is usually denoted using `Ω`.
:::

First, the codes for the paths. Because we are ultimately only
interested in `base ≡ base`, we just give codes for paths of the form
`base ≡ x`. For this, we use exactly the ``helix`` type family defined
above.

```
    code : S¹ → Type
    code = helix
```

Then ``encodeRefl`` and ``encode`` are defined as usual,
though ``encodeRefl`` is particularly simple because we only care
about ``base``.

```
    encodeRefl : code base
    encodeRefl = pos zero

    encode : (x : S¹) → base ≡ x → code x
    encode x p = J (λ y _ → code y) encodeRefl p
```

Now for ``decode``, which will take a lot more work.

```
    decode : (x : S¹) → code x → base ≡ x
```

We now case-split on `x`, so we will need to give cases for
``base`` and ``loop``. The ``base`` case is easy: we
have an element of `code base`, i.e. an integer, and we need to
produce a path `base ≡ base`. For this we have the function
``loopⁿ`` from earlier.

```
    decode base = loopⁿ
```

In the ``loop`` case, we will be asked to fill in the following
``SquareP``, where `y : code (loop i)`, or recalling the definition,
`y : sucℤ-≡ i`: (In the following diagrams, all the vertices are
always ``base``.)

                loop
            ∙ — — — — > ∙
            ^           ^                   ^
    loopⁿ y |           | loopⁿ y         j |
            |           |                   ∙ — >
            ∙ — — — — > ∙                     i
                refl

It might look odd to have `loopⁿ y j` on both sides: it seems it ought
to be impossible to fill this square, because we have `n` copies of
``loop`` going around one way and `n+1` copies going around the
other.

The reason is that the variable `y` has type `sucℤ-≡ i` rather than
being a a fixed integer: it varies along the type family `code (loop
i)` as `i` goes from ``i0`` to ``i1``. By the definition of ``helix``,
`y` has type ``ℤ`` when `i` is ``i0`` or ``i1``, but while moving
along the path between these, we have transported `n` to `suc n`. And
so the square should commute: going around either way should be `loopⁿ
(suc n)`.

We can build this square as an ``hcomp``. Here's the cube we are
going to fill, with the desired square sitting on the top.

                                      loop
                                ∙ — — — — — — — — > ∙
                    loopⁿ y   / ^                 / ^
                            /   |               / loopⁿ y
                          /     | refl        /     |
                        ∙ — — — — — — — — > ∙       |
                        ^       |           ^       |              ^   j
                        |       |           |       |            k | /
                        |       |           |       |              ∙ — >
                        |       |    loop   |       |                i
                        |       ∙ — — — — — | — — > ∙
    loopⁿ (predℤ (sucℤ y))    /             |     /
                        |   /               |   /  loopⁿ y
                        | /                 | /
                        ∙ — — — — — — — — > ∙
                                refl

Again, we have to be careful --- this is really a "Cube-over", because
the type of `y` varies over the `i` direction.

```
    decode (loop i) y j = hcomp (∂ i ∨ ∂ j) (decode-faces i y j)
      where
```

Three of the sides are easy, they are just squares that are constant
in one of the directions.

```
      decode-faces : (i : I) → (y : sucℤ-≡ i) → (j k : I) → Partial (∂ i ∨ ∂ j ∨ ~ k) S¹
      -- Exercise:
      decode-faces i y j k (i = i1) = loopⁿ y j
```

The `(i = i0)` face is slightly more interesting, here it is written
flat:

                loopⁿ y
            ∙ — — — — — > ∙
            ^             ^                  ^
       refl |             | refl           k |
            |             |                  ∙ — >
            ∙ — — — — — > ∙                    j
         loopⁿ (predℤ (sucℤ y))

A path `predℤ (sucℤ y) ≡ y` is provided by the retract part of the
equivalence ``sucℤ-≃``, so we can use that rather than reconstructing
the path. It just has to be surround with ``loopⁿ``.

```
      -- Exercise:
      decode-faces i y j k (i = i0) = {!!}
```

All that remains is to construct the base square and for this we have
to get our hands a little dirty. Written flat, this is the ``SquareP``

                               loop
                           ∙ — — — — > ∙
                           ^           ^                 ^
    loopⁿ (predℤ (sucℤ y)) |           | loopⁿ y       j |
                           |           |                 ∙ — >
                           ∙ — — — - > ∙                   i
                               refl

This is really close to the ``iterateⁿ-predℤ-square`` that we defined in
advance, which looks like this:

                               loop
                           ∙ — — — — > ∙
                           ^           ^                 ^
           loopⁿ (predℤ n) |           | loopⁿ n       j |
                           |           |                 ∙ — >
                           ∙ — — — - > ∙                   i
                               refl

To make these match, we need to supply an `n` that is equal to `sucℤ
y` on the left side and `y` on the right. This is exactly what
``unglue``-ing `y` gives us: on the left side we apply the equivalence
``sucℤ``, and on the right side, the identity equivalence.

```
      decode-faces i y j k (k = i0) = iterateⁿ-predℤ-square loop (ua-unglue sucℤ-≃ i y) i j
```

Checking that one composite is equal to the identity is easy using
``J`` as usual, because everything computes away to nothing when
the input path `p` is ``refl``:

```
    to-fro : isSection (decode base) (encode base)
    -- Exercise:
    to-fro p = J {!!} {!!} {!!}
```

And the other way can be verified by induction on ``ℤ``.
(Remember that `decode base` is exactly ``loopⁿ`` by definition, so
we don't have to worry about the complicated ``hcomp``.)

```
    fro-to : isRetract (decode base) (encode base)
    -- Exercise:
    fro-to n = {!!}
```

And we're done!


## Addition Yet Again

As a final demonstration in of univalence in this Lecture, let's use
the ``ΩS¹≃ℤ`` equivalence to define addition of integers yet another
time. We now know that ``ℤ`` is equivalent to `base ≡ base` so we can
do this by finding a binary operation on `S¹` corresponding to
addition.

Geometrically, this operation is easy to describe. For any two points
on the circle, look at their angles from the basepoint and add those
angles together. (Or phrased another way, consider ``S¹`` as the unit
circle in the complex plane, use multiplication of complex numbers.)

How do we describe this in type theory? If we fix one angle and let
the other one run from 0 to 360, the result runs around the circle
starting at the fixed angle. If we fix one of the points at `y` and
let the other run around `loop : base ≡ base`, we should get a path `y
≡ y` that also runs around ``S¹``. (Similar to ``loop`` itself, but
starting and ending at some point other than ``base``.)

```
rotate-loop : (y : S¹) → y ≡ y
-- Exercise: (Hint: We built the necessary square in Lecture 2-X!)
rotate-loop base       = loop
rotate-loop (loop i) j = {!!}
```

Now the actual multiplication. The point ``base`` of ``S¹`` lies at
angle 0, so it should not move the other point at all. And in the
``loop`` case, the above operation ``rotate-loop`` is exactly what we
need.

```
_·S¹_ : S¹ → S¹ → S¹
-- Exercise:
base   ·S¹ y = {!!}
loop i ·S¹ y = {!!}

infixl 30 _·S¹_
```

Now combine this multiplication with the ``ΩS¹≃ℤ`` equivalence:
turn `x` and `y` into loops, multiply them, and turn the resulting
loop back into an element of ``ℤ``.

```
_+ℤᵐ_ : ℤ → ℤ → ℤ
-- Exercise:
x +ℤᵐ y = equivFun ΩS¹≃ℤ {!!}

_ = test-identical (0 +ℤᵐ 0) 0
_ = test-identical (0 +ℤᵐ 1) 1
_ = test-identical (1 +ℤᵐ 0) 1
_ = test-identical (19 +ℤᵐ 34) 53
_ = test-identical (-19 +ℤᵐ 34) 15
```


## References and Further Reading

mvrnote: original proof for  S^1
proof of S^1 in other libraries
* https://arxiv.org/abs/1611.02108
  Cubical Type Theory: a constructive interpretation of the univalence axiom
  Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg


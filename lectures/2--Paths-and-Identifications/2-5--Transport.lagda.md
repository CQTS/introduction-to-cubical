```
module 2--Paths-and-Identifications.2-5--Transport where
```

# Lecture 2-5: Transport

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
```
-->

There is more to say about `transport`{.Agda} and the underlying
operation `transp`{.Agda}. Here is the actual definition of
`transport`{.Agda}, which we skipped when we first saw it in Lecture
2-1.

```
transport' : {A B : Type ℓ} → A ≡ B → A → B
transport' p a = transp (λ i → p i) i0 a
```

This uses the built-in `transp`{.Agda} operation which has type

```
_ = ∀ (φ : I) (A : (i : I) → Type) (a : A i0) → A i1
```

So, the `transp`{.Agda} operation takes in three arguments:

* `φ : I` is a *formula*,
* `A : I → Type ℓ` is a path in types, and
* `a : p i0` is an element of the type at the start of the path `A`

and the result is an element of the type at the other end of the path.

As usual, to understand the purpose of `φ`, we need to imagine that we
are in the context of some other cubical variables. The formula `φ`
expresses *where the transport is constant*. So `transport p x =
transp (λ i → p i) i0 x` is not constant anywhere, but `transport (λ _
→ A) i1 x` is constant everywhere and so definitionally equals `x`.
Agda will stop you if you demand `transp`{.Agda} be constant in a way
that doesn't make sense:

```
-- badtransp : {A B : Type ℓ} → A ≡ B → A → B
-- badtransp p a = transp (λ i → p i) i1 a
```

When transported along `p`, the element `a : A` becomes the element
`transport p a : B`. It seems reasonable for there to be a
`PathP`{.Agda} over the path `p` connecting `a` and `transport p a`,
and `transp`{.Agda} allows us to construct one:

```
transport-filler : (p : A ≡ B) (x : A)
                   → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x
```

In `transport-filler`{.Agda}, the transport is constant when `i = i0`,
in which case we can see that `(λ j → p (i0 ∧ j)) = (λ j → p i0)` is
also constant, and so we have that `transport-filler p x i0 = x`. When
`i = i1`, we have `~ i = i0` and `p (i1 ∧ j) = p j` so that
`transport-filler p x i1 = transp (λ j → p j) i0 x`, which is exactly
the definition of `transport p x`, so we see that the endpoints line
up.

Try using `transp`{.Agda} to prove that that transporting an element
`x : A` along the path of types that is constant at `A` gives back
`x`.

```
transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A)
               → transport (λ i → A) x ≡ x
-- Exercise:
transport-refl {A = A} x i = ?
```

To go the other way, we need a few functions which convert
paths-over-paths (i.e. `PathP`{.Agda}s) to paths involving
`transport`{.Agda}.

mvrnote: integrate this
```
PathP≡Path : ∀ (B : I → Type ℓ) (b1 : B i0) (b2 : B i1) →
             PathP B b1 b2 ≡ Path (B i1) (transport (λ i → B i) b1) b2
PathP≡Path B b1 b2 i =
  PathP (λ j → B (i ∨ j)) (transport-filler (λ j → B j) b1 i) b2
```

Now, returning to converting between `PathP`{.Agda} and paths involving
`transport`{.Agda}.  For the first conversion, `toPathP`, we need to do an
`hcomp`{.Agda} where the base is actually itself a `PathP`{.Agda}.
```
module _ {B : I → Type ℓ} {b1 : B i0} {b2 : B i1} where
  toPathP : transport (λ j → B j) b1 ≡ b2 → PathP B b1 b2
  {-

       b1 ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ >  b2
        ^                    ^
     b1 |                    | p                    ^
        |                    |                    j |
       b1 — — — > transport (λ j → B j) b1          ∙ — >
                                                      i
                B i
      B i0 — — — — — — — > B i1
  -}
  toPathP p i = hcomp (λ j → λ { (i = i0) → b1
                               ; (i = i1) → p j })
                      (transport-filler (λ j → B j) b1 i)
```

To go back the other way, we will use `transp`{.Agda} again but this
time in a different way. Now, when `i = i0` we want `fromPathP p i0 =
transport (λ i → B i) b1` and when `i = i1` we want `fromPathP p i1` =
b2`. So we will ask for `transp`{.Agda} to be constant when `i = i1`.

```
  fromPathP : PathP B b1 b2 → transport (λ i → B i) b1 ≡ b2
  fromPathP p i = transp (λ j → B (i ∨ j)) i (p i)
```

With these functions in hand, we can turn a family of propositions
into a predicate.

Recall from Lecture 2-5 the functions `toPathP`{.Agda} and
`fromPathP`{.Agda}:

These are an isomorphism. We've seen a path between the two types
before, in `PathP≡Path`{.Agda}. This is enough to produce an
isomorphism between the two types using `transport`{.Agda}. But
already have two maps `toPathP`{.Agda} and `fromPathP`{.Agda} between
these types, and we want those *specific* maps to be part of an
isomorphism. Verifying that they are inverse takes a lot more work,
unfortunately.

mvrnote: integrate

```
transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ p = transport (λ i → p (~ i))

transport-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-fillerExt p i x = transport-filler p x i

transport⁻-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → p i → A) (λ x → x) (transport⁻ p)
transport⁻-fillerExt p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → p i → B) (transport p) (λ x → x)
transport-fillerExt⁻ p = symP (transport⁻-fillerExt (sym p))

transport⁻-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → B → p i) (transport⁻ p) (λ x → x)
transport⁻-fillerExt⁻ p = symP (transport-fillerExt (sym p))

transport⁻Transport : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (a : A) →
                          transport⁻ p (transport p a) ≡ a
transport⁻Transport p a j = transport⁻-fillerExt p (~ j) (transport-fillerExt p (~ j) a)

transportTransport⁻ : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (b : B) →
                        transport p (transport⁻ p b) ≡ b
transportTransport⁻ p b j = transport-fillerExt⁻ p j (transport⁻-fillerExt⁻ p j b)

pathToIso : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → Iso A B
Iso.fun (pathToIso x) = transport x
Iso.inv (pathToIso x) = transport⁻ x
Iso.rightInv (pathToIso x) = transportTransport⁻ x
Iso.leftInv (pathToIso x) = transport⁻Transport x

PathP-iso-Path : ∀ (A : I → Type ℓ) (x : A i0) (y : A i1) → Iso (PathP A x y) (transport (λ i → A i) x ≡ y)
PathP-iso-Path A x y = pathToIso (PathP≡Path A x y)
```

## Transport Computes

Here are some examples of transporting in paths of types. If the path
of types is constant at an inductive type such as `ℕ`{.Agda} or
`Bool`{.Agda}, then transporting is simply the identity.

```
_ : {x : ℕ} → transport (λ i → ℕ) x ≡ x
_ = refl

_ : {b : Bool} → transport (λ i → Bool) b ≡ b
_ = refl
```

If we don't know anything about the type `A`, however, transporting
over a constant path is not by definition the identity.

```
{- Error!
_ : {x : A} → transport (λ _ → A) x ≡ x
_ = refl
-}
```

In the basic type formers that we have (pairs, functions, paths),
`transport`{.Agda} in the compound type is computes to some
combination of `transport`{.Agda}s in the input types.

```
module _ {A : I → Type} {B : I → Type} where private
```

To transport in a type of pairs, we just transport in each component:

```
  _ : {x : A i0} {y : B i0}
    →   transport (λ i → A i × B i) (x , y)
      ≡ (transport (λ i → A i) x , transport (λ i → B i) y)
  _ = refl

```

To transport in a type of functions, we transport *backwards* along
the domain, then apply the function, and then transport forwards along
the codomain:

```
  _ : {f : A i0 → B i0}
    →   transport (λ i → A i → B i) f
      ≡ λ x → transport (λ i → B i) (f (transport (λ i → A (~ i)) x))
  _ = refl
```

This is because `f : A i0 → B i0`, but `transport (λ i → A i → B i) f`
has to be a function `A i1 → B i1`, so to apply `f` to an element of
`A i1`, we first need to pull it back to `A i0`.

`transport`{.Agda} in a path type becomes a (double) composition, the
top of the following square:


               a i1 ∙ ∙ ∙ ∙ ∙ ∙ > b i1
                ^                   ^
                |                   |              ^
                |                   |            j |
          tr A (a i0) — — — > tr A (b i0)          ∙ — >
                                                     i

This is now a square entirely in the type `A i1`, and so the
`transport`{.Agda} may compute further depending on what `A i1` is.

```
module _ {A : I → Type} {a : (i : I) → A i} {b : (i : I) → A i} where private
  _ : {p : a i0 ≡ b i0}
    → transport (λ i → a i ≡ b i) p
    {- Exercise:
    ≡ ?
    -}
    ≡ sym (fromPathP (λ i → a i)) ∙∙ cong (transport (λ i → A i)) p ∙∙ fromPathP (λ i → b i)
  _ = refl

```

`PathP`{.Agda} is similar, but we have to write the `hcomp`{.Agda} manually, becuase
`∙∙`{.Agda} is only defined for ordinary paths.

```
module _ {A : I → I → Type} {a : (i : I) → A i i0} {b : (i : I) → A i i1} where private
  _ : {p : PathP (A i0) (a i0) (b i0)}
    → transport (λ i → PathP (A i) (a i) (b i)) p
    ≡ λ j → hcomp (λ i → λ { (j = i0) → fromPathP (λ i → a i) i;
                             (j = i1) → fromPathP (λ i → b i) i } )
            (transport (λ i → A i j) (p j))
  _ = refl
```

We can mix and match these. Here is how a "`B`-valued binary operation
on `A`" would transport:

```
module _ {A : I → Type} {B : I → Type} where private

  _ : {m : A i0 × A i0 → B i0}
    → transport (λ i → A i × A i → B i) m
    ≡ λ {(x , y) →
      let
        x' = (transport (λ i → A (~ i)) x)
        y' = (transport (λ i → A (~ i)) y)
      in transport (λ i → B i) (m (x' , y'))}
  _ = refl
```

Here's how a function into `Bool`{.Agda} would transport:

```
  _ : {p : A i0 → Bool}
    → transport (λ i → A i → Bool) p
    ≡ λ x → p (transport (λ i → A (~ i)) x)
  _ = refl
```

Try it yourself:

```
  _ : {m : A i0 × A i0 → A i0}
    → transport (λ i → A i × A i → A i) m
    ≡ λ { (x , y) →
        let
          x' = transport (λ i → A (~ i)) x
          y' = transport (λ i → A (~ i)) y
        in transport (λ i → A i) (m (x' , y'))
      }
  {- Exercise:
  _ : {m : A i0 × A i0 → A i0}
    → transport (λ i → A i × A i → A i) m
    ≡ ?
  -}
  _ = refl

  _ : {α : A i0 × B i0 → B i0}
    → transport (λ i → A i × B i → B i) α
    ≡ λ { (a , b) →
        let
          a' = transport (λ i → A (~ i)) a
          b' = transport (λ i → B (~ i)) b
        in transport (λ i → B i) (α (a' , b'))
      }
  {- Exercise:
  _ : {α : A i0 × B i0 → B i0}
    → transport (λ i → A i × B i → B i) α
    ≡ ?
  -}
  _ = refl

  _ : {y : (A i0 → A i0) → A i0}
    → transport (λ i → (A i → A i) → A i) y
    ≡ λ f →
      let f' = λ a → transport (λ i → A (~ i)) (f (transport (λ i → A i) a))
      in transport (λ i → A i) (y f')
  {- Exercise:
  _ : {y : (A i0 → A i0) → A i0}
    → transport (λ i → (A i → A i) → A i) y
    ≡ ?
  -}
  _ = refl
```

## Transport Computes, Dependently

There are dependent versions of the above computation rules for
`transport`{.Agda}. They follow the same pattern as above, but further
work is necessary so that things still typecheck.

```
module _ {A : I → Type} {B : (i : I) → A i → Type} where private
  _ : {x0 : A i0} {y0 : B i0 x0}
    → transport (λ i → Σ[ x ∈ A i ] B i x) (x0 , y0)
    {- Exercise:
    ≡ let
          -- This is just the same as in the non-dependent case
          x1 : A i1
          x1 = transport (λ i → A i) x0

          -- Here we need a path from `B i0 x0` to `B i1 x1`
          y1 = transport ? y0
        in (x1 , y1)
    -}
    ≡ let
          x1 : A i1
          x1 = transport (λ i → A i) x0

          x0≡x1 : PathP (λ i → A i) x0 x1
          x0≡x1 = transport-filler (λ i → A i) x0

          y1 = transport (λ i → B i (x0≡x1 i)) y0
        in (x1 , y1)
  _ = refl

  _ : {f : (x0 : A i0) → B i0 x0}
    → transport (λ i → (x : A i) → B i x) f
    {- Exercise:
    ≡ λ (x1 : A i1) →
        let
          x0 : A i0
          x0 = transport (λ i → A (~ i)) x1

          fx1 : B i1 x1
          fx1 = transport ? (f x0)
        in fx1
    -}
    ≡ λ (x1 : A i1) →
        let
          x0 : A i0
          x0 = transport (λ i → A (~ i)) x1

          x0≡x1 : PathP (λ i → A i) x0 x1
          x0≡x1 j = transport-filler (λ i → A (~ i)) x1 (~ j)

          fx1 : B i1 x1
          fx1 = transport (λ i → B i (x0≡x1 i)) (f x0)
        in fx1
  _ = refl
```

```
module 2--Paths-and-Identifications.2-5--Transport where
```

# Lecture 2-5: Transport

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

private
  variable
    ℓ ℓ' : Level
    A A' B C : Type ℓ
    x y : A
```
-->

In this lecture, we will revisit ``transport`` and the underlying
operation ``transp``, equipped with the intuition for partial
elements that we developed in the previous lecture. Here is the actual
definition of ``transport`` which we skipped when we first saw
it in Lecture 2-X.

```
transport' : {A B : Type ℓ} → A ≡ B → A → B
transport' p a = transp (λ i → p i) i0 a
```

This uses the built-in ``transp`` operation which has type

```
_ = (φ : I) → (A : (i : I) → Type) → A i0 → A i1
```

That is, the ``transp`` operation takes in three arguments:

* `φ : I` is a *formula*,
* `A : I → Type ℓ` is a path in types, and
* `a : p i0` is an element of the type at the start of the path `A`,

and the result is an element of the type at the other end of the path.

As usual, to understand the purpose of `φ`, we need to imagine we are
in the context of some other cubical variables. The formula `φ`
expresses the parts of the cube *where the transport is constant*. So
`transport p x = transp (λ i → p i) i0 x` is not constant anywhere,
but `transp (λ _ → A) i1 x` is constant everywhere and so
definitionally equals `x`.

```
_ : {A : Type ℓ} (a : A)
  → transp (λ _ → A) i1 a ≡ a
_ = λ x → refl
```

Agda will stop you if you demand ``transp`` be constant in a way
that doesn't make sense, like claiming that our original definition of
``transport`` is constant everywhere:

```
-- badtransp : {A B : Type ℓ} → A ≡ B → A → B
-- badtransp p a = transp (λ i → p i) i1 a
```

Here's an application. When ``transport``ed along `p`, the
element `a : A` becomes the element `transport p a : B`. It seems
reasonable for there to be a ``PathP`` over the path `p`
connecting `a` and `transport p a`, and ``transp`` allows us to
construct one:

```
transport-filler : (p : A ≡ B) (a : A)
  → PathP (λ i → p i) a (transport p a)
transport-filler p a i = transp (λ j → p (i ∧ j)) (~ i) a
```

Lets break this down. In ``transport-filler``, the
``transp`` is constant when `i = i0`, in which case we can see
that `(λ j → p (i0 ∧ j)) = (λ j → p i0)` is also constant, and so we
have that `transport-filler p x i0 = x`. When `i = i1`, we have `~ i =
i0` and `p (i1 ∧ j) = p j` so that `transport-filler p x i1 = transp
(λ j → p j) i0 x`, which is exactly the definition of `transport p x`,
so we see that the endpoints line up.

With a similar definition, we can show the same for elements of `B`,
transporting `x` backwards along `p` is connected via a path-over to
`x`.

```
transport-filler' : (p : A ≡ B) (b : B)
  → PathP (λ i → p i) (transport (sym p) b) b
-- Ebercise:
-- transport-filler' p b i = {!!}
transport-filler' p b i = transp (λ j → p (i ∨ ~ j)) i b
```

mvrnote: text

```
subst-filler : (B : A → Type ℓ) (p : x ≡ y) → (b : B x)
  → PathP (λ i → B (p i)) b (subst B p b)
subst-filler B p = transport-filler (λ i → B (p i))
```

Try using ``transp`` to prove that that transporting an element
`x : A` along the constant path of types at `A` gives back `x`.

```
transport-refl : (a : A) → transport (λ i → A) a ≡ a
-- Eaercise:
-- transport-refl {A = A} a i = {!!}
transport-refl {A = A} a i = transp (λ _ → A) i a
```

We can also show that transporting along `sym p` and then transporting
along `p` puts us right back where we were.

Hint: The goal normalizes to the expression `transp (λ i → p i) i0
(transp (λ i → p (~ i)) i0 b)`, which you can check by hitting `C-c
C-,`. So, you will have to engineer an expression also involving `j`
which reduces to this large expression when `j = i0` and which
simplifies to just `b` when `j = i1`. For the latter, remember that
`transp (λ _ → A) i1 x = x`.

```
transport-cancel : (p : A ≡ B) (b : B)
  → transport (λ i → p i) (transport (λ i → p (~ i)) b) ≡ b
-- Exercise:
transport-cancel p b j = {!!}
```

With ``transport-cancel`` in hand, we can show that `transport p`
is an equivalence of types with inverse `transport (sym p)`.

```
pathToEquiv : A ≡ B → A ≃ B
pathToEquiv p = equiv (transport p) (transport (sym p))
                      (transport-cancel p) (transport-cancel (sym p))
```

And with a little effort, we can show that the equivalence constructed
by this function on ``refl`` is equal to the obvious
``idEquiv`` from earlier. This can be done with several uses of
``transport-refl``, or you can use ``transp`` directly.

```
pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} i = (λ x → transport-refl x i) , sec , ret
  -- Exercise: (Hint: Use a couple of connection squares!)
  where sec : sectionOf (λ x → transport-refl x i)
        fst sec x = {!!}
        snd sec a = {!!}

        ret : retractOf (λ x → transport-refl x i)
        fst ret x = {!!}
        snd ret a = {!!}

        ret : retractOf (λ x → transport-refl x i)
        fst ret x = transport-refl x i
        snd ret a = connection∨ (λ j → transport-refl (transport-refl a j) j) i
```

There is a second way that ``PathP`` and ``transport``
relate. Recall that an element of `PathP A a0 a1` connects two
elements `a0 : A i0` and `a1 : A i1` of the types at either end of a
line of types `A : I → Type`. Instead of travelling along the line
`A`, we could first transport the endpoint `a0` over to the type `A
i1`, and then ask for a path entirely inside `A i1`. That is, we can
always convert a `PathP` into an ordinary `Path` involving a
transport, and vice versa.

mvrnote: this would benefit from a nice picture

For the first conversion, ``toPathP``, we need to do an
``hcomp`` where the base is actually itself a ``PathP``.

      a1 ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ > a2
       ^                    ^
    a1 |                    | p                    ^
       |                    |                    j |
      a1 — — — > transport (λ j → A j) a1          ∙ — >
                                                     i
                A i
     A i0 — — — — — — — - > A i1

```
toPathP : {A : I → Type ℓ} {a1 : A i0} {a2 : A i1}
  → Path (A i1) (transport (λ j → A j) a1) a2
  → PathP A a1 a2
toPathP {A = A} {a1} {a2} p i
  = hcomp (λ j → λ { (i = i0) → a1
                   ; (i = i1) → p j })
          (transport-filler (λ j → A j) a1 i)
```

To go back the other way, we will use ``transp`` again, but in a
different way. When `i = i0` we want `fromPathP p i0 = transport (λ i
→ B i) b1` and when `i = i1` we want `fromPathP p i1` = b2`. So we
will ask for ``transp`` to be constant when `i = i1`.

```
fromPathP : {A : I → Type ℓ} {a1 : A i0} {a2 : A i1}
  → PathP A a1 a2
  → Path (A i1) (transport (λ j → A j) a1) a2
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)
```

These two maps are inverses. Unfortunately, this is a real pain to
show, involving some really gnarly `hcomp`s. So, we will cheat, and
produce an equivalence an entirely different way.

```
PathP≡Path : (A : I → Type ℓ) (a1 : A i0) (a2 : A i1)
  → PathP A a1 a2 ≡ Path (A i1) (transport (λ i → A i) a1) a2
PathP≡Path A a1 a2 i =
  PathP (λ j → A (i ∨ j)) (transport-filler (λ j → A j) a1 i) a2

PathP≃Path : (A : I → Type ℓ) (x : A i0) (y : A i1)
  → (PathP A x y) ≃ (transport (λ i → A i) x ≡ y)
PathP≃Path A x y = pathToEquiv (PathP≡Path A x y)
```

This certainly gives an equivalence, but the forward and backward maps
are not the nice ``toPathP`` and ``fromPathP`` maps that we
defined above. For our purposes, this simpler equivalence is good
enough.


## Transport Computes

Because ``transp`` is built-in, it comes withs some magic that
makes it convenient when used with specific types. Here are some
examples.

If the path of types is constant at an inductive type such as
``ℕ`` or ``Bool``, then transporting is simply the identity.

```
_ : {x : ℕ} → transport (λ i → ℕ) x ≡ x
_ = refl

_ : {b : Bool} → transport (λ i → Bool) b ≡ b
_ = refl
```

If we don't know anything about the type `A`, however, transporting
over a constant path is not by definition the identity.
(Unfortunately!)

```
{- Error!
_ : {x : A} → transport (λ _ → A) x ≡ x
_ = refl
-}
```

For the basic type formers that we have seen (pairs, functions,
paths), ``transport`` computes to some combination of
``transport``s involving the input types.

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
the domain, apply the function, and then transport forwards along the
codomain:

```
  _ : {f : A i0 → B i0}
    →   transport (λ i → A i → B i) f
      ≡ λ x → transport (λ i → B i) (f (transport (λ i → A (~ i)) x))
  _ = refl
```

This is the only way this could fit together, because the input has
type `f : A i0 → B i0`, but `transport (λ i → A i → B i) f` needs to
be a function `A i1 → B i1`. To apply `f` to an element of `A i1`, we
first need to pull it back to `A i0`.

``transport`` in a path type becomes a (double) composition, the
top of the following square:


               a i1 ∙ ∙ ∙ ∙ ∙ ∙ > b i1
                ^                   ^
                |                   |              ^
                |                   |            j |
          tr A (a i0) — — — > tr A (b i0)          ∙ — >
                                                     i

This is now a square entirely in the type `A i1`, and so the
``transport`` may compute further depending on what `A i1` is.

```
module _ {A : I → Type} {a : (i : I) → A i} {b : (i : I) → A i} where private
  _ : {p : a i0 ≡ b i0}
    → transport (λ i → a i ≡ b i) p
      -- Exercise:
      ≡ {!!}
```

``PathP`` is similar, but we have to write the ``hcomp``
manually, becuase ``∙∙`` is only defined for ordinary paths.

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
on `A`" would transport. This just decomposes into transport
(backwards) in the pair, followed by application of the function, then
transport forwards of the result:

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

And here's how a function into ``Bool`` transports. As we have
seen, transport in ``Bool`` disappears, so in-fact we only have
to transport the input.

```
  _ : {p : A i0 → Bool}
    → transport (λ i → A i → Bool) p
    ≡ λ x → p (transport (λ i → A (~ i)) x)
  _ = refl
```

Try it yourself:

```
  -- Exercise:
  _ : {m : A i0 × A i0 → A i0}
    → transport (λ i → A i × A i → A i) m
      ≡ λ { (x , y) →
          {!!}
        }

  _ = refl

  -- Exercise:
  _ : {α : A i0 × B i0 → B i0}
    → transport (λ i → A i × B i → B i) α
      ≡ {!!}

  _ = refl

  -- Exercise:
  _ : {y : (A i0 → A i0) → A i0}
    → transport (λ i → (A i → A i) → A i) y
      ≡ ?

  _ = refl
```


## Transport Computes, Dependently

There are dependent versions of the above computation rules for
``transport``. They follow the same pattern as above, but further
work is necessary so that things still typecheck.

```
module _ {A : I → Type} {B : (i : I) → A i → Type} where private
  _ : {x0 : A i0} {y0 : B i0 x0}
    → transport (λ i → Σ[ x ∈ A i ] B i x) (x0 , y0)
    -- Exercise:
    ≡ let
          -- This is just the same as in the non-dependent case
          x1 : A i1
          x1 = {!!}

    --       -- Here we need a path from `B i0 x0` to `B i1 x1`
    --       y1 = transport {!!} y0
    --     in (x1 , y1)
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
    -- Exercise:
    ≡ λ (x1 : A i1) →
        let
          x0 : A i0
          x0 = transport (λ i → A (~ i)) x1

    --       fx1 : B i1 x1
    --       fx1 = transport ? (f x0)
    --     in fx1
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

mvrnote: Favonia exercise
{- BONUS: define comp in terms of hcomp and transp -}

  mycomp : {ℓ : Level} (A : I → Type ℓ) -- A may change along the dimension
           {φ : I}
           (u : ∀ i → Partial φ (A i)) -- the type of u may change along the dimension
           (u0 : A i0 [ φ ↦ u i0 ])
           → A i1

```
module 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra where
```

# Lecture 2-2: Isomorphisms and Path Algebra

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
    x y : A
```
-->

We have enough tools now to define an *isomorphism* between two
types. "Isomorphism" is a faux-Greek word meaning "same shape" ---
"iso-" and "morph". The idea of an isomorphism between two types is
that these types contain equivalent data.

Explicitly, an isomorphism between types `A` and `B` will be a pair
of maps `f : A → B` and `g : B → A` so that `f ∘ g ≡ id` and `g ∘ f ≡
id`. In other words, we can transform data of type `A` into data of
type `B` and vice versa, so that if we go from `A` to `B` and back
again, we get back to where we started.

If `f ∘ g ≡ id`, we say that `g` is a *section* of `f`, and if `g ∘ f
≡ id` we say that `g` is a *retract* of `f`.

```
section : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → (g : B → A) → Type ℓ'
section f g = ∀ b → f (g b) ≡ b

  -- Note: `g` is the retraction!
retract : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → (g : B → A) → Type ℓ
retract f g = ∀ a → g (f a) ≡ a
```

An isomorphism is therefore a function `f : A → B` with an inverse map
`g : B → A` so that `g` is both a section and a retract of `f`. We
will package this up into an iterated pair type.

```
Iso : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Iso A B = Σ[ fun ∈ (A → B) ]
          Σ[ inv ∈ (B → A) ]
          section fun inv ×
          retract fun inv
```

To make these less annoying to work with, we'll write some helpers for
constructing and destructing these `Iso`s.

```
iso : (fun : A → B)
    → (inv : B → A)
    → (rightInv : section fun inv)
    → (leftInv  : retract fun inv)
    → Iso A B
iso fun inv rightInv leftInv = fun , inv , rightInv , leftInv

isoFun : Iso A B → (A → B)
isoFun iso = fst iso
isoInv : Iso A B → (B → A)
isoInv iso = fst (snd iso)
isoRightInv : (iso : Iso A B) → section (isoFun iso) (isoInv iso)
isoRightInv iso = fst (snd (snd iso))
isoLeftInv : (iso : Iso A B) → retract (isoFun iso) (isoInv iso)
isoLeftInv iso = snd (snd (snd iso))
```

mvrnote: discuss records?

Here's a couple of basic examples. First, ihe identity function is
always an isomorphism, acting as its own inverse.

```
idIso : (A : Type ℓ) → Iso A A
-- Exercise:
idIso A = {!   !}
```

And, the data of an isomorphism is completely symmetric between `A`
and `B`, so given any isomorphism, we can flip it around.

```
invIso : Iso A B → Iso B A
-- Exercise:
invIso f = {!   !}
```

Isomorphisms compose like functions do, but we will prove this a
little later (`compIso`{.Agda} in Lecture 2-4).

An isomorphism between two types says, in effect, that elements of
those types are different representations of essentially the same
data. For example, suppose we define the following type:

```
data RedOrBlue : Type where
  red : RedOrBlue
  blue : RedOrBlue
```

This is a type with two elements, `red`{.Agda} and `blue`{.Agda}. We
already have a type with two elements: `Bool`{.Agda} with the elements
`true`{.Agda} and `false`{.Agda}. Our code really shouldn't depend
essentially on what we named the two elements of `Bool`{.Agda}; we can
demonstrate this explicitly by showing that `Bool`{.Agda} is
isomorphic to `RedOrBlue`{.Agda}.

```
IsoBoolRedOrBlue : Iso Bool RedOrBlue
IsoBoolRedOrBlue = iso to fro s r
  where
    to : Bool → RedOrBlue
    to true = red
    to false = blue

    fro : RedOrBlue → Bool
    fro red = true
    fro blue = false

    s : section to fro
    s red = refl
    s blue = refl

    r : retract to fro
    r true = refl
    r false = refl
```

Now, this isn't the only way we could have shown that `Bool`{.Agda}
was isomorphic to `RedOrBlue`{.Agda}; we could also have sent
`true`{.Agda} to `blue`{.Agda} and `false`{.Agda} to `red`{.Agda}.
Define this other isomorphism below:

```
OtherIsoBoolRedOrBlue : Iso Bool RedOrBlue
OtherIsoBoolRedOrBlue = iso to fro s r
{-
  where
    to : Bool → RedOrBlue
    to x = {!   !}

    fro : RedOrBlue → Bool
    fro x = {!   !}

    s : section to fro
    s x = {!   !}

    r : retract to fro
    r x = {!   !}
-}
  where
    to : Bool → RedOrBlue
    to true = blue
    to false = red

    fro : RedOrBlue → Bool
    fro red = false
    fro blue = true

    s : section to fro
    s red = refl
    s blue = refl

    r : retract to fro
    r true = refl
    r false = refl
```

Not every function `Bool → RedOrBlue` is an isomorphism. If we sent
both `true`{.Agda} and `false`{.Agda} to `red`{.Agda}, for example,
then there is no way we could find an inverse. Any inverse would have
to send `red`{.Agda} to `true`{.Agda} and to `false`{.Agda}, but these
aren't equal!

In Lecture 1-2, we had a few "bijections" between types. At least, we
had maps going each way. Now we can show that these really are
isomorphisms. Here's an especially easy one, where the paths in the
`section`{.Agda} and `retract`{.Agda} can be also `refl`{.Agda} for
any argument.

```
×-assoc-Iso : Iso (A × (B × C)) ((A × B) × C)
×-assoc-Iso = iso to fro sec ret
  where
    -- We defined these maps way back in Lecture 1-1, but only for
    -- types in the lowest universe, so we have to redefine them here.
    to : (A × (B × C)) → ((A × B) × C)
    to (a , (b , c)) = (a , b) , c

    fro : ((A × B) × C) → (A × (B × C))
    fro ((a , b) , c) = (a , (b , c))

    sec : section to fro
--  Exercise:
--  s x = ?
    sec x = refl

    ret : retract to fro
--  Exercise:
--  r x = ?
    ret x = refl
```

This worked because the composition of the two functions is
*definitionally* the identity on any argument. In the previous Lecture
we gave descriptions of `PathP`{.Agda}s in various types. The
functions involved are also definitional inverses and so assemble into
`Iso`{.Agda}s in a similar way.

```
funExt-Iso : {f g : A → B} → Iso ((x : A) → f x ≡ g x) (f ≡ g)
funExt-Iso = iso funExt funExt⁻ (λ _ → refl) (λ _ → refl)

-- Paths in a product are the same as the product of paths
×Path-Path×-Iso : {x y : A × B} →
  Iso (Path A (fst x) (fst y) × Path B (snd x) (snd y))
      (Path (A × B) x y)
×Path-Path×-Iso = iso ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)

-- The same is true when everything is maximally dependent
ΣPath-PathΣ-Iso : {A : I → Type ℓ}
                  {B : (i : I) → (a : A i) → Type ℓ'}
                  {x : Σ[ a ∈ A i0 ] B i0 a}
                  {y : Σ[ a ∈ A i1 ] B i1 a} →
  Iso (Σ[ p ∈ PathP A (fst x) (fst y) ]
             (PathP (λ i → B i (p i)) (snd x) (snd y)))
      (PathP (λ i → Σ[ a ∈ A i ] B i a) x y)
ΣPath-PathΣ-Iso = iso ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)
```

We will not always be so lucky. In the following `Iso`{.Agda}, we
cannot simply supply `refl`{.Agda} for an arbitrary argument `x`
because Agda does not know which cases of `Bool→⊤⊎⊤`{.Agda} and
`⊤⊎⊤→Bool`{.Agda} should be used with that `x`. But: if we split into
cases for `x`, then the functions compute and we can again supply
`refl`{.Agda} in each case.

```
Bool-⊤⊎⊤-Iso : Iso Bool (⊤ ⊎ ⊤)
Bool-⊤⊎⊤-Iso = iso Bool→⊤⊎⊤ ⊤⊎⊤→Bool sec ret
  where
    sec : section Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
--  Hint: Check your definitions for Bool→⊤⊎⊤ and ⊤⊎⊤→Bool
--  in 1-2 if this throws an error.
--  sec x = ?
    sec (inl tt) = refl
    sec (inr tt) = refl

    ret : retract Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
--  ret x = ?
    ret true = refl
    ret false = refl
```

The next is similar.

```
ℤ-ℕ⊎ℕ-Iso : Iso ℤ (ℕ ⊎ ℕ)
ℤ-ℕ⊎ℕ-Iso = iso ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ sec ret
  where
    sec : section ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
--  sec x = ?
    sec (inl x) = refl
    sec (inr x) = refl

    ret : retract ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
--  ret x = ?
    ret (pos n) = refl
    ret (negsuc n) = refl
```

```
∅⊎-Iso : ∀ {ℓ} (A : Type ℓ) → Iso (∅ ⊎ A) A
∅⊎-Iso A = iso (∅⊎-to A) (∅⊎-fro A) sec ret
  where
    sec : section (∅⊎-to A) (∅⊎-fro A)
--  Exercise:
--  sec x = ?
    sec x = refl

    ret : retract (∅⊎-to A) (∅⊎-fro A)
--  Exercise:
--  ret x = ?
    ret (inr x) = refl

∅×-Iso : Iso (∅ × A) ∅
∅×-Iso {A = A} = iso (∅×-to A) (∅×-fro A) sec ret
  where
    sec : section (∅×-to A) (∅×-fro A)
--  Exercise:
--  sec x = ?
    sec ()

    ret : retract (∅×-to A) (∅×-fro A)
--  Exercise:
--  ret x = ?
    ret (() , a)
```

Not all isomorphisms have to go between different types. A type
can be isomorphic to itself in a non-trivial way.

```
not-Iso : Iso Bool Bool
not-Iso = iso not not sec ret
  where
    sec : section not not
--  Exercise:
--  sec x = ?
    sec true = refl
    sec false = refl

    ret : retract not not
--  Exercise:
--  ret x = ?
    ret true = refl
    ret false = refl

sucℤ-Iso : Iso ℤ ℤ
sucℤ-Iso = iso sucℤ predℤ sec ret
  where
    sec : section sucℤ predℤ
--  Exercise:
--  sec x = ?
    sec (pos zero) = refl
    sec (pos (suc n)) = refl
    sec (negsuc zero) = refl
    sec (negsuc (suc n)) = refl

    ret : retract sucℤ predℤ
--  Exercise:
--  ret x = ?
    ret (pos zero) = refl
    ret (pos (suc n)) = refl
    ret (negsuc zero) = refl
    ret (negsuc (suc n)) = refl
```

And not all isomorphisms will be simply case-split-then-`refl`{.Agda}. The
section and retract here need to be constructed recursively:

```
ℕ-List⊤-Iso : Iso ℕ (List ⊤)
ℕ-List⊤-Iso = iso ℕ→List⊤ length sec ret
  where
    sec : section ℕ→List⊤ length
--  Exercise:
--  sec x = ?
    sec [] = refl
    sec (tt :: L) = cong (tt ::_) (sec L)

    ret : retract ℕ→List⊤ length
--  Exercise:
--  ret x = ?
    ret zero = refl
    ret (suc x) = cong suc (ret x)
```

## Path Algebra

In the last lecture, we saw what could be done with paths using only
the fact that they are functions `I → A`. In this lecture, we'll
introduce some more axioms for the interval which will let us prove
more.

So far, we have only used that the interval has endpoints `i0 i1 :
I`. But the actual unit interval $[0, 1]$ of topology has a lot more
structure than just its endpoints. We'll axiomatize some of this
structure so we can use it to define operations on paths.

First, there is the function $r(x) = 1 - x : [0, 1] → [0, 1]$. If
$p : [0, 1] → S$ is a path in the space $S$ from $p(0)$ to $p(1)$,
then $p ∘ r : [0, 1] → S$ is a path in $S$ from $p(1)$ to $p(0)$ ---
since $(p ∘ r)(0) = p(1)$ and $(p ∘ r)(1) = p(0)$ by definition.

Cubical Agda has a similar primitive operation on cubical variables:
`~ : I → I` is a built-in function that reverses the interval. By
definition we have that `~ i0 = i1` and `~ i1 = i0`. Uncomment the
goal and normalise the expression by moving the cursor into the goal
and pressing `C-c C-n`. (`C-n` for "normalise").

```
{-
_ : I
_ = {! ~ i0!}
-}
```

We can use this operation to give the symmetry principle for paths.

```
sym : x ≡ y → y ≡ x
sym p i = p (~ i)
```

We upgrade this to also apply to paths over a path. We have to flip
the path of types too, so that the end-points lie in the correct
types.

```
symP : {A : I → Type ℓ} → {x : A i1} → {y : A i0}
  → (p : PathP (λ i → A (~ i)) x y) → PathP A y x
symP p j = p (~ j)
```

Now, there's a fairly evident question we can ask: what happens if we
flip a path twice? Agda takes it as an axiom that `~ (~ i) = i`, so
the answer is that we get the same path again by definition.

```
symP-inv : (p : PathP _ x y) → symP (symP p) ≡ p
symP-inv p = refl
```

This is an example of a path between paths. In this case, the
path-between-paths is trivial. But the paths-between-paths we run into
won't be trivial for long.

These two definitions can be put together as an isomorphism.

```
symP-Iso : {A : I → Type ℓ} → {x : A i1} → {y : A i0}
  → Iso (PathP (λ i → A (~ i)) x y) (PathP A y x)
symP-Iso = iso symP symP symP-inv symP-inv
```

## The Interval De Morgan Algebra

To define interesting squares, we'll need to axiomatize a bit more
structure from the unit interval $[0,1]$. The functions $\max, \min :
[0, 1] × [0, 1] → [0, 1]$ are quite useful for constructing
homotopies: if $p : [0, 1] → S$ is a path in $S$, then $p ∘ \max$ is a
homotopy between $p$ and the constant path at $p(1), because $p(\max(0,
i)) = p(i)$ and $p(\max(1, i)) = p(1)$. For similar reasons, $p ∘ \min$
is a homotopy between the constant path at $p(0)$ and $p$.

We will axiomatize these with interval operations `∨`{.Agda} and
`∧`{.Agda} (for $\max$ and $\min$ respectively). Agda automatically
computes the values of `∨`{.Agda} and `∧`{.Agda} when either side is
one of the endpoints `i0`{.Agda} or `i1`{.Agda}.

Uncomment this block and try normalising the following expressions.

```
{-
_ : I
_ = {! i0 ∨ i0 !}

_ : I
_ = {! i0 ∨ i1 !}

_ : I
_ = {! i0 ∧ i0 !}

_ : I
_ = {! i0 ∧ i1 !}
-}
```

There are a few additional equalities which hold for $\max$ and $\min$
that Agda builds in for `∧`{.Agda} and `∨`{.Agda}, so that they hold
definitionally:

* Top and Bottom:
  $$
  \begin{align*}
  i0 ∧ j &= i0   &  i0 ∨ j &= j \\
  i1 ∧ j &= j    &  i1 ∨ j &= i1
  \end{align*}
  $$
* Idempotence:
  $$
  \begin{align*}
  i ∧ i &= i     & i ∨ i &= i
  \end{align*}
  $$
* Commutativity:
  $$
  \begin{align*}
  i ∧ j &= j ∧ i & i ∧ j &= j ∧ i
  \end{align*}
  $$
* Associativity:
  $$
  \begin{align*}
  (i ∧ j) ∧ k &= i ∧ (j ∧ k) & (i ∨ j) ∨ k &= i ∨ (j ∨ k)
  \end{align*}
  $$
* Distributivity:
  $$
  \begin{align*}
  i ∧ (j ∨ k) &= (i ∧ j) ∨ (i ∧ k) & i ∨ (j ∧ k) &= (i ∨ j) ∧ (i ∨ k)
  \end{align*}
  $$
* Symmetry:
  $$
  \begin{align*}
  ∼ (∼ i) &= i
  \end{align*}
  $$
* The De Morgan Laws:
  $$
  \begin{align*}
  ∼ (i ∧ j) &= (∼ i) ∨ (∼ j) & ∼ (i ∨ j) = (∼ i) ∧ (∼ j)
  \end{align*}
  $$

(You don't have to memorise these.)

Pen-and-Paper Exercise: Convince yourself that all of these axioms are
true for the actual unit interval $[0, 1]$ where `∨ = max`, `∧ = min`,
and `~ i = 1 - i`.

These laws make `I`{.Agda} into an algebraic structure known as a *De
Morgan algebra*. De Morgan was a British mathematician and
contemporary of Boole (from whom we get *Boolean algebra* and the name
of the type `Bool`{.Agda}). De Morgan was the first to state the laws
which have his name, coined the term "mathematical induction" and was
the first to formally state the induction principle for natural
numbers. De Morgan, like Boole, was concerned with turning logic into
algebra.

We can use the De Morgan algebra structure `∨`{.Agda} and `∧`{.Agda}
to build some squares that were unavailable to us before:

             p
         x - - - > y
         ^         ^
    refl |         | p               ^
         |         |               j |
         x — — — > x                 ∙ — >
            refl                       i
```
connection∧ : (p : x ≡ y) → Square refl p refl p
connection∧ p i j = p (i ∧ j)
```

          refl
       y - - - > y
       ^         ^
     p |         | refl            ^
       |         |               j |
       x — — — > y                 ∙ — >
           p                         i
```
connection∨ : (p : x ≡ y) → Square p refl p refl
connection∨ p i j = p (i ∨ j)
```

Below we have drawn some more squares for you to fill in.

           p⁻¹
       y - - - > x
       ^         ^
     p |         | refl            ^
       |         |               j |
       x — — — > x                 ∙ — >
          refl                       i

```
connectionEx1 : (p : x ≡ y) → Square p refl refl (sym p)
-- Exercise:
connectionEx1 p i j = ?

```
            p
        x - - - > y
        ^         ^
    p⁻¹ |         | refl            ^
        |         |               j |
        y — — — > y                 ∙ — >
           refl                       i
```
connectionEx2 : (p : x ≡ y) → Square (sym p) refl refl p
-- Exercise:
connectionEx2 p i j = ?
```

Here's a nice application. The definition of `ℤ`{.Agda} we gave back
in Lecture 1-2 is a little janky --- we treat the negatives and the
positives asymmetrically, handing `zero`{.Agda} to the `pos`{.Agda}
side and shifting the `negsuc`{.Agda} side down by one. Now that we have
paths, we can define a version of the integers that treats them the
same --- but we have to add in a path between "positive 0" and
"negative 0":

```
data ℤ' : Type where
  pos' : ℕ → ℤ'
  neg' : ℕ → ℤ'
  poszero≡negzero : pos' zero ≡ neg' zero
```

Using a connection, we can prove that these new integers are in fact
isomorphic to original ones.

```
ℤ'→ℤ : ℤ' → ℤ
-- Exercise:
ℤ'→ℤ z = ?

ℤ→ℤ' : ℤ → ℤ'
-- Exercise:
ℤ→ℤ' z = ?

ℤIsoℤ' : Iso ℤ ℤ'
ℤIsoℤ' = iso ℤ→ℤ' ℤ'→ℤ s r
  where
    s : section ℤ→ℤ' ℤ'→ℤ
--  Exercise: Use a conneciton in the case for `poszero≡negzero`!
--  s z = ?
    s (pos' x) = refl
    s (neg' zero) = poszero≡negzero
    s (neg' (suc zero)) = refl
    s (neg' (suc (suc x))) = refl
    s (poszero≡negzero i) = λ j → poszero≡negzero (i ∧ j)

    r : retract ℤ→ℤ' ℤ'→ℤ
--  Exercise:
--  r z = ?
    r (pos n) = refl
    r (negsuc zero) = refl
    r (negsuc (suc n)) = refl
```

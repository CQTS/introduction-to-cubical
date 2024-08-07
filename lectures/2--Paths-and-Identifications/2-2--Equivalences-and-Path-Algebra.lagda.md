```
module 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra where
```

# Lecture 2-2: Equivalences and Path Algebra

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths

private
  variable
    ℓ ℓ' : Level
    A A' B C : Type ℓ
    x y : A
```
-->

A function `f : A → B` lets us transform data of type `A` into data of
type `B`. If we have some other construction that needs an element of
`B`, we can use `f` to feed in an element of `A` instead. In this way,
we can see a function `f : A → B` as giving us a way to represent
elements of `B` by elements of `A`.

For example, in many languages, it is common to represent Booleans by
numbers by considering the number `0` to be ``false``, and any
other number to be ``true``. In Agda, we could write this
representation as a function `ℕ → Bool`.

```
isPositive : ℕ → Bool
isPositive zero = false
isPositive (suc n) = true
```

If this is going to give us a way to represent Booleans as natural
numbers, there needs to be at least some way to represent each
individual Boolean. This is certainly true, for example, we can use
`0` for ``false`` and `1` for ``true``.

```
Bool→ℕ : Bool → ℕ
Bool→ℕ true = suc zero
Bool→ℕ false = zero
```

The number `Bool→ℕ b` faithfully represents the Boolean `b` via the
function ``isPositive``, because `isPositive (Bool→ℕ b) ≡ b`.

```
isPositive-represents-Bool : (b : Bool) → isPositive (Bool→ℕ b) ≡ b
```

How do we prove this? Unfortunately we can't simply use the
reflexivity path for each `b`, like so

```
-- isPositive-represents-Bool b = refl
```

because Agda does not automatically check both cases for us. But all
we have to do is case-split on `b` ourselves: once Agda knows that `b
= true`, then it can use the definitions of the functions to compute
that `isPositive (Bool→ℕ true) = isPositive (suc zero) = true`. So for
the ``true`` case, we can use reflexivity, and the same is true
for the ``false`` case.

```
isPositive-represents-Bool true = refl
isPositive-represents-Bool false = refl
```

Generally speaking, if `f : A → B` is to give us a way to represent
elements of `B` by elements of `A`, we should expect to have at least
some way to represent any element of `B` by some element of `A`. And
we have a function `g : B → A` the other way so that for all `b : B`,
we have `f (g b) ≡ b`, we say that `g` is a *section* of `f`.

```
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
  isSection : (f : A → B) → (g : B → A) → Type ℓ'
  isSection f g = (b : B) → f (g b) ≡ b

  sectionOf : (f : A → B) → Type (ℓ-max ℓ ℓ')
  sectionOf f = Σ[ g ∈ (B → A)] isSection f g
```

So here, ``Bool→ℕ`` is a section of ``isPositive``; this is
exactly what ``isPositive-represents-Bool`` above is saying.

```
isSection-isPositive-Bool→ℕ : isSection isPositive Bool→ℕ
isSection-isPositive-Bool→ℕ = isPositive-represents-Bool
```

While every Boolean `b` can be represented by the natural number
`Bool→ℕ b`, it is not the case that every natural number `a` can be
represented by a Boolean with respect to the function ``Bool→ℕ``.
A natural number gives more data than a Boolean.

But what about the following type ``RedOrBlue``?

```
data RedOrBlue : Type where
  red : RedOrBlue
  blue : RedOrBlue
```

It is quite apparent that ``RedOrBlue`` has the same data as
``Bool``: each has two elements and nothing more. We can
represent a Boolean by an element of ``RedOrBlue`` as follows:

```
RedOrBlue→Bool : RedOrBlue → Bool
RedOrBlue→Bool red = true
RedOrBlue→Bool blue = false
```

And we can choose a representative for every Boolean by giving a
section ``Bool→RedOrBlue`` of ``RedOrBlue→Bool``.

```
Bool→RedOrBlue : Bool → RedOrBlue
Bool→RedOrBlue true = red
Bool→RedOrBlue false = blue

isSection-RedOrBlue-Bool : isSection RedOrBlue→Bool Bool→RedOrBlue
isSection-RedOrBlue-Bool true = refl
isSection-RedOrBlue-Bool false = refl
```

But this time, we can choose a representative for every
``RedOrBlue`` as a Boolean too!

```
isSection-Bool-RedOrBlue : isSection Bool→RedOrBlue RedOrBlue→Bool
isSection-Bool-RedOrBlue red = refl
isSection-Bool-RedOrBlue blue = refl
```

In this reversed situation, we say that `f : A → B` is a *retract* when
it *has* a section.

```
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
  isRetract : (f : A → B) → (g : B → A) → Type ℓ
  isRetract f g = isSection g f

  retractOf : (f : A → B) → Type (ℓ-max ℓ ℓ')
  retractOf f = Σ[ g ∈ (B → A)] isRetract f g
```

When the function `f : A → B` has a section `g : B → A`, and has a
retract `h : B → A`, as is the case for ``RedOrBlue→Bool`` here,
we say that `f` is an *equivalence*. In this situation, we can use `f`
to represent elements of `B` by elements of `A` (with chosen
representatives by `g`), and we can use `h` to represent elements of
`A` by elements of `B` (with chosen representatives by `f`). In other
words, we can represent elements of `B` by elements of `A` and
vice-versa --- the types describe equivalent data.

```
isEquiv : {A : Type ℓ} → {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isEquiv f = sectionOf f × retractOf f

Equiv : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Equiv A B = Σ[ f ∈ (A → B) ] isEquiv f
```

We will use the syntax `A ≃ B` for the type of equivalences between
`A` and `B`. (The symbol ``≃`` is input as `\simeq`.)

```
_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
_≃_ = Equiv

infix 4 _≃_
```

This is the notion of sameness for types that we will be working with
in these lecture notes.

To make these less annoying to work with, we'll write some helpers for
constructing and destructing these `Equiv`s.

```
equivFun : A ≃ B → (A → B)
equivFun e = fst e

equivSec : (e : A ≃ B) → B → A
equivSec e = fst (fst (snd e))

equivIsSec : (e : A ≃ B) → isSection (equivFun e) (equivSec e)
equivIsSec e = snd (fst (snd e))

equivRet : (e : A ≃ B) → B → A
equivRet e = fst (snd (snd e))

equivIsRet : (e : A ≃ B) → isRetract (equivFun e) (equivRet e)
equivIsRet e = snd (snd (snd e))
```

It is very common that the section of `f` and retract of `f` are the
same map, so we will us a helper to duplicate the map in this case.

```
equiv : (fun : A → B)
      → (inv : B → A)
      → (rightInv : isSection fun inv)
      → (leftInv  : isRetract fun inv)
      → A ≃ B
equiv fun inv rightInv leftInv = fun , (inv , rightInv) , (inv , leftInv)
```

::: Aside:
It might seem strange that our notion of equivalence involves *two*
maps backwards rather than just one.

When a map has a single inverse map that is a both a section and a
retract, the map is called an *isomorphism*, a faux-Greek word meaning
"same shape". While every isomorphism gives rise to an equivalence
(via the function ``equiv`` just above) and every equivalence
gives rise to an isomorphism, the type of equivalences and the type of
isomorphisms between two types are not in general the same! mvrnote:
link forwards if we prove this

It will turn out that "equivalence" as we've defined it here is the
better notion, because the type `isEquiv f` is a *proposition* about
the function `f`, whereas being an "isomorphism" sneaks in extra data.
We will happily forget about the term "isomorphism" from this point on
and stick with equivalence.
:::

At the very least, we can show that the identity function on any type
is an equivalence.

```
idEquiv : (A : Type ℓ) → A ≃ A
-- Exercise:
idEquiv A = {!!}
```

An equivalence between two types says, in effect, that elements of
those types are different representations of the same data. Putting
together the maps we defined above, ``Bool`` is equivalent to
``RedOrBlue``

```
Bool≃RedOrBlue : Bool ≃ RedOrBlue
Bool≃RedOrBlue = equiv Bool→RedOrBlue RedOrBlue→Bool isSection-Bool-RedOrBlue isSection-RedOrBlue-Bool 
```

Now, this isn't the only way we could have shown that ``Bool``
was equivalent to ``RedOrBlue``; we could also have sent
``true`` to ``blue`` and ``false`` to ``red``.
Define this other equivalence below:

```
OtherBool≃RedOrBlue : Bool ≃ RedOrBlue
OtherBool≃RedOrBlue = equiv to fro to-fro fro-to
  -- Exercise:
  where
    to : Bool → RedOrBlue
    to x = {!!}

    fro : RedOrBlue → Bool
    fro x = {!!}

    to-fro : isSection to fro
    to-fro x = {!!}

    fro-to : isRetract to fro
    fro-to x = {!!}
```

Not every function `Bool → RedOrBlue` is an equivalence. If we sent
both ``true`` and ``false`` to ``red``, for example,
then there is no way we could find an inverse. Any section would have
to send ``red`` to ``true`` and also to ``false``, but
these aren't equal!

In Lecture 1-2, we had a few "bijections" between types. At the time,
all we could do is produce maps going each way. Now we can show that
these really are equivalences. Here's an especially easy one, where
the paths in the ``to-fro`` and ``fro-to`` functions can be
``refl`` for any argument.

```
×-assoc-≃ : (A × (B × C)) ≃ ((A × B) × C)
×-assoc-≃ = equiv to fro to-fro fro-to
  where
    -- We defined these maps way back in Lecture 1-1, but only for
    -- types in the lowest universe, so we have to redefine them here.
    to : (A × (B × C)) → ((A × B) × C)
    to (a , (b , c)) = (a , b) , c

    fro : ((A × B) × C) → (A × (B × C))
    fro ((a , b) , c) = (a , (b , c))

    to-fro : isSection to fro
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract to fro
--  Exercise:
    fro-to x = {!!}
```

This worked because the composition of the two functions computes to
the identity on any argument.

In the previous Lecture we gave descriptions of ``PathP``s in
various types. The functions involved are also definitional inverses
and so assemble into equivalences in a similar way.

```
funExt-≃ : {f g : A → B} → ((x : A) → f x ≡ g x) ≃ (f ≡ g)
funExt-≃ = equiv funExt funExt⁻ (λ _ → refl) (λ _ → refl)

-- mvrnote: is orienting these the other direction more natural?
×Path≃Path× : {x y : A × B} →
  (fst x ≡ fst y) × (snd x ≡ snd y)
  ≃ (x ≡ y)
×Path≃Path× = equiv ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)

-- The same is true when everything is maximally dependent
ΣPath≃PathΣ : {A : I → Type ℓ}
                  {B : (i : I) → (a : A i) → Type ℓ'}
                  {x : Σ[ a ∈ A i0 ] B i0 a}
                  {y : Σ[ a ∈ A i1 ] B i1 a} →
  (Σ[ p ∈ PathP A (fst x) (fst y) ]
    (PathP (λ i → B i (p i)) (snd x) (snd y)))
  ≃ (PathP (λ i → Σ[ a ∈ A i ] B i a) x y)
ΣPath≃PathΣ = equiv ΣPathP→PathPΣ PathPΣ→ΣPathP (λ _ → refl) (λ _ → refl)
```

We will not always be so lucky, and have definitional inverses to our
functions. For the following you will have to split into cases, like
we did for the function ``isPositive-represents-Bool``.

If the next equivalence doesn't work doesn't work, go back and check
that the definitions of ``Bool→⊤⊎⊤`` and ``⊤⊎⊤→Bool`` you
gave are actually inverses!

```
Bool≃⊤⊎⊤ : Bool ≃ (⊤ ⊎ ⊤)
Bool≃⊤⊎⊤ = equiv Bool→⊤⊎⊤ ⊤⊎⊤→Bool to-fro fro-to
  where
    to-fro : isSection Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract Bool→⊤⊎⊤ ⊤⊎⊤→Bool
--  Exercise:
    fro-to x = {!!}
```

The next few are similar.

```
ℤ≃ℕ⊎ℕ : ℤ ≃ (ℕ ⊎ ℕ)
ℤ≃ℕ⊎ℕ = equiv ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ to-fro fro-to
  where
    to-fro : isSection ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
--  Exercise:
    fro-to x = {!!}

⊎-ump-≃ : (A ⊎ B → C) ≃ (A → C) × (B → C)
⊎-ump-≃ = equiv ⊎-ump ⊎-fold to-fro fro-to
  where
    to-fro : isSection ⊎-ump ⊎-fold
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract ⊎-ump ⊎-fold
--  Hint: You will need to case-split on the element of `A ⊎ B`, so
--  you can't use `refl` here directly.
--  Exercise:
    fro-to x = {!!}

∅×≃∅ : (A : Type ℓ) → (∅ × A) ≃ ∅
∅×≃∅ A = equiv (∅×-to A) (∅×-fro A) to-fro fro-to
  where
    to-fro : isSection (∅×-to A) (∅×-fro A)
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract (∅×-to A) (∅×-fro A)
--  Exercise:
    fro-to x = {!!}

Torus≃S¹×S¹ : Torus ≃ S¹ × S¹
Torus≃S¹×S¹ = equiv Torus→S¹×S¹ S¹×S¹→Torus to-fro fro-to
  where
    to-fro : isSection Torus→S¹×S¹ S¹×S¹→Torus
--  Exercise:
    to-fro c = {!!}

    fro-to : isRetract Torus→S¹×S¹ S¹×S¹→Torus
--  Exercise:
    fro-to t = {!!}
```

Equivalences do not necessarily go between different types. A type can
be equivalent to itself in a non-trivial way. This will be crucial
later!

```
not-≃ : Bool ≃ Bool
not-≃ = equiv not not to-fro fro-to
  where
    to-fro : isSection not not
--  Exercise:
    to-fro x = {!!}

    fro-to : isSection not not
--  Exercise:
    fro-to x = {!!}

sucℤ-≃ : ℤ ≃ ℤ
-- Exercise:
sucℤ-≃ = equiv sucℤ {!!} {!!} {!!}
```

And not all equivalences will be simply proven by
case-split-then-``refl``. The section and retract here need to be
constructed recursively:

```
ℕ≃List⊤ : ℕ ≃ (List ⊤)
ℕ≃List⊤ = equiv ℕ→List⊤ length to-fro fro-to
  where
    to-fro : isSection ℕ→List⊤ length
--  Exercise:
    to-fro x = {!!}

    fro-to : isRetract ℕ→List⊤ length
--  Exercise:
    fro-to x = {!!}
```


## Path Algebra

In the last lecture, we saw what could be done with paths using only
the fact that they are functions `I → A`. In this lecture, we'll
introduce some more axioms for the interval which will let us prove
more.

So far, we have only used that the interval has endpoints `i0 : I and
`i1 : I`. But the actual unit interval $[0, 1]$ has a lot more
structure than just its endpoints. We'll axiomatize some of this
structure so we can use it to define operations on paths.

First, there is the function $r(x) = 1 - x : [0, 1] → [0, 1]$ that
reverses the interval. If $p : [0, 1] → S$ is a path in the space $S$
from $p(0)$ to $p(1)$, then $p ∘ r : [0, 1] → S$ is a path in $S$ from
$p(1)$ to $p(0)$ --- since $(p ∘ r)(0) = p(1)$ and $(p ∘ r)(1) = p(0)$
by definition.

Cubical Agda has a primitive operation on elements of the interval:
`~_ : I → I`, which we think of as reversal. By definition, it holds
that `~ i0 = i1` and `~ i1 = i0`. Uncomment the goal and normalise the
expression by moving the cursor into the goal and pressing `C-c C-n`.

```
{-
_ : I
_ = {! ~ i0!}
-}
```

We can use this operation to give reverse a path.

```
sym : x ≡ y → y ≡ x
sym p i = p (~ i)
```

And we can upgrade this principle to also apply to path-overs. We have
to flip the path of types `A` too, so that the endpoints lie in the
correct types.

```
symP : {A : I → Type ℓ} → {x : A i1} → {y : A i0}
  → PathP (λ i → A (~ i)) x y
  → PathP A y x
symP p j = p (~ j)
```

Now, there's a fairly evident question we can ask: what happens if we
flip a path twice? Agda takes it as an axiom that `~ (~ i) = i`, so
the answer is that we get the same path again by definition.

```
symP-inv : (p : PathP _ x y) → symP (symP p) ≡ p
symP-inv p = refl
```

And so ``symP`` is an equivalence.

```
symP-≃ : {A : I → Type ℓ} → {x : A i1} → {y : A i0}
  → PathP (λ i → A (~ i)) x y ≃ PathP A y x
symP-≃ = equiv symP symP symP-inv symP-inv
```


## The Interval De Morgan Algebra

To define interesting ``Squares``s, we'll need to axiomatize more
structure from the unit interval $[0, 1]$. Mathematically, the
functions $\max, \min : [0, 1] × [0, 1] → [0, 1]$ are quite useful for
constructing homotopies: if $p : [0, 1] → S$ is a path in $S$, then $p
∘ \max$ is a homotopy between $p$ and the constant path at $p(1),
because $p(\max(0, i)) = p(i)$ and $p(\max(1, i)) = p(1)$. For similar
reasons, $p ∘ \min$ is a homotopy between the constant path at $p(0)$
and $p$.

We will axiomatize these with two more in-built interval operations
``∨`` and ``∧`` (for $\max$ and $\min$ respectively). Agda
automatically computes the values of ``∨`` and ``∧`` when
either side is one of the endpoints ``i0`` or ``i1``.

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
that Agda makes true for ``∧`` and ``∨``.

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

::: Aside:
Pen-and-Paper Exercise: Convince yourself that all of these axioms are

These laws make the interval ``I`` into an algebraic structure
known as a *De Morgan algebra*. We saw a version of the "De Morgan
laws" earler, for types, when we proved ``DeMorgan-law-1``,
``DeMorgan-law-2`` and ``DeMorgan-law-3``. Unlike for types,
the algebra on the interval also satisfies the missing fourth law
which we mentioned there.

::: Aside:
De Morgan was a British mathematician and contemporary of Boole (from
whom we get *Boolean algebra* and the name of the type ``Bool``).
He was the first to state the laws which have his name, coined the
term "mathematical induction" and was the first to formally state the
induction principle for natural numbers. De Morgan, like Boole, was
concerned with turning logic into algebra.
:::

We can use the De Morgan algebra structure ``∨`` and ``∧``
to build some squares that were unavailable to us before. The
following two are called *connections*.

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

Below we have drawn some more squares for you to fill in as practice.

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
connectionEx1 p i j = {!!}

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
connectionEx2 p i j = {!!}
```

As an immediate application of connections, we can show that the
``ℤ→ℤˢ`` and ``ℤˢ→ℤ`` maps we defined earlier are an
equivalence. You will need to use a connection in the case for
``posˢzero≡negˢzero``.

```
ℤ≃ℤˢ : ℤ ≃ ℤˢ
ℤ≃ℤˢ = equiv ℤ→ℤˢ ℤˢ→ℤ to-fro fro-to
  where
    to-fro : isSection ℤ→ℤˢ ℤˢ→ℤ
--  Exercise:
    to-fro z = {!!}

    fro-to : isRetract ℤ→ℤˢ ℤˢ→ℤ
--  Exercise:
    fro-to z = {!!}
```

::: Aside:
When you reach the `to-fro (posˢzero≡negˢzero i)` case, the goal should
look like:

    Goal: posˢ zero ≡ posˢzero≡negˢzero i
    ———— Boundary (wanted) —————————————————————————————————————
    i = i0 ⊢ λ i₁ → posˢ zero
    i = i1 ⊢ posˢzero≡negˢzero
    ————————————————————————————————————————————————————————————
    i : I

This is asking us to produce a path between paths. If you accept an
additional argument `j` (by adding it manually or pressing `C-c C-c`),
the goal becomes

    Goal: ℤˢ
    ———— Boundary (wanted) —————————————————————————————————————
    j = i0 ⊢ posˢ zero
    j = i1 ⊢ posˢzero≡negˢzero i
    i = i0 ⊢ posˢ zero
    i = i1 ⊢ posˢzero≡negˢzero j
    ————————————————————————————————————————————————————————————
    j : I
    i : I

which tells us exactly what square we need to construct.
:::


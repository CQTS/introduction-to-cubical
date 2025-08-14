<!--
```
module 1--Type-Theory.1-3--Universes-and-More-Inductive-Types where

open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
```
-->


# Lecture 1-3: Universes and More Inductive Types

There is a lingering question that we've left unanswered since Lecture
1-1. What is the type of the universe ``Type`` itself? One option open
to the designer of a type theory is to declare that ``Type`` is an
element of itself; this is the [approach] taken by the [Haskell]
programming language. This works fine for practical programming but
leads to logical contradictions thanks to some "Russell-style"
paradoxes. (Do some research on [Girard's paradox] if you are
curious!)

[Girard's paradox]: https://en.wikipedia.org/wiki/System_U#Girard's_paradox
[approach]: https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/poly_kinds.html#overview-of-type-in-type
[Haskell]: https://www.haskell.org/


## Universe Levels

To avoid this, Agda stratifies all types into a hierarchy using the
mechanism of *universe levels*. Roughly speaking, the level of a type
universe specifies the "bigness" of the types it can contain.

On its own, ``Type`` is secretly ``Type₀``, the universe of all types
of "level zero". But ``Type₀`` itself is too big to be of level zero,
and lives at level one: `Type₀ : Type₁`. Similarly, `Type₁` is too big
to be of level one, so `Type₁ : Type₂`, and so on.

```
_ = test-type Type₀ Type₁
_ = test-type Type₁ Type₂
_ = test-type Type₂ Type₃
-- Fails!
-- _ = test-type Type₀ Type₀
```

In general, the universe `Type ℓ` lives in universe `Type (ℓ-suc ℓ)`
for any level `ℓ : Level`, where ``ℓ-suc`` is a built-in function that
increments a universe level by one.

When we prove facts about functions, we might want to apply them in
situations where the universe ``Type`` is involved, or maybe things
lying in higher universe levels still. This is accomplished by having
functions accept types of *any* universe level, a trick known
technically as "universe polymorphism". As an example, for the very
final time, here is the universe-polymorphic definition of the
identity function on any type, where that type may live in any
universe.

```
idfun : {ℓ : Level} → {A : Type ℓ} → A → A
idfun x = x
```

``Level`` here is the magic, built-in collection of universe levels.
``Level`` is not actually a type, and it can't be sensibly mixed
together with ordinary types without Agda complaining. For each level
`ℓ : Level`, there is a corresponding universe of that level called
`Type ℓ`.

Similarly to ``idfun``, we can upgrade some of the functions we have
defined into their final, most general versions. (We do it for these
particular functions, because we end up using them later.) The actual
definitions haven't changed, all that has changed is that every
occurrence of ``Type`` is handed its own ``Level``, and all those
levels are accepted by the function up front.

```
const : {ℓ ℓ' : Level}
  → {A : Type ℓ}
  → {B : Type ℓ'}
  → A
  → B → A
const a b = a

×-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  → {A : Type ℓ₁} {B : Type ℓ₂}
  → {A' : Type ℓ₃} {B' : Type ℓ₄}

  → (A → A')
  → (B → B')
  → A × B → A' × B'
×-map f g (a , b) = (f a , g b)

Σ-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  → {A : Type ℓ₁}  {B : A → Type ℓ₂}
  → {A' : Type ℓ₃} {B' : A' → Type ℓ₄}

  → (f : A → A')
  → (g : (a : A) → B a → B' (f a))
  → Σ[ a ∈ A ] B a → Σ[ a' ∈ A' ] B' a'
Σ-map f g (a , b) = (f a , g a b)

Σ-curry : {ℓ₁ ℓ₂ ℓ₃ : Level}
  → {A : Type ℓ₁}
  → {B : A → Type ℓ₂}
  → {C : (x : A) → B x → Type ℓ₃}

  → ((p : Σ[ x ∈ A ] B x) → C (p .fst) (p .snd))
  → (x : A) → (y : B x) → C x y
Σ-curry f x y = f (x , y)

Σ-uncurry : {ℓ₁ ℓ₂ ℓ₃ : Level}
  → {A : Type ℓ₁}
  → {B : A → Type ℓ₂}
  → {C : (x : A) → B x → Type ℓ₃}

  → ((x : A) → (y : B x) → C x y)
  → (p : Σ[ x ∈ A ] B x) → C (p .fst) (p .snd)
Σ-uncurry f p = f (p .fst) (p .snd)
```

And here is our final definition of function composition, where
all the types involved might live in different universes.

```
_∘_ : {ℓ ℓ' ℓ'' : Level}
  → {A : Type ℓ}
  → {B : A → Type ℓ'}
  → {C : (x : A) → B x → Type ℓ''}

  → (g : {a : A} → (b : B a) → C a b)
  → (f : (a : A) → B a)
  → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)

infixr 9 _∘_
```

The built-in type constructors we have seen are universe polymorphic.
These type constructors, like functions `→` and products ``×``, 
can be thought of as functions that take types as arguments and
produce types as output. If you type `C-c C-d` and enter `_×_`, you
will see that it has type

```
_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_ = _×_
```

This uses one additional operation on universe levels, the ``ℓ-max``
operation, which calculates the larger of the two supplied universe
levels. In this case, ``×`` accepts types in any universe and gives
back a type in the largest of those two universes, in a sense lifting
the type in the smaller universe up to the bigger one.

The inductive types we defined earlier are all defined to lie in
``Type``, which is shorthand for the smallest type universe `Type
ℓ-zero`. What if we want to use these inductive types in higher
universes?

One option is to define new versions of those types that specify which
universe level we want them to lie in:

```
data Boolℓ (ℓ : Level) : Type ℓ where
  trueℓ  : Boolℓ ℓ
  falseℓ : Boolℓ ℓ
```

This quickly gets annoying, because we need operations to convert
between versions of ``Boolℓ`` at different universe levels. Instead,
we will use a very simple inductive type to "lift" an arbitrary type
from one universe level to a higher one.

```
data Lift {ℓ-in : Level} (ℓ-out : Level) (A : Type ℓ-in) : Type (ℓ-max ℓ-in ℓ-out) where
  lift : A → Lift ℓ-out A

lower : {ℓ ℓ' : Level} {A : Type ℓ} → Lift ℓ' A → A
lower (lift a) = a
```

The type `Lift A` is really just a wrapper around `A`; for all intents
and purposes the types are the same. But, `Lift A` has a higher
universe level than `A`.

Thankfully, we only need to use this ``Lift`` type very
occasionally; most of the code we write will be completely generic in
which universe levels are used.


## The Empty Type

The type ``⊤`` we saw in the previous Lecture is very simple,
having only one constructor ``tt``. We can go even further
and define a data type ``∅`` with no constructors at all. This is
the "empty type":

```
data ∅ : Type where
  -- Nothing!
```

We want to define functions out of this inductive type by pattern
matching, except in this case there are no constructors and so no
patterns to match with. We cannot just write no definition at all, so
Agda has special syntax for this situation: `()`. This is called an
"absurd" pattern, because to have an actual element of ``∅`` to match
on here would be absurd.

```
impossible-Bool : ∅ → Bool
impossible-Bool ()
```

How have we defined a function into ``Bool`` without actually
mentioning a ``Bool``? Well, this is a function that accepts an
argument that it's impossible to actually give an example of. Because
we can't ever provide an element of type ``∅``, this function never
needs to actually do anything. Its definition is vacuously complete.

And so, the recursion principle of the empty type is a version of the
"ex falso quodlibet" principle that we mentioned when defining
``implies``: regardless of the type `A`, there is always a map `∅ → A`.

```
∅-rec : {ℓ : Level} {A : Type ℓ}
  → (∅ → A)
∅-rec ()
```

Whenever we are defining a function that is provided an argument of
type ``∅``, we can use an absurd pattern to avoid writing anything at
all. On occasion, we won't have an element of ``∅`` handed to us
directly, but will be able derive one from other arguments we have
available. In that situation we will have to use this ``∅-rec`` by
hand.

The recursion principle is saying that a function `∅ → A` contains no
information at all, and so having an element of `∅ → A` is no
different to having an element of ``⊤``. Phrased as a universal
mapping property, our claim is that the following maps are inverses.

```
∅-ump-to : {ℓ : Level} {A : Type ℓ}
  → ⊤
  → (∅ → A)
-- Exercise:
∅-ump-to = {!!}

∅-ump-fro : {ℓ : Level} {A : Type ℓ}
  → (∅ → A)
  → ⊤
-- Exercise:
∅-ump-fro f = {!!}
```


## Disjoint Unions

Next let's define the *disjoint union* of two types. An element of a
disjoint union `A ⊎ B` should either be an element of `A` or an
element of `B`. We can turn this into the definition of an inductive
type. Like ``List``, this is an indexed inductive type. This time, it
requires two other types to be given as input.

```
data _⊎_ {ℓ ℓ' : Level} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
```

The names of the constructors are short for "in-left" and "in-right".

::: Caution:
Other resources may call this type the *coproduct* or *binary sum* of
two types.
:::

Here's a very simple example which just identifies which side the
input is on.

```
isLeft : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
  → A ⊎ B → Bool
isLeft (inl a) = true
isLeft (inr b) = false
```

Since a ``Bool`` is either ``true`` or ``false``, we should be able to
see ``Bool`` as the disjoint union of the singleton sets $\{ true \}$
(represented by ``⊤``) and $\{ false \}$ (represented by another copy of
``⊤``). We can construct maps to that effect:

```
Bool→⊤⊎⊤ : Bool → ⊤ ⊎ ⊤
-- Exercise:
Bool→⊤⊎⊤ b = {!!}

⊤⊎⊤→Bool : ⊤ ⊎ ⊤ → Bool
-- Exercise:
⊤⊎⊤→Bool c = {!!}

_ = test-identical (⊤⊎⊤→Bool (Bool→⊤⊎⊤ true)) true
_ = test-identical (⊤⊎⊤→Bool (Bool→⊤⊎⊤ false)) false
```

You should choose the above maps so that if you turn a ``Bool`` into
an element of `⊤ ⊎ ⊤` and then back into a ``Bool``, you get back to where
you started, and similarly for starting at `⊤ ⊎ ⊤`, so that these maps
give a bijection between ``Bool`` and `⊤ ⊎ ⊤`. (This is checked by
those tests.)

The recursion principle for the disjoint union is "dual" to the
universal mapping property of the product that we saw at the end of
Lecture 1-1. There, we had that from a pair of functions `C → A` and
`C → B` we could get a function `C → A × B`. Here, from a pair of
functions `A → C` and `B → C` we can build a map `A ⊎ B → C`.

```
⊎-rec : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (A → C)
  → (B → C)
  → (A ⊎ B → C)
⊎-rec f g (inl a) = f a
⊎-rec f g (inr b) = g b
```

As a universal mapping property, our claim is that functions *out of*
disjoint unions `A ⊎ B` are the same as pairs of functions from the
two sides.

```
⊎-ump-to : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (A → C) × (B → C)
  → (A ⊎ B → C)
-- Exercise:
⊎-ump-to (f , g) d = {!!}

⊎-ump-fro : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (A ⊎ B → C)
  → (A → C) × (B → C)
-- Exercise:
⊎-ump-fro f = {!!}
```

The type former ``⊎`` is functorial, in a similar manner to ``×-map``:

```
⊎-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
  → {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  → (A → C) → (B → D)
  → A ⊎ B
  → C ⊎ D
-- Exercise:
⊎-map f g d = {!!}
```

It's worth noting for later that the integers are the disjoint union of two
copies of the natural numbers:

```
ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
-- Exercise:
ℤ→ℕ⊎ℕ z = {!!}

ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
-- Exercise:
ℕ⊎ℕ→ℤ z = {!!}
```


## Type Arithmetic

There is a sense in which ``×`` of types acts like ordinary
multiplication of natural numbers. Because ``Bool`` has 2 elements and
``Day`` has 7, the product should have should have 14, which we can
check by case-splitting `Bool × Day` into all its possibilities.

```
count-Bool×Day : Bool × Day → ℕ
count-Bool×Day (true  , monday)    = 1
count-Bool×Day (true  , tuesday)   = 2
count-Bool×Day (true  , wednesday) = 3
count-Bool×Day (true  , thursday)  = 4
count-Bool×Day (true  , friday)    = 5
count-Bool×Day (true  , saturday)  = 6
count-Bool×Day (true  , sunday)    = 7
count-Bool×Day (false , monday)    = 8
count-Bool×Day (false , tuesday)   = 9
count-Bool×Day (false , wednesday) = 10
count-Bool×Day (false , thursday)  = 11
count-Bool×Day (false , friday)    = 12
count-Bool×Day (false , saturday)  = 13
count-Bool×Day (false , sunday)    = 14
```

Similarly, ``⊎`` acts like an addition of natural numbers.

```
count-Bool⊎Day : Bool ⊎ Day → ℕ
count-Bool⊎Day (inl true)      = 1
count-Bool⊎Day (inl false)     = 2
count-Bool⊎Day (inr monday)    = 3
count-Bool⊎Day (inr tuesday)   = 4
count-Bool⊎Day (inr wednesday) = 5
count-Bool⊎Day (inr thursday)  = 6
count-Bool⊎Day (inr friday)    = 7
count-Bool⊎Day (inr saturday)  = 8
count-Bool⊎Day (inr sunday)    = 9
```

We even have exponentiation provided by `→`, so that $n^m$. We can't verify this by
pattern matching (because functions are not inductive types that can
be pattern matched on), but we can reason through why this might be
the case. Consider the type of functions `Bool → Day`. We argued in
``Bool-rec`` that a function out of ``Bool`` is determined by its
value on ``true`` and ``false``. For ``true``, we choose one of 7
options, and for ``false``, we choose one of 7 options again, so
indeed there are $7^2$ possibilities in total.

We have the type ``⊤`` with one element to serve as the natural number
1, and ``∅`` with zero elements to serve as 0. Maybe surprisingly, these operations on
types satisfy a tremendous number of equations that are satisfied by
actual natural numbers.

* $x + y = y + x$,
* $x + (y + z) = (x + y) + z$,
* $x + 0 = x$,
* $x × y = y × x$,
* $x × (y × z) = (x × y) × z$,
* $x × 1 = x$,
* $x × 0 = 0$,
* $x × (y + z) = (x × y) + (x × z)$,
* $(x × y)^z = (x^z) × (y^z)$,
* $x^{y + z} = (x^y) × (x^z)$,
* $(x^y)^z = x^{y×z}$.

(These equations are a bit hard to read in the editor, but they're
nicely formatted on the website version.)

::: Aside:
In ordinary set-based mathematics, this is sometimes known as
[cardinal arithmetic].
:::

[cardinal arithmetic]: https://en.wikipedia.org/wiki/Cardinal_number#Cardinal_arithmetic

These turn out to be quite useful, so we'll prove a few of them here.
In fact, we have demonstrated several of them already in the form of
functions in each direction:

* ``×-commⁱ`` shows $x × y = y × x$,
* ``×-assoc-toⁱ`` and ``×-assoc-froⁱ`` show $x × (y × z) = (x × y) × z$,
* ``×-ump-to`` and ``×-ump-fro`` show $(x × y)^z = (x^z) × (y^z)$,
* ``×-curry`` and ``×-uncurry`` show $(x^y)^z = x^{y×z}$.
* ``⊎-ump-to`` and ``⊎-ump-fro`` show $x^{y + z} = (x^y) × (x^z)$,

The missing "multiplicative" law is the one showing that $x × 1 = x$.

```
×-idl-to : (A : Type) → ⊤ × A → A
-- Exercise:
×-idl-to A x = {!!}

×-idl-fro : (A : Type) → A → ⊤ × A
-- Exercise:
×-idl-fro A a = {!!}
```

Next the laws for addition, which can all verified by pattern matching.

```
⊎-comm : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
  → A ⊎ B → B ⊎ A
-- Exercise:
⊎-comm = {!!}

⊎-assoc-to : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
-- Exercise:
⊎-assoc-to = {!!}

⊎-assoc-fro : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
-- Exercise:
⊎-assoc-fro = {!!}
```

The type ``∅`` acts like zero with respect to addition. Remember,
whenever you have an element of ``∅``, you are in an absurd situation
and no longer have any obligation to prove the result!

```
∅⊎-to : {ℓ : Level} (A : Type ℓ) → ∅ ⊎ A → A
-- Exercise:
∅⊎-to A x = {!!}

∅⊎-fro : {ℓ : Level} (A : Type ℓ) → A → ∅ ⊎ A
-- Exercise:
∅⊎-fro A a = {!!}
```

Finally, we have the laws that relate the additive and multiplicative
worlds. Anything multiplied by 0 is 0:

```
∅×-to : {ℓ : Level} (A : Type ℓ)
  → ∅ × A → ∅
-- Exercise:
∅×-to A x = {!!}

∅×-fro : {ℓ : Level} (A : Type ℓ)
  → ∅ → ∅ × A
-- Exercise:
∅×-fro A a = {!!}
```

And multiplication distributes over addition:

```
×-⊎-distr : {ℓ : Level} {A B C : Type ℓ}
  → (A × (B ⊎ C))
  → (A × B) ⊎ (A × C)
-- Exercise:
×-⊎-distr x = {!!}

×-⊎-distr-inv : {ℓ ℓ' : Level} {A B C : Type ℓ}
  → (A × B) ⊎ (A × C)
  → (A × (B ⊎ C))
-- Exercise:
×-⊎-distr-inv x = {!!}
```

These rules have dependently-typed variants, where multiplication is
replaced by a Σ-type. As your last exercise, work out what the types
have to be:

```
∅Σ-to : {ℓ : Level} (A : ∅ → Type ℓ)
-- Exercise:
     → {!!}
     → {!!}

∅Σ-to A x = x .fst

∅Σ-fro : {ℓ : Level} (A : ∅ → Type ℓ)
-- Exercise:
     → {!!}
     → {!!}

∅Σ-fro A ()

Σ-⊎-distr : {ℓ ℓ' : Level} {A : Type ℓ} {B C : A → Type ℓ'}
-- Exercise:
     → {!!}
     → {!!}

Σ-⊎-distr (a , inl b) = inl (a , b)
Σ-⊎-distr (a , inr c) = inr (a , c)

Σ-⊎-distr-inv : {ℓ ℓ' : Level} {A : Type ℓ} {B C : A → Type ℓ'}
-- Exercise:
     → {!!}
     → {!!}

Σ-⊎-distr-inv (inl (a , b)) = (a , inl b)
Σ-⊎-distr-inv (inr (a , c)) = (a , inr c)
```


## References and Further Reading

* The original *[Homotopy Type Theory]* book:
  * Universes: Chapter 1.3
  * Empty Type: Chapter 1.7
  * Disjoint Unions: Chapter 1.7
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Universes: Chapter 6
  * Empty Type: Chapter 4.3
  * Disjoint Unions: Chapter 4.4
* Martin Escardo's [Lecture Notes]:
  * [Universes](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes)
  * [Empty Type](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#emptytype)
  * [Disjoint Unions](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#binarysum)
* Agda Documentation
  * [Sorts and Universes](https://agda.readthedocs.io/en/latest/language/sort-system.html)
  * [Universe Levels](https://agda.readthedocs.io/en/latest/language/universe-levels.html)

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html

* Talk slides by Emily Riehl on [Categorifying cardinal arithmetic]
* [An Analysis of Girard's Paradox] by Thierry Coquand
* [A Simplification of Girard's Paradox] by Antonius J.C. Hurkens

[Categorifying cardinal arithmetic]: https://math.jhu.edu/~eriehl/arithmetic.pdf
[An Analysis of Girard's Paradox]: https://www.cse.chalmers.se/~coquand/girard.pdf

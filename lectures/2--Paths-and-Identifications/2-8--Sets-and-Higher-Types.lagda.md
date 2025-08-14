<!--
```
module 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types where

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

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
```
-->


# Lecture 2-8: Sets and Higher Types

We saw in Lecture 2-3 that paths in types like ``Bool``, ``ℕ`` and
``ℤ`` are equalities between elements. As a consequence, for any two
elements `x` and `y`, the type of paths `x ≡ y` is always a
proposition --- specifically, the proposition that `x` equals `y`.

We call types with this property *sets*. Sets represent the
mathematical objects we're most familiar with from classical
mathematics: discrete structures whose equality is unambiguous.

```
isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
```

As we did for propositions, we'll spend some time proving closure
properties for sets.


## Basic Examples

We characterised the types of paths in ``⊤``, ``Bool`` and ``ℕ`` back
in Lecture 2-3, and from those characterisations it is easy to show
these types are sets.

```
isSet-⊤ : isSet ⊤
-- Exercise: (Hint: `≡≃≡⊤`)
isSet-⊤ x y = isProp-equiv {!!} {!!}

isSet-Bool : isSet Bool
-- Exercise:
isSet-Bool x y = {!!}

isSet-ℕ : isSet ℕ
-- Exercise:
isSet-ℕ x y = {!!}
```

The empty type ``∅`` is the set with no elements.

```
isSet-∅ : isSet ∅
-- Exercise:
isSet-∅ = {!!}
```

For ``⊎``, we will need a helper that relates paths in the two sides
to the characterisation ``≡⊎`` from back in Lecture 2-3.

```
isProp-≡⊎ : {A B : Type} → isSet A → isSet B → (a b : A ⊎ B) → isProp (a ≡⊎ b)
-- Exercise:
isProp-≡⊎ sA sB a b = {!!}

isSet-⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
-- Exercise:
isSet-⊎ pA pB = {!!}
```

Every proposition is a set. This may sound like an odd claim,
especially if you are used to first-order logic where there is a
strict separation between the two. In our setting, any proposition `P`
is a set that has at most one element.

```
isProp→isSet : isProp A → isSet A
-- Exercise:
isProp→isSet pA x y = {!!}
```

Again, not all types are sets. The type ``S¹`` should not be a set
since we have a path ``loop`` that we know is not the same as
``refl``.

```
¬isSet-S¹ : ¬ isSet S¹
-- Exercise:
¬isSet-S¹ isSet = {!!}
```

The type ``Type`` is not a set either. If all paths in ``Type`` were
equal, then ``not-Path`` would be equal to ``refl`` as a path `Bool ≡
Bool`, and this quickly leads to a contradiction.

```
¬isSet-Type : ¬ isSet Type
-- Exercise: (Hint: `true≢false`)
¬isSet-Type s = {!!}
```

One way of thinking of ``isSet`` is that for any paths `p : x ≡ y` and
`q : x ≡ y` there is a ``Square`` with shape

            refl
        y — — — — > y
        ^           ^            ^
      p |           | q        j |
        |           |            ∙ — >
        x — — — — > x              i
            refl

Of course, we can't necessarily get some ``Square`` like this for any
choice of corners `x` and `y`, we need the paths `p` and `q` to exist
to begin with.

So, ``isSet`` is like ``isProp`` but one dimension higher. We can't
necessarily fill a path between any two points, but we can fill any
``Square``:

```
isSet→Square : isSet A
  → {a b c d : A}
  → (r : a ≡ c) (s : b ≡ d)
  → (t : a ≡ b) (u : c ≡ d)
  → Square t u r s
-- Exercise: (Hint: `toPathP`)
isSet→Square sA r s t u = {!!}
```

Because being a set means that asking that a certain family of types
is all propositions, ``isSet`` is a proposition about a type.

```
isProp-isSet : isProp (isSet A)
-- Exercise: (Use `isProp-Π`)
isProp-isSet = {!!}
```


## Closure Properties

We can show a number of closure properties of sets like those for
propositions and contractible types.

First, if `A` and `B` are sets, then `A × B` is a set, and for `A → B`
it is sufficient for just `B` to be a set.

```
isSet-× : isSet A → isSet B → isSet (A × B)
-- Exercise:
isSet-× pA pB = {!!}

isSet-→ : isSet B → isSet (A → B)
-- Exercise:
isSet-→ pB = {!!}
```

Similarly to contractible types and propositions, any retract of a set
is a set. This follows easily from the following general about fact
about homotopies, which is a higher-dimensional generalisation of
``homotopy-Path``. On its own, a homotopy lets us

               g b — — — — — — — > g d
              / ^                 / ^
            /   |               /   |
          /     |             /     |
       g a — — — — — — — > g c      |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |      f b — — — —  |— — > f d
        |     /             |     /
        |   /               |   /
        | /                 | /
       f a — — — — — — — — f c

```
homotopy-Square : {f g : A → B}
  → (H : (x : A) → (f x ≡ g x))
  → {a b c d : A}
  → {r : a ≡ c} {s : b ≡ d}
  → {t : a ≡ b} {u : c ≡ d}
  → Square (ap f t) (ap f u) (ap f r) (ap f s)
  → Square (ap g t) (ap g u) (ap g r) (ap g s)
-- Exercise: (Hint: Use an `hcomp` with `sq` as the base and `homotopy-Square` on all sides.)
homotopy-Square {B = B} H {r = r} {s} {t} {u} sq i j = {!!}
```

::: Aside:
Alternatively, produce a path

      Square (ap f t) (ap f u) (ap f r) (ap f s) 
    ≡ Square (ap g t) (ap g u) (ap g r) (ap g s)

and apply ``transport``.
:::

```
isSet-retract : B RetractOnto A → isSet B → isSet A
isSet-retract r sB x y p q 
  = homotopy-Square (r .section .proof) (ap-Square (r .map) (sB _ _ _ _))

isSet-equiv : A ≃ B → isSet B → isSet A
isSet-equiv = isSet-retract ∘ equiv→retract
```

And ``isSet-equiv`` lets us easily clear up ``ℤ``, without fussing
about with defining an observational equality type `≡ℤ`:

```
isSet-ℤ : isSet ℤ
-- Exercise: (Hint: Find a useful equivalence in Lecture 2-2)
isSet-ℤ = isSet-equiv {!!} {!!}
```


## Hedberg's Theorem

There's a very slick criterion for when a type is a set: Hedberg's
Theorem. Recall the notion of decidable type from the end of Lecture
1-5. A type `A` is decidable when we have an inhabitant of `A ⊎ ¬ A`,
which we packaged into the ``Dec`` inductive type.

Hedberg's Theorem states that any type with *decidable equality* is a
set. A type has decidable equality whenever the type of paths between
any two points is decidable:

```
Dec≡ : Type ℓ → Type ℓ
Dec≡ A = (x y : A) → Dec (x ≡ y)
```

We are assuming that the path types in `A` are all decidable, but not
that they are decidable *propositions*. (After all, if we already knew
they were propositions then we would already know our type is a set.)

Here's a simple example. All propositions have decidable equality.
Given two elements of a proposition it is easy to decide whether they
are equal, the answer is always ``yes``!

```
isProp→Dec≡ : isProp A → Dec≡ A
-- Exercise:
isProp→Dec≡ pA = {!!}
```

Inductive types often have decidable equality. The proofs are much
like the (very similarly named) ``Dec-≡Bool`` and ``Dec-≡ℕ``
definitions from earlier, which we wrote before we had the notion of
path types.

```
Dec≡-Bool : Dec≡ Bool
-- Exercise:
Dec≡-Bool = {!!}

Dec≡-ℕ : Dec≡ ℕ
-- Exercise:
Dec≡-ℕ = {!!}
```

We will prove Hedberg's Theorem using a slick argument that we learned
from [Favonia]. Here is the idea. Start with a path `p : x ≡ y`. By
assumption, `x ≡ y` is decidable, so we also have an element of `Dec
(x ≡ y)`. This can't be ``no``, because that would cause a
contradiction: after all, we already know that `x ≡ y` via `p`.

[Favonia]: https://favonia.org/courses/hdtt2020/

So we have `yes q : Dec (x ≡ y)`, where `q : x ≡ y` is also a path
between the same points. But here is the key: this path `q` is the
*same*, regardless of which `p` we start with.

Start by defining a function that either replaces a path `p` with the `q`
from `Dec (x ≡ y)` or derives a contradiction.

```
Dec≡-bad-replacement : {x y : A} → Dec (x ≡ y) → x ≡ y → x ≡ y
-- Exercise:
Dec≡-bad-replacement d p = {!!}
```

Next, we want to show that this replacement is equal to the path that
we started with. The plan is to do this using ``J``, but for that
to work we need the replacement to equal ``refl`` when `p` is
itself ``refl``. Right now it isn't: instead, the replacement is
just `Dec≡-bad-replacement (dec x x) refl : x ≡ x`, which doesn't
simplify.

This is easily fixed. Define a function that gives a good replacement
path, by composing the old definition with the inverse of the path
`Dec≡-bad-replacement (dec x x) refl` that we want to get rid of:

```
Dec≡-good-replacement : Dec≡ A → {x y : A} → x ≡ y → x ≡ y
-- Exercise:
Dec≡-good-replacement dec {x} {y} p = {!!}

Dec≡-replacement-undo : (dec : Dec≡ A) → {x y : A} → (p : x ≡ y) → Dec≡-good-replacement dec p ≡ p
-- Exercise:
Dec≡-replacement-undo dec {x} {y} p = J (λ y p → Dec≡-good-replacement dec p ≡ p) {!!} {!!}
```

The final lemma is that these good replacements are all equal to each
other, regardless of what path you start with. This is easy after
pattern matching on `Dec (x ≡ y)`.

```
Dec≡-replacement-same : (dec : Dec≡ A) → {x y : A} → (p₁ p₂ : x ≡ y)
  → Dec≡-good-replacement dec p₁ ≡ Dec≡-good-replacement dec p₂
-- Exercise:
Dec≡-replacement-same dec {x} {y} p₁ p₂ = {!!}

  where helper : (w : Dec (x ≡ y)) →
            sym (Dec≡-bad-replacement (dec x x) refl) ∙ Dec≡-bad-replacement w p₁
          ≡ sym (Dec≡-bad-replacement (dec x x) refl) ∙ Dec≡-bad-replacement w p₂
--      Exercise:
        helper d = {!!}
```

Now glue these pieces together to finish the proof.

```
hedberg : Dec≡ A → isSet A
hedberg dec x y p₁ p₂ =
-- Exercise:
     p₁                           ≡⟨ {!!} ⟩
     Dec≡-good-replacement dec p₁ ≡⟨ {!!} ⟩
     Dec≡-good-replacement dec p₂ ≡⟨ {!!} ⟩
     p₂ ∎
```


## Higher Types

You may have noticed a pattern developing in the last couple of
Lectures. We started with the simplest possible types, contractible
types, and have gradually considered types that contain more and more
interesting paths.

* Contractible types contain no information at all. We'll declare
  these to have "h-level 0".
* Propositions are exactly the types whose path types are
  contractible, as we checked in ``isProp→isContr≡`` and
  ``isContr≡→isProp``. We'll declare these to have "h-level 1".
* Sets we are now defining to be the types whose path types are
  propositions, and so we will say have "h-level 2".
* Continuing this way, types with "h-level 3" are those whose path
  types are sets. We have already seen a nontrivial example: ``S¹``,
  as we proved in Lecture 2-6.

And so on, with higher and higher types.

```
isHLevel : ℕ → Type ℓ → Type ℓ
isHLevel zero    X = isContr X
isHLevel (suc n) X = (x y : X) → isHLevel n (x ≡ y)
```

The h-level of a type is one way to measure the complexity of its path
spaces: a type with a known h-level has all its interesting
information *below* a certain dimension. Inspecting higher dimensional
paths eventually reaches path types that are contractible, and all
higher dimensional path types from that point on remain contractible
(thanks to ``isContr→isContr≡``).

There is a dual way of measuring the complexity of a type that instead
specifies that a type has all its interesting paths *above* a certain
dimension. This is known as "connectedness", and we discuss it further
in Lecture 3-2.

::: Caution:
In homotopy theory, a different numbering system is used for h-levels,
so that the hierarchy shifted down by two. A set, i.e. a type with
h-level 2, is said to have "truncation level 0", and a proposition has
"truncation level -1". Sometimes this is shortened even further, so
that a set is a "0-type" and a proposition is a "(-1)-type". This is
just a difference in conventions, but will be necessary to keep in
mind when reading other sources.
:::

::: Aside:
This definition doesn't exactly match ``isProp`` when `n = 1`, but as
we saw in ``isProp→isContr≡`` and ``isContr≡→isProp``, it is
equivalent. An alternative definition would specify

    isHLevel (suc zero) X = isProp X

directly rather than leaving that to the inductive case. We'll stick
with the simpler definition so that we have one fewer case to deal
with in our proofs. It is easy enough to patch over the difference
using what we've proven already:

```
isProp→isHLevel1 : isProp A → isHLevel 1 A
isProp→isHLevel1 = isProp→isContr≡

isHLevel1→isProp : isHLevel 1 A → isProp A
isHLevel1→isProp = isContr≡→isProp

isSet→isHLevel2 : isSet A → isHLevel 2 A
isSet→isHLevel2 sA x y = isProp→isHLevel1 (sA x y)

isHLevel2→isSet : isHLevel 2 A → isSet A
isHLevel2→isSet hA x y = isHLevel1→isProp (hA x y)
```
:::


We can systematise some of the results we've seen in this Lecture and
the previous. First up, ``isContr→isProp`` and ``isProp→isSet``:

```
isHLevel-suc : (n : ℕ) → isHLevel n A → isHLevel (suc n) A
-- Exercise:
isHLevel-suc n = {!!}
```

Next, ``isProp-isContr``, ``isProp-isProp`` and ``isProp-isSet``:

```
isProp-isHLevel : (n : ℕ) → isProp (isHLevel n A)
-- Exercise:
isProp-isHLevel n = {!!}
```

Finally, the many closure properties we've seen so far. You'll find
``isHLevel-equiv`` useful for both ``isHLevel-Σ`` and ``isHLevel-Π``.

```
isHLevel-≡ : (n : ℕ)
  → isHLevel n A
  → (x y : A) → isHLevel n (x ≡ y)
-- Exercise: (This one is easier than it sounds!)
isHLevel-≡ n = {!!}

isHLevel-retract : (n : ℕ) → B RetractOnto A → isHLevel n B → isHLevel n A
-- Exercise:
isHLevel-retract n = {!!}

isHLevel-equiv : (n : ℕ) → (A ≃ B) → isHLevel n B → isHLevel n A
isHLevel-equiv n = isHLevel-retract n ∘ equiv→retract

isHLevel-Σ : {A : Type ℓ} → {B : A → Type ℓ'} 
  → (n : ℕ) 
  → isHLevel n A 
  → ((x : A) → isHLevel n (B x))
  → isHLevel n (Σ[ x ∈ A ] B x)
-- Exercise:
isHLevel-Σ n = {!!}

isHLevel-Π : {B : A → Type ℓ}  
  → (n : ℕ)
  → ((x : A) → isHLevel n (B x))
  → isHLevel n ((x : A) → B x)
-- Exercise:
isHLevel-Π n = {!!}
```

This is all well and good, but do we have concrete examples of types
with a h-level higher than that of sets? We saw in ``¬isSet-S¹`` that
``S¹`` is not a set, but it does have the next h-level beyond that.
(Such types are often called "groupoids".)

All the hard work was done back in Lecture 2-6. We know that
`base ≡ base` is equivalent to ``ℤ``, a set, and so has h-level 2. It
just takes a little futzing around to show the same is true for any
endpoints `x` and `y`.

```
isHLevel3-S¹' : isHLevel 3 S¹
isHLevel3-S¹' = isHLevel-2-x≡y
  where
  isHLevel-2-base≡base : isHLevel 2 (base ≡ base)
  -- Exercise:
  isHLevel-2-base≡base = {!!}

  isHLevel-2-base≡y : (y : S¹) → isHLevel 2 (base ≡ y)
  isHLevel-2-base≡y = S¹-ind isHLevel-2-base≡base (isProp→any-PathP (λ _ → isProp-isHLevel 2) _ _)

  isHLevel-2-x≡y : (x y : S¹) → isHLevel 2 (x ≡ y)
  isHLevel-2-x≡y = S¹-ind isHLevel-2-base≡y (isProp→any-PathP (λ _ → isProp-Π λ _ → isProp-isHLevel 2) _ _)
```

## References and Further Reading

* The original *[Homotopy Type Theory]* book:
  * Sets: Chapter 3.1
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Sets: Chapter 12.3
  * Higher Types: Chapter 12.4
* Martin Escardo's [Lecture Notes]:
  * [Sets](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#set-types)
  * [Hedberg's Theorem](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#hedberg)

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html

* Original paper presenting Hedberg's Theorem: [A coherence theorem for Martin-Löf's type theory](https://doi.org/10.1017/S0956796898003153) by Michael
  Hedberg

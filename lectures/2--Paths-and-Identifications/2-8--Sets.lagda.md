```
module 2--Paths-and-Identifications.2-8--Sets where
```

# Lecture 2-8: Sets

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

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A A' B P Q : Type ℓ
```
-->

As we saw in Lecture 2-1, paths in inductive types like ``Bool``,
``ℕ`` and ``ℤ`` are equalities between elements. As a
consequence, for any two elements `x` and `y`, the type of paths
`x ≡ y` is always a proposition --- specifically, the proposition that
`x` equals `y`.

We call types with this property *sets*.

```
isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
```

The type ``⊤`` is a one-element set, and the empty type
``∅`` is the set with no elements.

```
isSet⊤ : isSet ⊤
-- Exercise: (Remember, you characterised paths in `⊤` in `≡≃≡⊤`)
isSet⊤ x y = isPropEquiv {!!} {!!}

isSet∅ : isSet ∅
-- Exercise:
isSet∅ = {!!}
```

Other inductive typed are similar to ``⊤``: we already
characterised their types of paths back in Lecture 2-3.

```
isSetBool : isSet Bool
-- Exercise:
isSetBool x y = {!!}

isSetℕ : isSet ℕ
-- Exercise:
isSetℕ x y = {!!}
```

For ``⊎``, we will need a helper that connects paths in the two
sides to the characterisation ``≡⊎``.

```
isProp-≡⊎ : {A B : Type} → isSet A → isSet B → (a b : A ⊎ B) → isProp (a ≡⊎ b)
-- Exercise:
isProp-≡⊎ sA sB a b = {!!}

isSet⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
-- Exercise:
isSet⊎ pA pB = {!!}
```

Not all types are sets. Intuitively, ``S¹`` should not be a set
since we have a non-trivial path ``loop`` right there. Use
``refl≢loop`` to show that ``S¹`` is also not a set.

```
¬isSet-S¹ : ¬ isSet S¹
-- Exercise:
¬isSet-S¹ isSet = {!!}
```

It is also easy to show that ``Type`` itself is not a set. Here's
the idea: if all paths in ``Type`` were equal, then
`not-Path`{.Adga} would be equal to ``refl``. Use this with
``true≢false`` to reach a contradiction.

```
¬isSet-Type : ¬ isSet Type
-- Exercise:
¬isSet-Type s = {!!}
```


## Closure Propertis of Sets

We can show a number of closure properties of sets, similar to those
we showed for propositions and contractible types.

First, if `A` and `B` are sets, then `A × B` is a set, and for `A → B`
it is sufficient for just `B` to be a set.

```
isSet× : isSet A → isSet B → isSet (A × B)
-- Exercise:
isSet× pA pB = {!!}

isSet→ : isSet B → isSet (A → B)
-- Exercise:
isSet→ pB = {!!}
```

Similar to contractible types and propositions, any retract of a set
is a set. This will involve filling the following cube:


                y - - - - - - - - > y
         p    / ^             q   / ^
            /   |               /   |
          /     |             /     |
        x - - - - - - - - > x       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |    r (s y)  - - - | - > r (s y)
     r (s q)  /             |     /
        |   /               |   /  r (s q)
        | /                 | /
      r (s x) - - - - - - r (s x)


```
isSetRetract : B RetractionOnto A → isSet B → isSet A
isSetRetract {A = A} (r , s , h) setB x y p q i j = hcomp faces (bottom i j)
  where
    bottom : Square (cong r (cong s p)) (cong r (cong s q)) refl refl
    -- Exercise:
    bottom = {!!}

    faces : I → Partial (∂ i ∨ ∂ j) A
    -- Exercise:
    faces k (i = i0) = {!!}
    faces k (i = i1) = {!!}
    faces k (j = i0) = {!!}
    faces k (j = i1) = {!!}

isSetEquiv : A ≃ B → isSet B → isSet A
isSetEquiv = isSetRetract ∘ equivRetracts
```

``isSetRetract`` enables a slick proof that any proposition is a
set. This may sound like an odd claim, but we can think of any
proposition `P` as a set with at most one element.

```
isProp→isSet : isProp A → isSet A
-- Exercise:
isProp→isSet {A = A} pA x y = isSetRetract {!!} {!!} {!!} {!!}
```

Univalence allows us to prove that the type of
propositions is a set.

First, being an equivalence between propositions it itself a
proposition. (In fact, this is true for functions between any types,
as we prove with a lot more effort in Lecture X-X, but it is easy
enough to prove directly for the case we need it here.)

```
isPropisEquiv-for-Props : isProp P → isProp Q → (f : P → Q) → isProp (isEquiv f)
-- Exercise: (Hint: Glue together `isPropΣ` and `isPropΠ` a few times.)
isPropisEquiv-for-Props pP pQ f = {!!}

```

Then, the existence of a path between two propositions is a
proposition:

```
isProp≃OfProp : (P Q : Prop ℓ) → isProp (fst P ≃ fst Q)
-- Exercise:
isProp≃OfProp (P , pP) (Q , pQ) e f = {!!}

isProp≡OfProp : (P Q : Prop ℓ) → isProp (fst P ≡ fst Q)
-- Exercise:
isProp≡OfProp P Q = isPropRetract {!!} {!!}
```

And finally ``≡Subtype`` tells us that this is sufficient: A path
in ``Prop`` is the same as a path of the underlying types, which
is enough to get the conclusion we wanted.

```
isSetProp : isSet (Prop ℓ)
-- Exercise:
isSetProp P Q = {!!}
```


## Hedberg's Theorem


Thre's a very slick criterion for when a type is a set, a fact which
is known as Hedberg's Theorem. This states that any type with
"decidable equality" is a set. A type has decideable equality whenever
the type of paths between any two points is decideable.

```
Dec≡ : {ℓ : Level} → Type ℓ → Type ℓ
Dec≡ A = (x y : A) → Dec (x ≡ y)
```

Note that we are assuming that the path types are all decidable, but
not that they are decideable *propositions*. (After all, if we already
knew they were propositions then we would already know our type is a
set.)

Here's a simple example. We have seen that not all propositions are
decidable, but all propositions have decidable equality. Given two
elements of a proposition it is easy to decide whether they are equal,
the answer is always ``yes``!

```
isProp→Dec≡ : isProp A → Dec≡ A
-- Exercise:
isProp→Dec≡ pA = {!!}
```

Inductive types often have decidable equality. The proofs are much
like the (very similarly named) ``Dec-≡Bool`` and `Dec-≡ℕ{.Agda}
definitions from earlier, which we wrote before we had the notion of
path.

```
Dec≡-Bool : Dec≡ Bool
-- Exercise:
Dec≡-Bool = {!!}

Dec≡-ℕ : Dec≡ ℕ
-- Exercise:
Dec≡-ℕ = {!!}
```

We will prove Hedberg's theorem using a slick proof that we learned
from Favonia. mvrnote: link. Here is the idea. Suppose we have a path
`p : x ≡ y`. By assumption, `x ≡ y` is decidable, so we also have an
element of `Dec (x ≡ y)`. This can't be ``no``, because that
would immediately give a contradiction: after all, we already have the
path `p`.

So we have `yes q : Dec (x ≡ y)`, where `q : x ≡ y` is also a path
between the same two points. But here is the key: this path `q` is the
*same*, regardless of which `p₁` we start with.

Start by defining a function that replaces a path `p` with the `q`
from `Dec (x ≡ y)`, or derives a contradiction.

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
pattern-matching on `Dec (x ≡ y)`.

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




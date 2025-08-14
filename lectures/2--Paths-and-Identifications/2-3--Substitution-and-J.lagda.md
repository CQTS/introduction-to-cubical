<!--
```
module 2--Paths-and-Identifications.2-3--Substitution-and-J where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y : A
```
-->


# Lecture 2-3: Substitution and J

One of the fundamental principles of equality is that we may
substitute equal things for equal things. Consider a predicate like
``isEvenP``: if `x` and `y` are natural numbers with `x ≡ y` and we
know that `isEvenP x`, then we should certainly be able to conclude
that `isEvenP y`.

This principle is so basic that we take it for granted. But looking at
the operations we have available so far, there is nothing that allows
us to do this. In this Lecture we'll introduce the primitive operation
that Cubical Agda provides for substitution: ``transport``.

Together with some of the path algebra from last lecture, we will use
``transport`` to prove Martin-Löf's ``J`` rule, which is a powerful
induction principle for path types. This is much like the induction
principles we saw for the inductive types in Lectures 1-2 and 1-3:
just as we can define functions out of ``ℕ`` giving a case for
``zero`` and ``suc``, we will be able to define functions out of path
types by giving a case just for ``refl``.

Finally, we'll use this ``J`` rule to fully characterise the paths in
some of the inductive types we've seen so far, showing for example
that paths in ``Bool`` correspond to the observational equality
``≡Bool`` that we expect. For this, we'll use the well-known
"encode-decode" method.


## Substitution

Given a type family `B : A → Type` thought of as a predicate, and a
path `p : x ≡ y` in the type `A`, we want a function
`subst B p : B x → B y` that "substitutes `x` for `y` in things of
type `B x`".

```
subst : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
```

To see exactly what primitive notion we are missing, consider that we
haven't yet said what a path `I → Type` should be.

Taking a cue from homotopy theory, we expect that a path between
spaces should be a continuous deformation of one space into
another --- a so-called "homotopy equivalence". In particular, then,
if we have a path `A : I → Type`, we should be able to "continuously
move" an element `a : A i0` to some element of `A i1`. This is called
"transporting" the element `a` from `A i0` to `A i1` along the path of
types `A`. Agda axiomatizes this idea with a function called
``transport``.

```
transport : A ≡ B → A → B
```

::: Aside:
Well, actually, ``transport`` is defined via a slightly more
general operation unhelpfully called ``transport-fixing``, which we will
return to in Lecture 2-5.
```
transport p a = transport-fixing (λ i → p i) i0 a
```
:::

Using ``transport``, we can define ``subst`` by transporting in the
path of types `(λ i → B (p i)) : B x ≡ B y`. We know the endpoints of
this path are correct because `p i0` is exactly `x` and `p i1` is
exactly `y`.

```
subst B p b = transport (λ i → B (p i)) b
```

Our first application of ``subst`` is showing that there is no path
from ``true`` to ``false`` in ``Bool``.

```
true≢false : ¬ (true ≡ false)
true≢false p = subst (λ b → true ≡Bool b) p tt
```

Let's take a minute to make sure we understand what's going on here.
Remember that ``¬`` is defined to be simply functions into ``∅``, so
``true≢false`` is a function `true ≡ false → ∅`. That is, to prove
that ``true`` doesn't equal ``false``, we assume we have a path 
`true ≡ false` and derive a contradiction. How do we do this?

Well, we have by definition that `true ≡Bool true` is ``⊤`` and that
`true ≡Bool false` is ``∅``, this time using the type family ``≡Bool``
that we defined for observational equality. If we're given a path 
`p : true ≡ false`, then we could replace the second ``true`` in 
`true ≡Bool true` with ``false`` to get an element of 
`true ≡Bool false`, which would finish our proof.

The family we are substituting in is therefore `(λ b → true ≡Bool b)`.
The resulting term `subst (λ b → true ≡Bool b) p` is a function `true
≡Bool true → true ≡Bool false`, so unwinding the definition of
``≡Bool``, a function `⊤ → ∅`. This we can simply feed in ``tt`` to
obtain an element of ``∅``, our contradiction.

Try proving a similar fact for ``ℕ``, that zero is not equal to any
successor.

```
zero≢suc : {n : ℕ} → ¬ zero ≡ suc n
-- Exercise:
zero≢suc p = {!!}
```

While we're here, we can show that the constructors for ``⊎`` are also
disjoint. These proofs all go roughly the same way. You'll first need
a predicate ``IsInl``, to take the place of ``true ≡Bool b`` in the
previous proof.

```
IsInl : A ⊎ B → Type
-- Exercise:
IsInl s = {!!}

inl≢inr : ¬ inl x ≡ inr y
-- Exercise: (Hint: it may help to specify the endpoints of the `subst`, so `subst {x = ...} {y = ...}`)
inl≢inr {x = x} {y = y} path = {!!}

inr≢inl : ¬ inr x ≡ inl y
-- Exercise:
inr≢inl path = {!!}
```


## Martin-Löf's J Rule

Combining transport with the the De Morgan structure on the interval,
we can show a fundamental but not-as-well-known principle of identity:
Martin-Löf's ``J`` rule.

Recall the ``connection∧`` square:

              p
         x — — — > y
         ^         ^
    refl |         | p               ^
         |         |               j |
         x — — — > x                 ∙ — >
            refl                       i

Reading this square in the `i` direction, we can see it as a path
between ``refl`` and `p` which keeps the beginning of the path
constant at `x` but lets the other end vary along `p`. We can
therefore take any property of the path `refl : x ≡ x` and transport
it to any path `p : x ≡ y` beginning with `x`. The ``J``-rule
expresses this principle.

```
J-line : (Q : (y : A) → x ≡ y → Type ℓ)
  → (p : x ≡ y)
  → Q x refl ≡ Q y p
J-line Q p i = Q (p i) (connection∧ p i)

J : (Q : (y : A) → x ≡ y → Type ℓ)
  → (r : Q x refl)
  → (p : x ≡ y)
  → Q y p
J Q r p = transport (J-line Q p) r
```

If we think of the dependent type `Q` as a property, then the
``J`` rule says that to prove `Q y p` for all `y : A` and `p : x
≡ y`, it suffices to prove `Q` just when `y` is `x` and the path `p`
is ``refl``. For this reason, the ``J`` rule is sometimes
known as "path induction" since it resembles an induction principle
like ``Bool-ind`` or ``ℕ-ind``: proving a property of all
elements of a type by proving the property for specific cases.

For comparison:

* Induction for ``Bool``: To prove `Q b` for all `b : Bool`, it
  suffices to prove `Q true` and `Q false`.
* Induction for ``ℕ``: To prove `Q n` for all `n : ℕ`, it
  suffices to prove `Q zero`, and `Q (suc n)` assuming that `Q n`.
* Induction for ``Path``: To prove `Q y p` for all elements `y : A`
  and paths `p : x ≡ y`, it suffices to prove `Q x refl`.

The induction principle for ``Bool`` includes a convenient computation
rule: if `f b : Q b` is defined by induction from `x : P true` and `y
: Q false`, then if we know `b` concretely then we get back exactly
the corresponding input we used: `f true = x` and `f false = y` by
definition. We can prove a similar fact for the ``J`` rule, but
unfortunately we only get a path, and ``J`` doesn't actually *compute*
to `r` when handed ``refl``.

```
J-refl : (Q : (y : A) → x ≡ y → Type ℓ) (r : Q x refl)
      → J Q r refl ≡ r
J-refl Q r i = transport-fixing (λ _ → Q _ refl) i r
```

::: Aside:
Right now we don't have the tools to understand the definition of
``J-refl``, but when we cover ``transport-fixing`` in Lecture 2-5, we will
recognise the above definition as exactly ``transport-refl``.
:::

The ``J`` rule is one half of an equivalence, giving a universal
mapping property for paths.

```
J-ump-≃ : (Q : (y : A) → x ≡ y → Type ℓ)
  → ((y : A) → (p : x ≡ y) → Q y p) ≃ Q x refl
J-ump-≃ {A = A} {x = x} Q = inv→equiv to fro to-fro fro-to
  where
    to : ((y : A) → (p : x ≡ y) → Q y p) → Q x refl
--  Exercise:
    to f = {!!}

    fro : Q x refl → ((y : A) → (p : x ≡ y) → Q y p)
--  Exercise:
    fro q y p = {!!}

    to-fro : isSection to fro
--  Exercise: (Hint: this is an instance of `J-refl`)
    to-fro q = {!!}

    fro-to : isRetract to fro
--  Exercise: (Hint: use `J` again!)
    fro-to f = {!!}
```

When the type family used in ``J`` ignores the path, then we recover
exactly the ``subst`` operation that we started with.

```
subst-from-J : (B : A → Type ℓ) → (p : x ≡ y) → B x → B y
subst-from-J B p b = J (λ y _ → B y) b p

_ = λ {ℓ : Level} (A : Type ℓ) (B : A → Type ℓ) (x y : A) (p : x ≡ y)
  → test-identical (subst-from-J B p) (subst B p)
```

There's a very subtle point here that is worth mentioning. In the
above definition, we used ``J`` to define an element of `B y` given
that we already had an element `b : B x`. But we could also have used
``J`` to define the function `B x → B y` in its entirety.

```
subst-from-J' : (B : A → Type ℓ) → (p : x ≡ y) → (B x → B y)
subst-from-J' {x = x} B p = J (λ y p → B x → B y) idfun p
```

Why does this work? Well, we have to produce a function `B x → B y`
when `y` is in fact the same as `x`, but this is easy: we have
``idfun``. This ``subst-from-J'`` is no longer *exactly* the same as
``subst``, but we can still prove them to be the same using ``J`` and
``J-refl``.


## Applications of J

The ``J`` principle is exceptionally powerful, much more powerful than
it might appear. In fact, in the bare Martin-Löf theory on which
Cubical Type Theory is based, the ``J`` rule is taken as one of the
defining properties of equality.

```
sym-from-J : {x y : A} → (x ≡ y) → (y ≡ x)
sym-from-J {x = x} p = J (λ z _ → z ≡ x) refl p
```

Try reconstructing ``ap`` using ``J``:

```
ap-from-J : (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
-- Exercise:
ap-from-J f {x} p = {!!}
```

::: Caution:
These are perfectly valid ways to define ``sym`` and ``ap`, but they
are is not identical to the functions we have already:

```
-- Fails!
-- _ = λ {A : Type} {x y : A} (p : x ≡ y)
--   → test-identical (sym-from-J p) (sym p)
```

Our existing ``sym`` and ``ap`` have much better computational
properties, so you should continue to use them rather than these ones
defined from ``J``.
:::

More interestingly, we can also get operations we haven't encountered
yet:

```
comp-from-J : {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
comp-from-J {x = x} p q = J (λ z _ → x ≡ z) p q
```

In these examples, we haven't yet used the path parameter of the type
family `Q`. This often comes up when proving properties of
constructions that have themselves involved ``J``.

```
sym-inv-from-J : {x y : A} → (p : x ≡ y) → sym-from-J (sym-from-J p) ≡ p
sym-inv-from-J {x = x} {y} p
  = J (λ z q → sym-from-J (sym-from-J q) ≡ q) refl-case p
  where
    refl-case : sym-from-J (sym-from-J refl) ≡ refl
    refl-case = comp-from-J (ap sym-from-J (J-refl (λ z _ → z ≡ x) refl))
                            (J-refl (λ z _ → z ≡ x) refl)
```

As we've said, it is possible to continue down this road and do all of
Homotopy Type Theory relying solely on the ``J``-rule. But working in
the cubical style has significant advantages: far more equations hold
automatically rather than having to be proved by hand. We've just seen
an example of this: in ``sym-inv-from-J`` we've had to do a lot more
work to show what in ``symP-inv`` was immediate. In the next Lecture
we'll see the more cubical approach to composition of paths, and
similar operations.


## Paths in Bool

One lingering question is what we get if we look at paths in the
inductive types we have seen so far (``⊤``, ``∅``, ``Bool``, ``ℕ`` and
``⊎``). There is a general way these constructions go for inductive
types known as the "encode-decode" method, which is due to Dan Licata.

Let's take ``Bool`` as our first example. We already have a candidate
for what paths in ``Bool`` should be, that is, ``≡Bool``. We'll call
this type the `code` for paths in ``Bool``. Our plan is to show that
the type `x ≡ y` is equivalent to `code x y` by giving explicit
encoding and decoding functions.

```
≡≃≡Bool : (x y : Bool) → (x ≡ y) ≃ (x ≡Bool y)
≡≃≡Bool x y = inv→equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : Bool → Bool → Type
    code x y = x ≡Bool y
```

We need an `encode` function that takes paths in ``Bool`` to codes, in
this case, elements of ``≡Bool``. It is easy to come up with codes
that should correspond to the reflexivity paths:

```
    encode-refl : (x : Bool) → code x x
    encode-refl true = tt
    encode-refl false = tt
```

It's not strange that ``false`` is sent to ``tt``: remember
that `encode-refl false` is supposed to encode the fact that `false ≡
false`, and this is certainly true!

And now the ``J`` rule allows us to extend this to all
paths. Specifically, we use ``J`` for the type family `code x :
(y : Bool) → Type`.

```
    encode : (x y : Bool) → x ≡ y → code x y
    encode x y = J (λ z _ → code x z) (encode-refl x)
```

Similarly, we need a ``decode`` function that turns codes back
into ordinary paths. Looking at `x ≡Bool y`, once we split `x` and `y`
into cases we know exactly the type is and can act accordingly. Either
the endpoints are the same, in which case we have ``refl``, or
the endpoints are different, in which case `x ≡Bool y` is ``∅``
and we have a contradiction.

```
    decode : (x y : Bool) → code x y → x ≡ y
    decode true true _ = refl
    decode true false e = ∅-rec e
    decode false true e = ∅-rec e
    decode false false _ = refl
```

That this is a section is similar, after splitting into cases it's
easy:

```
    to-fro : (x y : Bool) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro x y p = {!!}
```

For the retract, we plan to use ``J`` again, so we just have to check
the retract property for ``refl``.

```
    fro-to-refl : (x : Bool) → decode x x (encode x x refl) ≡ refl
    fro-to-refl true = refl
    fro-to-refl false = refl
```

And the ``J`` rule is exactly what is required to extend this to
all paths.

```
    fro-to : (x y : Bool) → isRetract (encode x y) (decode x y)
    fro-to x y = J (λ z p → decode x z (encode x z p) ≡ p) (fro-to-refl x)
```

This completes the equivalence!


## The Encode-Decode Method

This encode-decode trick is one that comes up often when
characterising the paths in a type. The goal is to describe the type
of paths `x ≡ y` by finding an equivalent type `code x y` that is
easier to work with.

Proofs of this kind have a similar shape. Let's summarise what we did,
noting what was unique to ``Bool`` and what we can re-use for an
arbitrary type.

<!--
```
module EncodePattern
  (X : Type)
  (code : X → X → Type)
  (encode-refl : (x : X) → code x x)
  (decode : (x y : X) → code x y → x ≡ y)
  (fro-to-refl : (x : X) → decode x x (subst (λ z → code x z) refl (encode-refl x)) ≡ refl)
  where
```
-->

We start with a type `X` with the goal of characterising paths `x ≡ y`
in `X`. We make a guess at the answer as a type family

    code : X → X → Type

with the idea that `code x y` will be equivalent to `x ≡ y`. Choosing
`code` will involve some creativity or luck, but it can usually be
intuited from the definition of `X`. As a rule of thumb, the path
types of inductive types should also be describable as inductive types
themselves; it is helpful if `code` is an inductive type so that it is
easy to define functions out of it.

For our guess to pass the smell test, we should at least be able to
define a function corresponding to reflexivity.

    encode-refl : (x : X) → code x x

With this in hand, we can always make the definition

```
  encode : (x y : X) → x ≡ y → code x y
  encode x y p = J (λ z _ → code x z) (encode-refl x) p
```

Next we need a decoding map. So long as we choose ``code`` so that it
has a nice mapping-out property --- for example, when it is an
inductive type --- this should be easy.

    decode : (x y : X) → code x y → x ≡ y

The proof that this is a section should be similarly easy, because it
also involves mapping out of ``code``.

    to-fro : (x y : X) → isSection (encode x y) (decode x y)

All that remains is to prove that it is also a retract. In this case,
we need a function with type `(x y : X) → decode x y (encode x y p) ≡
p`. When `p` is ``refl``, so we are aiming to construct `fro-to-refl :
(x y : X) → decode x y (encode x y p) ≡ p`, this is easy, because
``encode`` was defined in terms of ``encode-refl``. The ``J`` rule
extends this to a general path.

```
  fro-to : (x y : X) → isRetract (encode x y) (decode x y)
  fro-to x y = J (λ c p → decode x c (encode x c p) ≡ p) (fro-to-refl x)
```


## More Encode-Decode

Try characterising the paths in ``⊤``. This should essentially be
the same as the proof for ``Bool`` but with half of the cases
deleted.

```
≡≃≡⊤ : (x y : ⊤) → (x ≡ y) ≃ ⊤
≡≃≡⊤ x y = inv→equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : ⊤ → ⊤ → Type
    code x y = ⊤

    encode-refl : (x : ⊤) → code x x
    -- Exercise:
    encode-refl x = {!!}

    encode : (x y : ⊤) → x ≡ y → code x y
    encode x y p = J (λ z _ → code x z) (encode-refl x) p

    decode : (x y : ⊤) → code x y → x ≡ y
    -- Exercise:
    decode x y c = {!!}

    to-fro : (x y : ⊤) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro x y c = {!!}

    fro-to-refl : (x : ⊤) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    fro-to-refl x = {!!}

    fro-to : (x y : ⊤) → isRetract (encode x y) (decode x y)
    fro-to x y p = J (λ c p → decode x c (encode x c p) ≡ p) (fro-to-refl x) p
```

::: Aside:
In `code` above, we *don't* case-split on `x` and `y`, because we want
to show that `(x ≡ y) ≃ ⊤` regardless of what `x` and `y` are. If we
case split and write `code tt tt = ⊤` then the types no longer line
up, because Agda doesn't automatically know that every element of ``⊤``
is ``tt``.
:::

For ``ℕ``, we already have a candidate for `code`: observational
equality ``≡ℕ``.

```
≡≃≡ℕ : (x y : ℕ) → (x ≡ y) ≃ (x ≡ℕ y)
≡≃≡ℕ x y = inv→equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : ℕ → ℕ → Type
    code x y = x ≡ℕ y

    encode-refl : (x : ℕ) → code x x
    -- Exercise:
    encode-refl x = {!!}

    encode : (x y : ℕ) → x ≡ y → code x y
    encode x y p = J (λ z _ → code x z) (encode-refl x) p

    decode : (x y : ℕ) → code x y → x ≡ y
    -- Exercise:
    decode x y c = {!!}

    to-fro : (x y : ℕ) → isSection (encode x y) (decode x y)
    -- Exercise:
    to-fro x y p = {!!}

    fro-to-refl : (x : ℕ) → decode x x (encode x x refl) ≡ refl
    -- Exercise:
    fro-to-refl x = {!!}

    fro-to : (x y : ℕ) → isRetract (encode x y) (decode x y)
    fro-to x y p = J (λ z q → decode x z (encode x z q) ≡ q) (fro-to-refl x) p
```

Next, disjoint unions. We didn't define a candidate ``≡⊎`` for the
paths to be equal to back in Lecture 1-5 as we did with the others,
but it's not hard to guess what it should be. After all, the two sides
are supposed to be *disjoint*, so paths between ``inl``s should be
exactly paths in the left type, paths between ``inr``s should be
exactly paths in the right type, and there should be no paths at all
between ``inl``s and ``inr``s.

```
_≡⊎_ : {A B : Type} (x y : A ⊎ B) → Type
inl a1 ≡⊎ inl a2 = a1 ≡ a2
inl a  ≡⊎ inr b  = ∅
inr b  ≡⊎ inl a  = ∅
inr b1 ≡⊎ inr b2 = b1 ≡ b2
```

::: Aside:
This is not the most general definition of ``≡⊎`` we could use: notice
that this only handles types `A` and `B` in the lowest universe. To do
this right, we would have to land in `Type (ℓ-max ℓ ℓ')`, and ``Lift``
each right-hand side to that level. This doesn't change anything important
about the encode-decode proof, so we omit it here to cut down on
noise.
:::

For this particular proof, it is more convenient to define `encode`
manually by pattern matching, rather than using ``J``.

```
≡≃≡⊎ : (x y : A ⊎ B) → (x ≡ y) ≃ (x ≡⊎ y)
≡≃≡⊎ {A = A} {B = B} x y = inv→equiv (encode x y) (decode x y) (to-fro x y) (fro-to x y)
  where
    code : (x y : A ⊎ B) → Type
    code x y = x ≡⊎ y

    encode : (x y : A ⊎ B) → x ≡ y → code x y
    encode (inl _) (inl _) = inl-inj
    encode (inl _) (inr _) = inl≢inr
    encode (inr _) (inl _) = inr≢inl
    encode (inr _) (inr _) = inr-inj

    decode : (x y : A ⊎ B) → code x y → x ≡ y
--  Exercise:
    decode x y = {!!}

    to-fro : (x y : A ⊎ B) → isSection (encode x y) (decode x y)
--  Exercise:
    to-fro x y = {!!}

    fro-to-refl : (x : A ⊎ B) → decode x x (encode x x refl) ≡ refl
--  Exercise:
    fro-to-refl x = {!!}

    fro-to : (x y : A ⊎ B) → isRetract (encode x y) (decode x y)
--  Exercise:
    fro-to x y = {!!}
```

Finally, ``List``s. Try this from scratch yourself, using ``ℕ`` and
``⊎`` as a model.

```
_≡List_ : List A → List A → Type ℓ-zero
-- Exercise:
xs ≡List ys = {!!}

≡≃≡List : (xs ys : List A) → (xs ≡ ys) ≃ (xs ≡List ys)
-- Exercise:
≡≃≡List {A = A} xs ys = {!!}
```

## References and Further Reading


* The original *[Homotopy Type Theory]* book:
  * Encode-Decode for disjoint unions: Chapter 2.12
  * Encode-Decode for natural numbers: Chapter 2.13
  * Encode-Decode Generally: Chapter 8.9
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Encode-Decode, presented in the guise of the "fundamental theorem
    of identity types": Chapter 11

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082

* Agda Documentation
  * [Partial elements](https://agda.readthedocs.io/en/latest/language/cubical.html#partial-elements)


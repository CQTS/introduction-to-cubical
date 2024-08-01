```
module 1--Type-Theory.1-4--Propositions-as-Types where
```

# Lecture 1-4: Propositions as Types

<!--
```
open import Library.Prelude hiding (_+_; _·_)
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
```
-->

In the last lecture, we saw how to define some familiar data types
--- Booleans, natural numbers, integers --- and how to define some of
their familiar operations. But to do mathematics, we need to be able
to prove things about these types and their operations.

A proposition, informally speaking, is a mathematical statement for
which we know what would constitute a proof. To prove that a number
`n` is even, for example, we could divide it evenly in two; this would
suffice to prove that the number is even, so the statement "`n` is
even" is a proposition: we know what it would mean to prove it.

In this lecture, we will give a first pass at a type theoretic
formalization of the notion of propositions.

One way to formalize a proposition is as a function to the Booleans.
We've already seen several of these, like ``isEven``,
``isLeft``, and so on. If `P : A → Bool` is one of these
functions, then we think of it as describing the proposition that "the
Boolean value `P a` equals `true`".

This way of representing propositions is common in other programming
languages. But there is another, more powerful way of formalizing
propositions which is made possible by dependent types: we think of
types as themselves expressing propositions.


## Propositions as Types

The core of the idea is that a proposition will be encoded as a type
type, and to prove the proposition is to give an element of that type.

First, have type versions of ``true`` and ``false``.

```
TrueP : Type
TrueP = ⊤

FalseP : Type
FalseP = ∅
```

The type ``⊤`` has an element ``tt``; under the
interpretation that proofs of propositions are the elements of the
types representing those propositions, this means we can prove that
``TrueP`` holds. On the other hand, ``∅`` has no elements by
definition. Therefore, we can't prove that ``FalseP`` holds ---
at least, not without assuming some contradictory hypotheses.

We can turn each Boolean value into its corresponding type:

```
IsTrue : Bool → Type
IsTrue true  = TrueP
IsTrue false = FalseP
```

An amazing feature of propositions-as-types idea is that the
operations on types we have seen in the last few lectures become
familiar operations on propositions.

In ordinary logic, to prove `P and Q` we need to prove `P` and to
prove `Q`. That is, a proof of `P and Q` consists of a pair of proofs,
one for `P` and one for `Q`. We can turn this directly into a
definition.

```
_andP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P andP Q = P × Q
```

Now consider implication. Implication means that, assuming you have a
proof of `P`, you can get a proof of `Q`. This is exactly what
functions do, so we can also turn this into a definition:

```
_impliesP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P impliesP Q = P → Q
```

Once we have these as building blocks, we can start to construct other
logical operations. When two propositions imply each other, this is
known as "logical equivalence":

```
_iffP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P iffP Q = (P → Q) × (Q → P)
```

We can prove that these operations on types correspond correctly with
the operations on Booleans, via ``IsTrue``. Prove the following
by case splitting on the arguments and filling in both sides of the
logical equivalence. On the left of the ``iffP`` we use the
ordinary operation on Booleans, and on the right we use the
corresponding operation on propositions-as-types.

```
and→Type : (a b : Bool) → (IsTrue (a and b)) iffP ((IsTrue a) × (IsTrue b))
-- Exercise:
and→Type a b = {!!}

implies→Type : (a b : Bool) → (IsTrue (a implies b)) iffP ((IsTrue a) → (IsTrue b))
-- Exercise:
implies→Type a b = {!!}
```

Negation can be seen as a special case of implication: "not P" is the
same as "P implies false", and again we make this our definition.

```
¬_ : {ℓ : Level} → Type ℓ → Type ℓ
¬_ P = P → ∅

-- This makes `¬` go on the outside of most formulas
infix 3 ¬_
```

We had better also make sure this means what we think it does!

```
not→Type : (a : Bool) → (IsTrue (not a)) iffP (¬ IsTrue a)
-- Exercise:
not→Type a = ?
```

A basic principle of negation is contraposition: if `P` implies `Q`
then whenever `Q` is false, certainly `P` must be false too.

This gives us an opportunity to introduce another useful Agda hotkey.
If you place your cursor in the below hole and press `C-c C-,`, Agda
will tell you that the goal has type `¬ Q → ¬ P`. This is certainly
true, but the path forwards is a little obscured. It helps if we
*unfold* the definition of ``¬`` in the goal, which we can ask
Agda to do by pressing `C-u C-u C-c C-,` in Emacs, or `C-y C-,` in
VSCode.

It is revealed that the goal has type `(Q → ∅) → P → ∅`. This makes it
clear that ``¬contra`` should take two arguments, one with type
`Q → ∅`, and the other with type `P`.

```
¬-contra : {ℓ ℓ' : Level} → {P : Type ℓ} → {Q : Type ℓ'}
        → (P → Q)
        → (¬ Q → ¬ P)
-- Exercise:
¬-contra f = {!!}
```

The logic of the propositions-as-types is not exactly the same as the
logic of Booleans, however. The reason has to do with double negation:
recall that for the Booleans, `not not b` is always equal to `b` which
you can check by just trying both possibilities. Working with
propositions-as-types, we can show one direction of that equivalence:

```
implies¬¬ : {ℓ : Level} → {P : Type ℓ} → (P → (¬ ¬ P))
-- Exercise:
implies¬¬ p = ?
```

But, we cannot show that `¬ ¬ A → A` in general!

```
-- Uncomment to try if you want!
-- impossible-¬¬implies : {ℓ : Level} (P : Type ℓ) → (¬ ¬ P) → P
-- impossible-¬¬implies P nnp = {!!}
```

One way to understand the difference between `¬ ¬ P` and `P` is that
we think of `p : P` as giving *evidence* that the proposition `P`
holds. What `¬ ¬ P` says is that to assume `P` were false would be
false, but this does not on its own conjure any evidence for `P`. This
quirk of logic in type theory makes it a "constructive" logic ---
there is a difference between providing (or "constructing") evidence
for a proposition and proving that its falsehood would be absurd ---
as opposed to the "classical" logic of the Booleans.

It seems that we're at risk of `¬`s piling up endlessly if the above
implication only works in one direction. But in fact, as soon as we
have three `¬`s, we can cancel two of them.

```
¬¬¬implies¬ : {ℓ : Level} → {P : Type ℓ} → (¬ ¬ ¬ P) → (¬ P)
-- Exercise:
¬¬¬implies¬ nnnp = ?
```

As a challenge, prove that it's impossible for `P` and `¬ P` to be
logically equivalence. Again, it may help to see what to do next if
you unfold the definitions.

```
¬-not-same : {ℓ : Level} → {P : Type ℓ} → ¬ (P iffP (¬ P))
-- Exercise: 
¬-not-same (l , r) = ?
```


## Or

This pattern of relating logical operations to type operations
continues with ``or``, but runs into a subtle hiccup. Our attempt
at a type avatar of ``or`` is ``⊎``, the disjoint union.
This makes some sense: to prove `P or Q` should consist of either a
proof of `P` or a proof of `Q`.

First, let's define maps both ways.

```
or→Type-fro : (a b : Bool) → ((IsTrue a) ⊎ (IsTrue b)) → IsTrue (a or b)
-- Exercise:
or→Type-fro a b p = {!!}

or→Type-to : (a b : Bool) → IsTrue (a or b) → ((IsTrue a) ⊎ (IsTrue b))
-- Exercise:
or→Type-to a b p = {!!}
```

What this shows is that `IsTrue (a or b)` and `(IsTrue a) ⊎ (IsTrue b)`
are logically equivalent, that is, one ``iffP`` the other. But
now: define the map backwards again, but making the opposite choice in
the case `or→Type-to' true true`.

```
or→Type-to' : (a b : Bool) → IsTrue (a or b) → ((IsTrue a) ⊎ (IsTrue b))
-- Exercise:
or→Type-to' a b p = {!!}
```

So having an element of `(IsTrue a) ⊎ (IsTrue b)`, is *more*
information than just knowing that at least one of `a` or `b` is true:
if *both* `a` and `b` are true, the element of `(IsTrue a) ⊎ (IsTrue b)`
still makes a choice between the two sides. So, the type no longer
merely expresses the truth of a proposition.

What we ought to learn from this is that not *every* type should be
thought of as a proposition. Some types, like ``ℕ``, say, are
better thought of as sets that have many different elements. What we
are noticing with ``or`` is that the disjoint union of two
propositions can be a non-trivial data type. We actually saw this
earlier, when we proved that ``Bool`` is bijective with `⊤ ⊎ ⊤`.

In a later lecture (mvrnote: link) we will make a definition that
exactly picks out which types are the ones we should think of as
propositions: types that have at most one element. This unique
element, if it exists at all, is thought of as "the fact that the
proposition is true". At that point we will also properly define the
operation which corresponds to the proposition `P or Q`.

Nevertheless, ``⊎`` is close enough to ``or`` for our
current purposes. Try proving De Morgan's laws, which may be
familiar from ordinary propositional logic. For the last one, we get
stuck in a similar way to `impossible-¬¬implies` above. In that case,
how are we suppoesd to know which of ``inl`` or ``inr`` to
pick?

```
DeMorgan-law-1 : {P Q : Type} → ¬ (P ⊎ Q) → (¬ P) × (¬ Q)
DeMorgan-law-1 npq = (λ p → npq (inl p)) , (λ q → npq (inr q))

DeMorgan-law-2 : {P Q : Type} → (¬ P) × (¬ Q) → ¬ (P ⊎ Q)
DeMorgan-law-2 (np , nq) (inl p) = np p
DeMorgan-law-2 (np , nq) (inr q) = nq q

DeMorgan-law-3 : {P Q : Type} → (¬ P) ⊎ (¬ Q) → ¬ (P × Q)
DeMorgan-law-3 (inl np) (p , q) = np p
DeMorgan-law-3 (inr nq) (p , q) = nq q

-- Uncomment to see where you get stuck if you want!
-- impossible-DeMorgan-law-4 : {P Q : Type} → ¬ (P × Q) → (¬ P) ⊎ (¬ Q)
-- impossible-DeMorgan-law-4 npq = {!!}
```


## Equality

The most fundamental proposition concerning the data types we have
seen so far is *equality*. We can define equality for Booleans
by case-splitting as follows:

```
_≡Bool_ : (a b : Bool) → Type
true ≡Bool true = ⊤
true ≡Bool false = ∅
false ≡Bool true = ∅
false ≡Bool false = ⊤
```

That is, there is a unique proof that `true ≡Bool true`, no proofs
that `true ≡Bool false`, and so on. This kind of equality defined by
pattern-matching is often called "observational equality".

Now how do we prove an equality of ``Bool``s? We just inhabit the
relevant type:

```
true-is-true : true ≡Bool true
true-is-true = tt
```

What if the Boolean value involved is a variable, or some complicated
expression? By case splitting, we can hopefully simplify the goal into
one of the trivial cases as above, that is, we just do recursion on
the data type! (Using recursion to prove a proposition is often called
"induction", we will make this more precise in the next section.)

Using recursion we can prove that observational equality is a
reflexive, symmetric, and transitive relation on Booleans.

```
≡Bool-refl : (a : Bool) → a ≡Bool a
-- Exercise:
≡Bool-refl a = {!!}

≡Bool-sym : (a b : Bool)
  → a ≡Bool b
  → b ≡Bool a
-- Exercise:
≡Bool-sym a b p = {!!}

≡Bool-trans : (a b c : Bool)
  → a ≡Bool b
  → b ≡Bool c
  → a ≡Bool c
-- Exercise:
≡Bool-trans a b c p q = {!!}
```

We can also show that all of our logical operations preserve the
relation of equality, as expected. Like the previous, these can be
proven purely by splitting into all the possible cases, so we won't
make you do them all.

```
not-≡Bool : (a b : Bool)
  → a ≡Bool b
  → (not a) ≡Bool (not b)
-- Exercise:
not-≡Bool a b p = {!!}

and-≡Bool : (a1 a2 b1 b2 : Bool)
  → (a1 ≡Bool a2)
  → (b1 ≡Bool b2)
  → (a1 and b1) ≡Bool (a2 and b2)
-- Exercise:
and-≡Bool a1 a2 b1 b2 p q = {!!}
```

We can similarly define equality of natural numbers.

```
_≡ℕ_ : (n m : ℕ) → Type
-- Exercise:
n ≡ℕ m = ?
```

And show that it is a reflexive, symmetric, and transitive relation.
The difference in the proofs is that, because ``ℕ`` is a
recursive datatype, some cases in our proofs will need to be recursive
too.

```
≡ℕ-refl : (n : ℕ) → n ≡ℕ n
-- Exercise:
≡ℕ-refl n = ?

≡ℕ-sym : (n m : ℕ)
  → n ≡ℕ m
  → m ≡ℕ n
-- Exercise:
≡ℕ-sym n m p = ?

≡ℕ-trans : (n m k : ℕ)
  → n ≡ℕ m
  → m ≡ℕ k
  → n ≡ℕ k
-- Exercise:
≡ℕ-trans n m k p q = {!!}
```

We can also show that all of the arithmetic operations preserve the
equality.

```
+-≡ℕ : (n1 n2 m1 m2 : ℕ)
  → n1 ≡ℕ n2
  → m1 ≡ℕ m2
  → (n1 +ℕ m1) ≡ℕ (n2 +ℕ m2)
-- Exercise:
+-≡ℕ n1 n2 m1 m2 p q = {!!}
```

Next, we can show that addition is unital (that is, has an identity
element), and associative. These are all very easy by recursion.
Remember that you don't *have* to case split on an argument just
because you can, ``≡ℕ-assoc`` is much simpler if you don't!

```
≡ℕ-unitl : (n : ℕ) → n ≡ℕ (zero +ℕ n)
-- Exercise:
≡ℕ-unitl n = {!!}

≡ℕ-unitr : (n : ℕ) → n ≡ℕ (n +ℕ zero)
-- Exercise:
≡ℕ-unitr n = {!!}

≡ℕ-assoc : (n m k : ℕ) → (n +ℕ (m +ℕ k)) ≡ℕ ((n +ℕ m) +ℕ k)
-- Exercise:
≡ℕ-assoc n m k = {!!}
```

Finally, we can show that addition is commutative. This one is
trickier, and we will have to glue together some of the facts we
proved above. In both parts, it is easiest if you pattern match on the
argument `n` but *not* on the argument `m`!

```
≡ℕ-comm-helper : (n m : ℕ) → suc (n +ℕ m) ≡ℕ (n +ℕ suc m)
-- Exercise:
≡ℕ-comm-helper n m = {!!}

≡ℕ-comm : (n m : ℕ) → (n +ℕ m) ≡ℕ (m +ℕ n)
-- Exercise:
≡ℕ-comm n m = {!!}
```

It would be tedious if we had to define the specific notion of
equality we wanted for every type that we ever define. It's also not
entirely exactly how to do it in more difficult cases.

For example, to say that elements in the disjoint union `A ⊎ B` are
equal, we would want to say that if `a = a'` then `inl a = inl a'` and
if `b = b'` then `inr b = inr b'` and that it is never the case that
`inl a = inr b` or vice versa (since the union is disjoint). But
without knowing specifically what the types `A` and `B` are, we
wouldn't know what equality meant for them.

Remarkably, it is possible to give a uniform notion of "equality" for
any type --- this is the subject of Part 2 of these notes. But, as
we'll see shortly, this general notion of *paths* between of elements
of general types will not always be a proposition --- paths will often
be interesting pieces of data in their own right.

Before we go on, let's see one more proposition defined by
case-splitting: the ordering of natural numbers. mvrnote: does this
get used? did we put this in for Fin eventually?

```
_≤ℕ_ : (n m : ℕ) → Type
zero ≤ℕ m = ⊤
suc n ≤ℕ zero = ∅
suc n ≤ℕ suc m = n ≤ℕ m

-- data _≤ℕ_ : (n m : ℕ) → Type₀ where
--   zero-≤ : (m : ℕ) → zero ≤ℕ m
--   suc-≤  : (n m : ℕ) → n ≤ℕ m → (suc n) ≤ℕ (suc m)

≤ℕ-refl : (n : ℕ) → n ≤ℕ n
-- Exercise:
≤ℕ-refl n = {!!}

≤ℕ-trans : (n m k : ℕ) (p : n ≤ℕ m) (q : m ≤ℕ k) → n ≤ℕ k
-- Exercise:
≤ℕ-trans n m k p q = {!!}

≤ℕ-antisym : (n m : ℕ) (p : n ≤ℕ m) (q : m ≤ℕ n) → n ≡ℕ m
-- Exercise:
≤ℕ-antisym n m p q = {!!}
```


## Induction Principles

In the above we proofs we were secretly using an upgraded form of
recursion principles known as "induction principles". The difference
is that where recursion principles allowed us to define ordinary
functions out of ``Bool``, ``ℕ``, etc., induction principles
allow us to define *dependent* functions out of these types, into a
type family of our choice.

``Bool`` is the easiest. Here a type family `C : Bool → Type ℓ`,
simply picks out two (possibly different) types, `C true` and `C false`.
Now, we just upgrade the recursion principle so that we use one element of
each of these types, rather than two elements of the same type:

```
Bool-ind : {ℓ : Level} {C : Bool → Type ℓ}
         → C true
         → C false
         → ((x : Bool) → C x)
-- Exercise:
Bool-ind c₁ c₂ x = {!!}
```

The recursion principle for `A ⊎ B` is upgraded to an induction
principle in a similar way. For the recursion principle, the inputs
were maps `A → C` and `B → C`. If `C` is now a type dependent on `A ⊎
B`, these maps have to land in `C x`, where `x : A ⊎ B`. Luckily,
there are obvious candidates for `x` in both cases: take the ``inl`` or
``inr`` of the input `a : A` or `b : B` respectively.

```
⊎-ind : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
      → ((a : A) → C (inl a))
      → ((b : B) → C (inr b))
      → (x : A ⊎ B) → C x
-- Exercise:
⊎-ind cinl cinr x = {!!}
```

``ℕ`` is a little trickier. It is best to think of ordinary
mathematical induction, and consider `C` to be some property of the
natural numbers we are trying to check. Then the two inputs make
sense: we first have the base case of type `C zero`, claiming that the
property `C` holds for ``zero``. Then we have the inductive step
for ``suc``: saying that, for any `n : ℕ`, if we can prove `C`
holds for `n` then it also holds for `suc n`.

If we can provide both of those things, then we get a function from
`(n : ℕ) → C n`, meaning that `C` holds for every `n`.

```
ℕ-ind : {ℓ : Level} {C : ℕ → Type ℓ}
         → (z : C zero)
         → (r : (n : ℕ) → C n → C (suc n))
         → ((n : ℕ) → C n)
-- Exercise:
ℕ-ind z r n = ?
```

As before, we don't often need to use ``Bool-ind``,
``⊎-ind`` or ``ℕ-ind``; we can instead use the
pattern-matching features of Agda directly.


## Quantifiers

One thing we are still missing from ordinary logic is *quantifiers*,
that is, the propositions `forall x. P(x)` and `exists x. P(x)`, where
`P` is now a predicate on values `x`. For our purposes here, we will
consider any type family `A → Type` as expressing a predicate on
elements of `A`.

For example, the predicate on natural numbers that identifies when the
natural number is ``zero``.

```
isZeroP : ℕ → Type
isZeroP zero = ⊤
isZeroP (suc n) = ∅
```

In cases like this where we already have a map into ``Bool``, we
can turn it into a predicate by applying ``IsTrue``.

```
isEvenP : ℕ → Type
isEvenP n = IsTrue (isEven n)

isOddP : ℕ → Type
isOddP n = IsTrue (isOdd n)
```

We can combine these predicates using the operations we've already
seen, for example, we can form the predicate on natural numbers `n`
that the number `n` is even or odd.

```
evenOrOdd : (n : ℕ) → Type
evenOrOdd n = isEvenP n ⊎ isOddP n
```

Of course this should be true for *every* element `n`. The proposition
`forall n. P(n)` is represented by a dependent function from natural
numbers `n` to proofs that `evenOrOdd n` holds.

```
∀evenOrOdd : (n : ℕ) → evenOrOdd n
-- Exercise:
∀evenOrOdd n = {!!}
```

Try another simple case:

```
zeroImpliesEven : (n : ℕ) → (isZeroP n) → (isEvenP n)
-- Exercise:
zeroImpliesEven n = {!!}
```

For the proposition `exists n. P(n)`, the obvious thing to try is a
dependent pair: that is, a proof of `exists n. P(n)` should be an
actual example of an `n`, together with a proof that `P(n)` holds. So,
we might represent the proposition that there exists an even number
as:

```
Even : Σ[ n ∈ ℕ ] isEvenP n
Even = 2 , tt
```

This interpretation of `exists` is not quite right for similar reasons
as to `⊎`. After all, there are lots of different even numbers that we
can use to inhabit the above type, and so the type represents more
information than the mere proposition that an even number exists: it
comes with a choice of one. Again we will fix this in Part 2.

For the following two, you should remember that ``¬`` is simply
functions into ``∅``. Once you unfold that definition, the below
exercises are *exactly* two functions that we have seen before.

```
¬Σ→forall¬ : {A : Type} {B : A → Type}
  → ¬ (Σ[ a ∈ A ] B a) → (a : A) → ¬ B a
-- Exercise:
¬Σ→forall¬ = ?

forall¬→¬Σ : {A : Type} {B : A → Type}
  → ((a : A) → ¬ B a) → ¬ (Σ[ a ∈ A ] B a)
-- Exercise:
forall¬→¬Σ = ?
```


## Decidable Types

There is another crucial place where constructive logic differs from
classical logic: the Law of Excluded Middle. This is the completely
intuitive statement that for any proposition `P`, either `P` or `not
P`.

And yet, you will have a hard time proving the following!

```
-- Uncomment to try if you want!
-- impossible-LEM : {ℓ : Level} (P : Type ℓ) → (¬ P) ⊎ P
-- impossible-LEM = {!!}
```

and in fact, the two impossible problems in this file are related: as
soon as you can solve one, you can solve the other.

```
-- Suppose you have `LEM` for `P`, then:
LEM→¬¬implies : {ℓ : Level} {P : Type ℓ}
              → ((¬ P) ⊎ P)
              → (¬ ¬ P → P)
-- Exercise:
LEM→¬¬implies p = {!!}

-- We almost have LEM for any particular `P`:
¬¬LEM : {ℓ : Level} {P : Type ℓ} → ¬ ¬ ((¬ P) ⊎ P)
-- Exercise:
¬¬LEM x = {!!}

-- Suppose you have `¬¬implies` for `(¬ P) ⊎ P`, then:
¬¬implies→LEM : {ℓ : Level} {P : Type ℓ}
              → (¬ ¬ ((¬ P) ⊎ P) → (¬ P) ⊎ P)
              → ((¬ P) ⊎ P)
-- Exercise:
¬¬implies→LEM f = {!!}
```

So if we have a generic proposition `P`, we cannot split into into
cases for whether `P` holds or not this: would be saying that we
always have an element of `P ⊎ ¬ P` telling us whether a proposition
is true.

For some specific types though, we can show that `P ⊎ ¬ P`: we call
such types "decidable". The following type is essentally identical to
the type `P ⊎ ¬ P` but, we define a new type so we can give it more
meaningful constructor names.

```
data Dec {ℓ : Level} (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

Here are the simplest examples:
```
Dec⊤ : Dec ⊤
-- Exercise:
Dec⊤ = {!!}

Dec∅ : Dec ∅
-- Exercise:
Dec∅ = {!!}
```

Predicates defined on data types are often decidable, because we built
them out of ``⊤`` and ``∅``.

```
Dec-isEvenP : (n : ℕ) → Dec (isEvenP n)
-- Exercise:
Dec-isEvenP n = {!!}
```

In particular, observational equality of booleans and natural numbers
is decidable. Just pattern-match and observe whether or not they are
equal!

```
Dec-≡Bool : (a b : Bool) → Dec (a ≡Bool b)
-- Exercise:
Dec-≡Bool a b = {!!}

Dec-≡ℕ : (a b : ℕ) → Dec (a ≡ℕ b)
-- Exercise:
Dec-≡ℕ a b = {!!}
```

We further discuss constructive mathematics and its limits in the
extras file (mvrnote: link) Lecture 1-XE: Constructive Logic.

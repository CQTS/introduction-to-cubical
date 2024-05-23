```
module 1--Type-Theory.1-3--Propositions-as-Types where
```

# Lecture 1-3: Propositions as Types

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
```
-->

In the last lecture, we saw how to define some familiar data types
--- Booleans, natural numbers, integers --- and how to define some of
their familiar operations. But to do mathematics, we need to prove
facts about these types and their operations.

A proposition, informally speaking, is a mathematical statement for
which we know what would constitute a proof. To prove that a number
`n` is even, for example, we could divide it evenly in two; this would
suffice to prove that the number is even, so the statement "`n` is
even" is a proposition: we know what it would mean to prove it.

In this lecture, we will give a first pass at a type theoretic
formalization of the notion of propositions. One way to formalize a
proposition is as a function to the Booleans. If `P : A → Bool` is
such a function, then we think of it as describing the proposition
that "`P a` equals `true`". Here is a definition of the proposition
that a number is even, defined together with the proposition that a
number is odd:

```
isEven : ℕ → Bool
isOdd  : ℕ → Bool

isEven zero = true
isEven (suc n) = isOdd n

isOdd zero = false
isOdd (suc n) = isEven n
```

Try writing a proposition to represent whether a natural number is
`zero`{.Agda}.

```
isZero : ℕ → Bool
-- Exercise:
isZero n = {!!}
```

This way of representing propositions is most common in programming
languages without dependent types. But there is another very powerful
way of formalizing propositions possible with dependent types. We can
think of some types as themselves expressing propositions. This idea
is known as "propositions as types".

Propositions as Types

The idea of "propositions as types" is that a proposition is a
(certain kind of) type, and that to prove that proposition is to give
an element of that type. We can turn the Booleans into types like so:

```
TrueP : Type
TrueP = ⊤

FalseP : Type
FalseP = ∅

IsTrue : Bool → Type
IsTrue true  = TrueP
IsTrue false = FalseP
```

So `IsTrue`{.Agda} sends `true`{.Agda} to the type `⊤`{.Agda}, which
has an element `tt`{.Agda}; under the interpretation that proofs of
propositions are the elements of the types representing those
propositions, this means we can prove that `IsTrue true` holds. On the
other hand, `false`{.Agda} gets sent to `∅`{.Agda}, which has no
elements by definition. Therefore, we can't prove that `IsTrue false`
holds --- at least, not without assuming some contradictory
hypotheses.

An amazing feature of the propositions-as-types idea is that the
operations on types we have seen in the last two lectures become
operations on propositions.

In ordinary logic, to prove `P and Q` we need to prove `P` and to
prove `Q`. That is, a proof of `P and Q` consists of a pair of proofs,
one for `P` and one for `Q`. We can turn this directly into a
definition.

```
_andP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type _
P andP Q = P × Q
```

Now consider implication. Implication means that, assuming you have a
proof of `P`, you can get a proof of `Q`. This is exactly what
functions do, so we can also turn this into a definition:

```
_impliesP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type _
P impliesP Q = P → Q
```

Once we have these as building blocks, we can start to construct other
logical operations. We can define when two propositions imply each
other: this is also known as "logical equivalence".

```
_iffP_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type _
P iffP Q = (P impliesP Q) andP (Q impliesP P)
```

We can prove that these definitions correspond correctly with the
operations on Booleans. Prove the following by case splitting. On the
left of the `iffP`{.Agda}, we use the ordinary operation on Booleans, and on
the right, we use the corresponding operation on propositions-as-types.

```
and→Type : (a b : Bool) → (IsTrue (a and b)) iffP ((IsTrue a) andP (IsTrue b))
-- Exercise:
and→Type a b = {!!}

⇒→Type : (a b : Bool) → (IsTrue (a ⇒ b)) iffP ((IsTrue a) impliesP (IsTrue b))
-- Exercise:
⇒→Type a b = {!!}
```

Negation can be seen as a special case of implication: "not P" is the same as "P implies false".

```
infix 3 ¬_  -- This is just to make ¬ go on the outside of most formulas

¬_ : {ℓ : Level} → Type ℓ → Type ℓ
¬_ P = P impliesP FalseP  -- P → ⊥
```

We had better make sure this means what we think it does.
```
not→Type : (a : Bool) → (IsTrue (not a)) iffP (¬ IsTrue a)
-- Exercise:
not→Type a = ?
```

The logic of the propositions-as-types is not exactly the same as the
logic of Booleans. The reason has to do with double negation: recall
that for the Booleans, `not not b ↔ b` always. With
propositions-as-types, we can show one direction of these implications:

```
implies¬¬ : {ℓ : Level} → {P : Type ℓ} → (P → (¬ ¬ P))
-- Exercise:
implies¬¬ p = ?
```

But, we cannot show that `¬ ¬ A impliesP A` in general!

```
-- Uncomment to try if you want!
-- impossible-implies¬¬ : ∀ {ℓ} (P : Type ℓ) → (¬ ¬ P) impliesP P
-- impossible-implies¬¬ P nnp = {!!}
```

One way to understand the difference between `¬ ¬ P` and `P` is that
we may think of `p : P` as giving *evidence* that the proposition `P`
is true. What `¬ ¬ P` says is that to assume `P` were false would be
false, but this does not in itself produce any evidence for `P`. This
quirk of type theoretic logic makes it a "constructive" logic ---
there is a difference between providing (or "constructing") evidence
for a proposition and proving that its falsehood would be absurd ---
as opposed to the "classical" logic of the Booleans.

It seems like we're at risk of `¬`s piling up endlessly, if the
implication only works in one direction. But in fact, as soon as we
have three `¬`s, we can cancel two of them.

```
¬¬¬implies¬ : {ℓ : Level} → {P : Type ℓ} → (¬ ¬ ¬ P) → (¬ P)
-- Exercise:
¬¬¬implies¬ nnnp = ?
```

Lots of properties stay the same from ordinary logic, here's a
collection. Some of these are tough! Most of these won't be used
later, so you can comment them out if you get stuck.

```
¬-not-both : {ℓ : Level} → {P : Type ℓ} → ¬ (P andP (¬ P))
-- Exercise:
¬-not-both x = ?

¬-not-same : {ℓ : Level} → {P : Type ℓ} → ¬ (P iffP (¬ P))
-- Exercise:
¬-not-same x = ?

¬¬-map : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → ¬ ¬ (P → Q) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-map f = ?

¬¬-func : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-func f = ?

¬¬-bind : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → (P → (¬ ¬ Q)) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-bind f nnp nq = ?
```

Some classical facts *almost* hold, in that we can prove them once
they are surrounded by `¬ ¬`. For both of these, you will need to use
`∅-rec`{.Agda} once you have proven a contradiction.

```
¬¬-implies¬¬ : {ℓ : Level} → {P : Type ℓ} → ¬ ¬ ((¬ ¬ P) → P)
-- Exercise: bit tricky!
¬¬-implies¬¬ n = ?

¬¬-pierce : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → ¬ ¬ (((P → Q) → P) → P)
-- Exercise: bit tricky!
¬¬-pierce n = ?
```

## Or

This pattern of relating logical operations to type operations
continues with `or`{.Agda}, but runs into a subtle hiccup. First,
define maps both ways.

```
or→Type-fro : (a b : Bool) → ((IsTrue a) ⊎ (IsTrue b)) → IsTrue (a or b)
-- Exercise:
or→Type-fro a b p = {!!}

or→Type-to : (a b : Bool) → IsTrue (a or b) → ((IsTrue a) ⊎ (IsTrue b))
-- Exercise:
or→Type-to a b p = {!!}
```

What this shows is that `IsTrue (a or b)` and `(IsTrue a) ⊎ (IsTrue b)`
are logically equivalent, that is, one `iffP`{.Agda} the other. But:
Define the map backwards again, but make the opposite choice in
the case `or→Type-to' true true`.

```
or→Type-to' : (a b : Bool) → IsTrue (a or b) → ((IsTrue a) ⊎ (IsTrue b))
-- Exercise:
or→Type-to' a b p = {!!}
```

This has to do with the fact that not *every* type should be thought
of as a proposition. Some types, like `Bool`{.Agda} and `ℕ`{.Agda},
are better thought of as sets having many different elements. What we
are noticing with `or`{.Agda} above is that the disjoint union of two
propositions can be a non-trivial data type. We actually saw this
earlier, when we proved that `Bool`{.Agda} is bijective with `⊤ ⊎ ⊤`.

In this case, having an element of `(IsTrue a) ⊎ (IsTrue b)`, is
*more* information than just knowing that `a` or `b` is true. If it
happens to be the case that both `a` and `b` are true, the element
still makes a choice between the two sides.

In a later lecture we will make a definition that exactly picks out
which types are the ones it is appropriate to think of as
propositions: types that have at most one element. We think of this
unique element as "the fact that the proposition is true". We can
properly define the operation which corresponds to the proposition `P
or Q`, but we will not have the technology for that until we have
worked through Part 2.

Disjunction lets us highlight another place where constructive logic
differs from classical logic. You will have a hard time proving the
following!

```
-- Uncomment to try if you want!
-- impossible-LEM : ∀ {ℓ} (P : Type ℓ) → (¬ P) ⊎ P
-- impossible-LEM = {!!}
```

But again, this becomes true once we surround it with `¬ ¬`.

```
¬¬-LEM : ∀ {ℓ} (P : Type ℓ) → ¬ ¬ ((¬ P) ⊎ P)
-- Exercise:
¬¬-LEM P x = {!!}
```

The proof of the following works on a similar principle: suppose you
have one side and then use it to prove the other.

```
¬¬-weird : ∀ {ℓ} (P Q : Type ℓ) → ¬ ¬ ( (P → Q) ⊎ (Q → P))
-- Exercise:
¬¬-weird P Q x = {!!}
```

## Induction

How can we use these propositions-as-types to prove things about other
types? For this, we use an upgraded form of recursion principles,
called "induction principles". The difference is that, whereas
recursion principles allowed us to define ordinary functions out of
`Bool`{.Agda}, `ℕ`{.Agda}, etc., induction principles allow us to
define *dependent* functions.

`Bool`{.Agda} is the easiest. There are only two cases, so we just have to
upgrade the inputs to lie in type corresponding to each case:

```
Bool-ind : {ℓ : Level} {C : Bool → Type ℓ}
         → (ctrue : C true)
         → (cfalse : C false)
         → ((x : Bool) → C x)
-- Exercise:
Bool-ind ctrue cfalse x = {!!}
```

The induction principle for `A ⊎ B` is upgraded in a similar way. In
the recursion principle, the inputs were maps `A → C` and `B → C`. If
`C` is now a type dependent on `A ⊎ B`, these maps have to land in `C
x`, where `x : A ⊎ B`. Luckily, there are obvious candidates for `x` in
both cases: take the `inl` or `inr` of the input `a : A` or `b : B`
respectively.

```
⊎-ind : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : A ⊎ B → Type ℓ''}
      → (cinl : (a : A) → C (inl a))
      → (cinr : (b : B) → C (inr b))
      → (x : A ⊎ B) → C x
-- Exercise:
⊎-ind cinl cinr x = {!!}
```

`ℕ`{.Agda} is a little trickier. It is best to think of ordinary
mathematical induction, and consider `C` to be some property of the
natural numbers we are trying to check. Then the two inputs make
sense: we first have the base case of type `C zero`, claiming that the
property `C` holds for `zero`{.Agda}. Then we have the inductive step
for `suc`{.Agda}: saying that, for any `n : ℕ`, if we can prove `C`
holds for `n` then it also holds for `suc n`.

If we can provide both of those things, then we get a function from
`(n : ℕ) → C n`, meaning that `C` holds for every `n`.

```
ℕ-ind : {ℓ : Level} {C : ℕ → Type ℓ}
         → (czero : C zero)
         → (csuc : (n : ℕ) → C n → C (suc n))
         → ((n : ℕ) → C n)
-- Exercise:
ℕ-ind czero csuc n = ?
```

As in recursion, we don't often need to use `Bool-ind`{.Agda},
`⊎-ind`{.Agda} or `ℕ-ind`{.Agda}; we can instead use the
pattern-matching features of Agda directly.

```
isEvenP : ℕ → Type
isEvenP n = IsTrue (isEven n)

isOddP : ℕ → Type
isOddP n = IsTrue (isOdd n)

isZeroP : ℕ → Type
isZeroP n = IsTrue (isZero n)

```

## Quantifiers

mvrnote: should talk about sigma and pi as exists and forall

```
evenOrOdd : (n : ℕ) → isEvenP n ⊎ isOddP n
-- Exercise:
evenOrOdd n = {!!}

zeroImpliesEven : (n : ℕ) → (isZeroP n) impliesP (isEvenP n)
-- Exercise:
zeroImpliesEven n = {!!}
```

```
Σ-⊎-distr : {A : Type} {B C : A → Type}
                   → (Σ[ a ∈ A ] (B a ⊎ C a))
                   → (Σ[ a ∈ A ] B a) ⊎ (Σ[ a ∈ A ] C a)
-- Exercise:
Σ-⊎-distr x = {!!}
```

For the following two, you should remember that `¬`{.Agda} is simply
functions into `∅`{.Agda}. Once you unfold that definition, the below
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

## Equality

The most fundamental proposition concerning the data we have seen so
far is equality. We can define equality for Booleans inductively as
follows:

```
_≡Bool_ : (a b : Bool) → Type
true ≡Bool true = ⊤
true ≡Bool false = ∅
false ≡Bool true = ∅
false ≡Bool false = ⊤
```

This kind of inductively defined equality is often known as
"observational equality". Using induction, we can prove that
observational equality is a reflexive, symmetric, and transitive
relation on Booleans.

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
relation of equality, as expected. These can be proven purely by
splitting into all the possible cases.

```
not-equals : (a b : Bool)
  → a ≡Bool b
  → (not a) ≡Bool (not b)
-- Exercise:
not-equals a b p = {!!}

and-equals : (a1 a2 b1 b2 : Bool)
  → (a1 ≡Bool a2)
  → (b1 ≡Bool b2)
  → (a1 and b1) ≡Bool (a2 and b2)
-- Exercise:
and-equals a1 a2 b1 b2 p q = {!!}
```

We can similarly define equality of natural numbers.

```
_≡ℕ_ : (n m : ℕ) → Type
-- Exercise:
n ≡ℕ m = ?
```
Try writing out this definition in plain language to check your
understanding.

Similarly to `≡Bool`, We can prove that equality of natural numbers is
a reflexive, symmetric, and transitive relation. The difference in the
proofs is that, because `ℕ`{.Agda} is a recursive datatype, our proofs
will need to be recursive too.

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
  → (n1 + m1) ≡ℕ (n2 + m2)
-- Exercise:
+-≡ℕ n1 n2 m1 m2 p q = {!!}
```

Finally, show that addition is unital, associative and commutative.
(These are all very easy by induction.)

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

≡ℕ-comm : (n m : ℕ) → (n +ℕ m) ≡ℕ (n +ℕ m)
-- Exercise:
≡ℕ-comm n m = {!!}
```

It would be quite tedious if we had to define the specific notion of
equality we wanted for every type we had. It's also not clear exactly
how we could do it. For example, to say that elements in the disjoint
union `A ⊎ B` are equal, we would want to say that if `a = a'` then
`inl a = inl a'` and if `b = b'` then `inr b = inr b'` and that it is
never the case that `inl a = inr b` or vice versa (since the union is
disjoint). But without knowing specifically what the types `A` and
`B` are, we wouldn't know what equality meant for them.

Remarkably, it is possible to give a uniform notion of "equality" for
any type --- this is the subject of Part 2. But, as we'll see shortly,
this general notion of *paths* between of elements of general types
will not always be a proposition --- paths will often be interesting
pieces of data in their own right.

Before we go on, let's see one more inductively defined proposition:
the ordering of natural numbers: mvrnote: does this get used? did we
put this in for Fin eventually?

```
_≤ℕ_ : (n m : ℕ) → Type
zero ≤ℕ m = TrueP
suc n ≤ℕ zero = FalseP
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

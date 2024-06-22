```
module 1--Type-Theory.1-X--Universe-Levels-and-More-Inductive-Types where
```

# Lecture 1-3: Universe Levels and More Inductive Types

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
```
-->

## Universe Levels

There is a lingering question from Lecture 1-1. what is the type of
the universe `Type`{.Agda} itself?. One option is to just declare that
`Type : Type`, this is the approach that the Haskell language takes.
This works fine for practical programming but leads to logical
contradictions thanks to some "Russell-style" paradoxes. (Search up
"Girard's paradox" if you are curious!)

For this reason, Agda allows us to specify "universe levels", usually
written with the symbol `ℓ`, that stratify types into a hierarchy.
`Type`{.Agda} on its own is secretly `Type₀` the universe of all types
at level zero. But `Type₀` itself does not live at level zero, rather
one step up: `Type₀ : Type₁`. Similarly, `Type₁ : Type₂`, and so on.
In general, the universe `Type ℓ` lives in universe `Type (ℓ-suc ℓ)`
for any level `ℓ`, where `ℓ-suc`{.Agda} is a built-in function that
increments a level by one.

When we prove general facts about functions, we might want to apply
them in situations where the universe `Type`{.Agda} is involved, or
maybe things lying in higher levels still. This is accomplished by
having functions accept types of *any* universe level, a trick known
technically as "universe polymorphism". So as an example, for the very
final time, here is the universe-polymorphic definition of the
identity function on any type, where that type may live in any
universe.

```
idfun : {ℓ : Level} → (A : Type ℓ) → A → A
idfun A x = x
```

`Level`{.Agda} here is the magic, built-in collection of universe
levels, and it can't be mixed together with actual types. For each
level `ℓ : Level`, there is a corresponding universe of that level
called `Type ℓ`.

Similarly to `idfun`{.Agda}, we can upgrade some of the functions we
have defined into their final, most general versions.

```
const : {ℓ ℓ' : Level}
      → {A : Type ℓ}
      → {B : Type ℓ'}
      → A
      → B → A
const a b = a

apply : {ℓ ℓ' : Level}
      → {A : Type ℓ}
      → {B : A → Type ℓ'}
      → ((x : A) → B x)
      → (x : A)
      → B x
apply f a = f a

flip : {ℓ₁ ℓ₂ ℓ₃ : Level}
     → {A : Type ℓ₁}
     → {B : Type ℓ₂}
     → {C : A → B → Type ℓ₃}
     → ((x : A) (y : B) → C x y)
     → ((y : B) (x : A) → C x y)
flip f y x = f x y
```

Here is our very final definition of function composition, where all
the types involved might live in different universes.

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
Agda considers definitions with underscores specially, and lets us
refer to such a definition in two ways: either the normal way, that
is, `_∘_ g f`, or with the arguments replacing the underscores: `g ∘
f`. We will use infix operators like this whenever it is closer to
normal mathematical practice, like this composition operator or
arithmetical operators `+`{.Agda}, `·`{.Agda}, etc.

The built-in type constructors we have seen are universe polymorphic.
These type constructors, like functions `→` and products `×`{.Agda},
are functions that take types as arguments and produce types as
output. If you type `C-c C-d` and enter `_×_`, you will see that it
has type

```
my× : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
my× = _×_
```

This uses the one remaining operation on universe levels, the
`ℓ-max`{.Agda} operation that gives the larger of the two supplied
universe levels. In this case, `×`{.Agda} accepts types in any
universe and gives back a type in the largest of those two universes,
in a sense lifting the type in the smaller universe up to the bigger
one.

The inductive types we defined earlier are all defined to lie in
`Type`{.Agda}, which, the smallest type universe `Type ℓ-zero`. What
if we want to use these inductive types in higher universes?

One option is to define new versions of these types that allow us to
specify which universe level we want them to lie in:

```
data Boolℓ (ℓ : Level) : Type ℓ where
  trueℓ  : Boolℓ ℓ
  falseℓ : Boolℓ ℓ
```

This quickly gets annoying, because we need operations to convert
between versions of `Boolℓ` at different universe levels.

Instead, we will use a very simple inductive type to "lift" an
arbitrary type from one universe level to a higher one.

```
data Lift {ℓ ℓ' : Level} (A : Type ℓ) : Type (ℓ-max ℓ ℓ') where
  lift : A → Lift A

lower : {ℓ ℓ' : Level} {A : Type ℓ} → Lift {ℓ' = ℓ'} A → A
lower (lift a) = a
```

The type `Lift A`{.Agda} is really just a wrapper around `A`; for all
intents and purposes the types are the same. But, `Lift A`{.Agda} has
a higher universe level than `A`.

Thankfully, we only need to use this `Lift`{.Agda} type very
occasionally; most of the code we write will be completely generic in
which universe levels are used.


## The Empty Type

The type `⊤`{.Agda} we saw in the previous is very simple, having only
one constructor `tt`{.Agda}. We can go even further and define a data
type `∅`{.Agda} with no constructors at all. This is the "empty type":

```
data ∅ : Type where
-- Nothing!
```

We want to define functions out of this inductive type by pattern
matching, except in this case there are no constructors and so no
patterns to match with. We cannot just write no definition at all, so
Agda has special syntax for this situation: `()`, called the "absurd"
pattern, because to have an actual element of the empty type
`∅`{.Agda} to match on here would be absurd.

```
impossible-Bool : ∅ → Bool
impossible-Bool ()
```

And so, the recursion principle of the empty type is a version of the
"ex falso quodlibet" principle of logic: with no assumptions, we may
define a map `∅ → A` for any type `A` at all.

```
∅-rec : {ℓ : Level} {A : Type ℓ}
        → ∅ → A
∅-rec ()
```

Whenever we are provided an argument of type `∅`{.Agda}, we can use
this empty pattern to avoid writing anything at all. On occasion, we
will have to do some constructions to produce an element of `∅`{.Agda}
rather than having it handed to us: in those cases we will have to use
`∅-rec`{.Agda} by hand.

We can show that "zero times `A` is always zero", interpreting "times"
and "zero" as type constructors. For the first direction, we don't
have to use any special features of `∅`{.Agda}.

```
∅×-to : (A : Type) → ∅ × A → ∅
-- Exercise:
∅×-to A x = {!!}
```

The other direction is different: after all, we somehow have to summon
an element of an arbitrary type `A` out of nowhere. There are two ways
to do it, either using an absurd pattern immediately, or using
`∅-rec`{.Agda} to produce the impossible element of `A`.

```
∅×-fro : (A : Type) → ∅ → ∅ × A
-- Exercise:
∅×-fro A a = {!!}
```


## Disjoint Unions

Next let's define the disjoint union of two types. An element of the
disjoint union `A ⊎ B` should either be an element of `A` or an
element of `B`. We can turn this into the definition of an inductive
type.

```
data _⊎_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
```

The names of the constructors are short for "in-left" and "in-right".
Here's a very simple example, that just identifies which side the
input is on.

```
isLeft : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
       → A ⊎ B → Bool
isLeft (inl a) = true
isLeft (inr b) = false
```

Since a `Bool`{.Agda} is either `true`{.Agda} or `false`{.Agda}, we
should be able to see `Bool`{.Agda} as the disjoint union of the set
$\{true\}$ (represented by `⊤`{.Agda}) and $\{false\}$ (represented by
another copy of `⊤`{.Agda}). We can construct maps to that effect:

```
Bool→⊤⊎⊤ : Bool → ⊤ ⊎ ⊤
-- Exercise:
Bool→⊤⊎⊤ b = {!!}

⊤⊎⊤→Bool : ⊤ ⊎ ⊤ → Bool
-- Exercise:
⊤⊎⊤→Bool c = {!!}
```

You should choose the above maps so that if you turn a `Bool`{.Agda}
into an element of `⊤ ⊎ ⊤` and then back into a `Bool`{.Agda}, you get
to where you started, and similarly for starting at `⊤ ⊎ ⊤`.
Therefore, these maps give a bijection between `Bool`{.Agda} and `⊤ ⊎
⊤`.

The above examples happened to not actually use the contents of `A`
and `B`. Try the following, where those contents are necessary to
produce the required output.

```
⊎-map : {A B C D : Type} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
-- Exercise:
⊎-map f g d = {!!}

⊎-fold : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
-- Exercise:
⊎-fold f g d = {!!}
```

It's worth noting that the integers are the disjoint union of two
copies of the natural numbers:

```
ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
-- Exercise:
ℤ→ℕ⊎ℕ z = {!!}


ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
-- Exercise:
ℕ⊎ℕ→ℤ z = {!!}
```

There is a sense in which `⊎`{.Agda} acts like an addition of types.
Because `Bool`{.Agda} has two elements and `Day`{.Agda} has seven, the
disjoint union should have nine, which we can check by case-splitting
into all the possibilities.

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

Like addition, the operation is associative and commutative.

```
⊎-assoc-to : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
-- Exercise:
⊎-assoc-to = {!!}

⊎-assoc-fro : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
-- Exercise:
⊎-assoc-fro = {!!}

⊎-comm : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂}
  → A ⊎ B → B ⊎ A
-- Exercise:
⊎-comm = {!!}
```

And the type `∅`{.Agda} acts like zero.

```
∅⊎-to : {ℓ : Level} (A : Type ℓ) → ∅ ⊎ A → A
-- Exercise:
∅⊎-to A x = {!!}

∅⊎-fro : {ℓ : Level} (A : Type ℓ) → A → ∅ ⊎ A
-- Exercise:
∅⊎-fro A a = {!!}
```

The general recursion principle for the disjoint union is "dual" to
the universal mapping property of the product that we saw at the end
of the last lecture. There, we had that from two functions `C → A` and
`C → B` we get a map `C → A × B` by pairing up the results. Now, from
`f : A → C` and `g : B → C`, we get a map `A ⊎ B → C`.

```
⊎-rec : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      → (A → C)
      → (B → C)
      → (A ⊎ B → C)
⊎-rec f g (inl a) = f a
⊎-rec f g (inr b) = g b
```

mvrnote: distributivity


```
Σ-⊎-distr : {A : Type} {B C : A → Type}
                   → (Σ[ a ∈ A ] (B a ⊎ C a))
                   → (Σ[ a ∈ A ] B a) ⊎ (Σ[ a ∈ A ] C a)
-- Exercise:
Σ-⊎-distr x = {!!}

Σ-⊎-distr-inv : {A : Type} {B C : A → Type}
                   → (Σ[ a ∈ A ] B a) ⊎ (Σ[ a ∈ A ] C a)
                   → (Σ[ a ∈ A ] (B a ⊎ C a))
-- Exercise:
Σ-⊎-distr-inv x = {!!}
```

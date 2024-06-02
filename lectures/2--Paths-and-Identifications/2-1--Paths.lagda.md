```
module 2--Paths-and-Identifications.2-1--Paths where
```

# Lecture 2-1: Paths

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
```
-->

Before we begin: The following block lets us refer to some
arbitrary types `A`, `B`, ... and terms `x : A`, `y : A`, ... without
clutting every definition with `{A : Type} {B : Type}`, and so on.

```
private
  variable
    ℓ ℓ₂ : Level
    A B C D : Type ℓ
    x y : A
```

In Lecture 1-3, we saw that we could define types representing
equality in inductively defined types like `Bool`{.Agda} and
`ℕ`{.Agda}. However, it would be tedious to have to define equality
separately for every type (and worse, to check that every function
preserves equality), and it would make proving general facts about
equality difficult.

To resolve this issue, Cubical Agda takes a page from homotopy theory
--- the mathematical theory of continuous deformations of
shapes. Classically, a *homotopy* is a continuous deformation of one
object into another. In homotopy theory, we only care about the
properties of objects which are unchanged by continuous deformation;
in other words, for the purposes of homotopy theory, to give a
homotopy between objects is to say that they are the same for all
homotopy theoretical purposes. That is, homotopies are ways to say two
things are the same.

Since we are looking for a general concept of sameness for all types,
it makes sense to take some ideas from homotopy theory. Let's see a
bit more of the classical theory first, so we have something to ground
our intuitions.

If $f$ and $g : X → Y$ are two continuous functions between spaces $X$
and $Y$ (say, subsets of $n$-dimensional Euclidean space), then a
homotopy $h$ between $f$ and $g$ is a function $h : [0, 1] × X → Y$ of
two variables $h(t, x)$ where $h(0, x) = f(x)$ and $h(1, x) = g(x)$
for all $x$. The intermediate values $h(t, x)$ continuously deform the
function $f$ into the function $g$.

(If you are reading this in your editor, we are using "$" to delimit
mathematical expressions as opposed to type theoretic ones;
admittedly the difference is not too important.)

As we have seen in Lecture 1-1, we can think of a function of two
variables as a function of one variable landing in functions of one
variable. Using this idea, we can see a homotopy $h$ between $f$ and
$g$ as a function $h : [0, 1] → (X → Y)$ into the space of continuous
functions $X → Y$ where $h(0) = f$ and $h(1) = g$. In other words, a
homotopy is a *path* in function space, where a path is a continuous
function out of the unit interval $[0, 1]$. In general, if objects $F$
and $G$ are points of some space $S$, then a homotopy between $F$ and
$G$ is a path $h : [0, 1] → S$ with $h(0) = F$ and $h(1) = G$, no
matter what $F$ and $G$ are.


## Paths

This is the idea we will borrow for type theory. We will axiomatize a
special "type" `I`{.Agda} --- meant to be our type theoretic version of the
unit interval $[0, 1]$ --- with two elements `i0 : I` and `i1 : I`
(meant to be the endpoints $0$ and $1$). A *path* will then be a function
`h : I → S` into any type `S`. In general then, our notion of sameness
`x ≡ y` for any two elements `x y : S` will be a function `h : I → S`
with `h(i0) = x` and `h(i1) = y`. Crucially, these will be
*definitional* equalities; Agda will check that values of the function
on `i0` and `i1` match exactly with the ones that we specify.

However, `I`{.Agda} is not like other types, because we don't intend
it to represent a type of mathematical object. We are just using it as
a tool to get at a notion of sameness. For that reason, we silo it and
its endpoints in their own special universe.

```
_ : IUniv
_ = I

_ : I
_ = i0

_ : I
_ = i1
```

This prevents us from using all our usual type operations on `I`, which
is good, since it isn't meant to be treated as a data type.

```
-- Uncomment these and try them out, if you want!
{-
_ : Type
_ = I × I  -- error!

_ : Type
_ = Bool → I -- error!
-}
```

However, since we want to discuss types of paths in any type, we have
the rule that for any type `A : Type`, the type `I → A` of functions from
`I` to `A` is a bona-fide type.

```
_ : Type
_ = I → Bool
```

Now we come to paths. Agda provides a built-in type `Path A x y` which
is like a function `I → A`, but where the endpoints are known to be
`x` and `y` *by definition*. That is, starting with `p : Path A x y`,
evaluating `p i0` gives *exactly* `x`, and evaluating `p i1` gives
*exactly* `y`. We will typically use the infix notation `x ≡ y` for
`Path A x y` when the type `A` can be inferred. (To enter the `≡`
symbol, write `\equiv`).

We define new paths just like we define functions: we assume we have an
`i : I`, and then give an element of the type we are making the path
in. The simplest path we can come up with is the "reflexivity" path:
for any element `x`, there is a constant path at `x`.

```
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x
```

Interpreted as a statement about sameness, this means that `x` is the
same as `x` - certainly a good start!

Even with such a basic principle, this is already enough to start
proving some useful equalities.

```
∘-assoc : (h : C → D)
          (g : B → C)
          (f : A → B)
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
-- Exercise:
∘-assoc h g f i x = ?

∘-idˡ : (f : A → B) → f ∘ (λ a → a) ≡ f
-- Exercise:
∘-idˡ f i x = ?

∘-idʳ : (f : A → B) → (λ b → b) ∘ f ≡ f
-- Exercise:
∘-idʳ f i x = ?
```

We can even show that `Bool` has the structure of a *Boolean algebra*.
In the following, `∀ x` is just syntactic sugar for `(x : _)`, so this
only works when the type of `x` can be inferred by Agda.

```
notnot : ∀ x → not (not x) ≡ x
notnot true  = refl
notnot false = refl

or-zeroˡ : ∀ x → true or x ≡ true
or-zeroˡ _ = refl

or-zeroʳ : ∀ x → x or true ≡ true
or-zeroʳ false = refl
or-zeroʳ true  = refl

or-identityˡ : ∀ x → false or x ≡ x
or-identityˡ _ = refl

or-identityʳ : ∀ x → x or false ≡ x
or-identityʳ false = refl
or-identityʳ true  = refl

or-comm : ∀ x y → x or y ≡ y or x
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl

or-assoc : ∀ x y z → x or (y or z) ≡ (x or y) or z
or-assoc false y z = refl
or-assoc true  y z = refl

or-idem : ∀ x → x or x ≡ x
or-idem false = refl
or-idem true  = refl
```

OK, that's enough of that --- it's straightforward to keep going.
(You can find all the laws for a Boolean algebra listed on Wikipedia,
or you can peek ahead to 2-2 and take all the laws for a De Morgan
algebra (but where `∧ = and` and `∨ = or` and `~ = not`) together with
the "Law of Excluded Middle": `b or (not b)`.)

Types of paths are types like any other, so we can define functions
that accept paths as arguments and produce paths as results.

```
congNonDep : (f : A → B)
  → (x ≡ y)
  → f x ≡ f y
congNonDep f p i = f (p i)
```

This is the principle that says that doing the same thing to both
sides of an equation gives an equal result --- very useful!

```
cong-bin : (f : A → B → C) {a a' : A} {b b' : B}
         → (p : a ≡ a')
         → (q : b ≡ b')
         → (f a b) ≡ (f a' b')
-- Exercise:
cong-bin f p q = ?

cong-∘ : (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → congNonDep (g ∘ f) p ≡ congNonDep g (congNonDep f p)
-- Exercise:
cong-∘ f g p = ?
```

## Paths in Pair and Function Types

Now we can begin to ask what paths look like in various types.
Inductive data types (like `Bool`{.Agda}) will be covered in detail in
Lecture 2-3. Let's begin with something easier: what is a path in a
pair type? It's a pair of paths of the components!

To prove these, remember that a path is secretly a function `I → A`,
so ignoring the endpoints, the first is asking for a function
`(I → A) × (I → B) → (I → A × B)`. It should be easy to come up with
such a function, and it turns out that this obvious definition has the
correct endpoints.

```
≡-× : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
-- Exercise:
≡-× (p , q) = ?

≡-fst : {x y : A × B} → x ≡ y → (fst x ≡ fst y)
-- Exercise:
≡-fst p = ?

≡-snd : {x y : A × B} → x ≡ y → (snd x ≡ snd y)
-- Exercise:
≡-snd p = ?
```

Similarly, what is a path in a function type? It is a function landing
in paths!

```
funExt : {f g : A → B}
  → ((x : A) → f x ≡ g x)
  → f ≡ g
-- Exercise:
funExt f = ?

funExt⁻ : {f g : A → B}
  → f ≡ g
  → ((x : A) → f x ≡ g x)
-- Exercise:
funExt⁻ p = ?
```
This is the principle of "function extensionality": to say that `f`
is the same as `g` means that, for all `x`, `f x` is the same as `g x`.

The `≡` constructor has low precedence, so `f x ≡ f y` means `(f x) ≡
(f y)`, and not something weird like `f (x ≡ f) y`.

Try proving function extensionality for binary functions.

```
funExt2 : {f g : A → B → C}
       (p : (x : A) (y : B) → f x y ≡ g x y)
       → f ≡ g
-- Exercise:
funExt2 p i x y = ?
```

## Paths over Paths

A path in a type `A` is a function `p : I → A`. But what if `A` itself
were a path of types `A : I → Type`? Then we could consider dependent
functions `p : (i : I) → A i`; we call these paths over the path `A`.
The name for this in Agda is `PathP`, for Path (over) P(ath).

```
_ : (A : I → Type) (x : A i0) (y : A i1) → Type
_ = PathP
```

As with paths, where `p : x ≡ y` is a function `I → A` with `p i0 = x`
by and `p i1 = y` by definition, if we have `p : PathP A a b`, then `p
i0 = a` and `p i1 = b` by definition. In fact, the type `Path A x y`
is defined in terms of `PathP`, where the path of types happens to be
constant at the type `A`. This is just like how non-dependent
functions `A → B` are exactly dependent functions `(x : A) → B` where
`B` happens to be a constant type and not depend on `x`.

```
myPath : (A : Type) (x : A) (y : A) → Type
-- Exercise: (easy)
myPath A x y = ?
```

We can now clear up a lingering question from the previous section. We
calculated what paths in pair and function types should be, but only
for *non-dependent* pairs and functions. It turns out `PathP` is
exactly the missing ingredient for describing paths in these types.

Function extensionality can be extended to *dependent* function
extensionality. The body of the definition is identical to
`funExt`{.Agda} but the type improves:

```
depFunExt : {B : A → I → Type ℓ₂}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → ((x : A) → PathP (B x) (f x) (g x))
  → PathP (λ i → (x : A) → B x i) f g
-- Exercise:
depFunExt p i x = {!!}
```

Similarly, we can upgrade `congNonDep`{.Agda} to work with dependent
functions:

```
cong : {B : A → Type ℓ₂} {x y : A}
       (f : (a : A) → B a)
     → (p : x ≡ y)
     → PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)
```

Now for dependent pairs. There are actually two places dependency
could show up here. The first is the obvious one, when `B` depends on
`A`. The definitions are the same as in the non-dependent case, so try
to fill in the parameters to the `PathP`{.Agda} type.

```
module _ {A : Type ℓ} {B : A → Type ℓ₂}
  {x y : Σ[ a ∈ A ] B a}
  where

  ΣPathP→PathPΣ' : Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y)
         → x ≡ y
  -- Exercise:
  ΣPathP→PathPΣ' eq i = {!!}

  PathPΣ→ΣPathP' : x ≡ y
         → Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y)
  -- Exercise:
  PathPΣ→ΣPathP' eq = {!!}

```

But there is a second notion of dependency: it could be that the types
`A` and `B` themselves come from a path of types. Again, the actual
definitions are identical; but their types become more powerful.

```
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₂}
  {x : Σ[ a ∈ A i0 ] B i0 a} {y : Σ[ a ∈ A i1 ] B i1 a}
  where

  ΣPathP→PathPΣ : Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
         → PathP (λ i → Σ[ a ∈ A i ] B i a) x y
  -- Exercise:
  ΣPathP→PathPΣ : Σ[ p ∈ PathP ? ? ? ] PathP ? ? ?
         → PathP (λ i → Σ[ a ∈ A i ] B i a) x y

  PathPΣ→ΣPathP : PathP (λ i → Σ[ a ∈ A i ] B i a) x y
         → Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
  -- Exercise:
  ΣPathP→ΣPathP : PathP (λ i → Σ[ a ∈ A i ] B i a) x y
         → Σ[ p ∈ PathP ? ? ? ] PathP ? ? ?
```

## Squares

A path between paths is a path in type of paths, which is to say, a
function `a : I → (I → A)`. We can therefore think of
paths-between-paths as functions of two interval variables `i` and
`j`. Though we don't want to use the elements of `I` like data and so
don't let ourselves form the type `I × I`, we can nevertheless think
of a function of two interval variables as giving a function out of a
square.

            a-1
       a01 - - - > a11
        ^           ^
    a0- |           | a1-      ^
        |           |        j |
       a00 — — — > a10         ∙ — >
            a-0                  i

We will see a square as above as a path between the paths `a0-` and
`a1-`. However, these don't have the same type; `a0- : a00 ≡ a01` and
`a1- : a10 ≡ a11`. But using `a-0` and `a-1`, we may "continuously
vary" from the type of `a0-` to the type of `a1-`. Consider the type
following type family:

```
a-0≡a-1 : {A : Type ℓ} {a00 a01 a10 a11 : A}
          (a-0 : a00 ≡ a10) (a-1 : a01 ≡ a11)
        → I → Type ℓ
a-0≡a-1 a-0 a-1 i = a-0 i ≡ a-1 i
```

Note that:

* `(a-0≡a-1 a-0 a-1 i0) = (a00 ≡ a01)` and
* `(a-0≡a-1 a-0 a-1 i1) = (a10 ≡ a11)`

by definition.

We want to say that the square is somehow an element of this
continuously varying path type. With `PathP`{.Agda}, we can define the type
of squares as paths over the continuously varying path `a-0≡a-1`{.Agda}:

```
Square : {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (a0- : a00 ≡ a01)
       → (a1- : a10 ≡ a11)
       → (a-0 : a00 ≡ a10)
       → (a-1 : a01 ≡ a11)
       → Type ℓ
Square a0- a1- a-0 a-1 = PathP (a-0≡a-1 a-0 a-1) a0- a1-
```
Here's the picture again, for you to inspect:

             a-1
       a01 - - - > a11
        ^           ^
    a0- |           | a1-      ^
        |           |        j |
       a00 — — — > a10         ∙ — >
             a-0                 i

Elements of the `Square A` type are squares exist in a constant type
`A`. But just as we can upgrade `Path` to `PathP` where the type `A`
can vary over the path, we can upgrade `Square` to `SquareP` where the
type can vary over the square.

```
SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
  (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋
```

mvrnote: exercises?

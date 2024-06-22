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
open import 1--Type-Theory.1-X--Universe-Levels-and-More-Inductive-Types
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

In Lecture 1-3 mvrnote:link, we saw that we could define types that
represent equality in another inductive type, like `Bool`{.Agda} or
`ℕ`{.Agda}. It would be tedious to have to define equality separately
for every type (and worse, to check that every function preserves
equality), and it would make proving general facts about equality
difficult.

To resolve this issue, Cubical Agda takes a page from homotopy theory
--- the mathematical theory of continuous deformations of shapes.
Classically, a *homotopy* is a continuous deformation of one object
into another. In homotopy theory, we only care about the properties of
objects which are unchanged by continuous deformation; so for the
purposes of homotopy theory, to give a homotopy between objects is to
say that they are the same, at least for all homotopy-theoretical
purposes. In other words, to a homotpy theorist, a homotopy is a way
to say two things are the same.

We will use this as inspiration for our general concept of sameness
that will apply to all types. Let's see a bit more of the classical
theory first, so we have something to ground our intuitions.

If $f, g : X → Y$ are two continuous functions between spaces $X$ and
$Y$ (say, subsets of Euclidean space), then a homotopy $h$ between $f$
and $g$ is a function $h : [0, 1] × X → Y$ of two variables $h(t, x)$
where $h(0, x) = f(x)$ and $h(1, x) = g(x)$ for all $x$. The
intermediate values $h(t, x)$ continuously deform the function $f$
into the function $g$.

::: Aside:
If you are reading this in your editor, we are using "$" to delimit
mathematical expressions as opposed to type theoretic ones;
admittedly the difference is not too important.
:::

As we saw in Lecture 1-1, we can think of a function of two variables
as a function of one variable that gives back another function of one
variable (via `curry×`{.Agda} and `uncurry×`{.Agda}). Using this idea,
we can see a homotopy $h$ between $f$ and $g$ as a function $h : [0,
1] → (X → Y)$ into the space of continuous functions $X → Y$, so that
$h(0) = f$ and $h(1) = g$. In other words, a homotopy is a *path* in
function space, where a path is a continuous function out of the unit
interval $[0, 1]$.

In general, if objects $F$ and $G$ are points that live in some space
$S$, then a homotopy between $F$ and $G$ is a path $h : [0, 1] → S$
with $h(0) = F$ and $h(1) = G$, no matter what $F$ and $G$ are.


## Paths

This is the idea we will borrow for type theory. Agda provides a
special "type" `I`{.Agda} to act as our type theoretic version of the
unit interval $[0, 1]$, equipped with two elements `i0 : I` and `i1 :
I`, which act as the endpoints $0$ and $1$. A *path* `x ≡ y` from `x`
to `y` of type `A` will then be a function `h : I → A` where `h(i0) =
x` and `h(i1) = y`. Agda will remember the endpoints of our paths, so
that when we later evaluate the path at `i0`, we get `x` exactly, and
similarly for `i1` and `y`.

However, somewhat similarly to `Level`{.Agda}, the type `I`{.Agda} is
not like other types, because we don't intend it to represent an type
of mathematical object. Rather, we just using it as a tool to get at a
sensible notion of sameness. For that reason, it and its endpoints get
siloed in their own special universe.

```
_ : IUniv
_ = I

_ : I
_ = i0

_ : I
_ = i1
```

::: Aside:
Above we make a "definition" with name `_`; this signals to Agda to
check the type of what we provide, but then throw away the result. We
will use this to demonstrate the type of some expression without
having to invent a new name for it.
:::

This prevents us from using all our usual type operations on
`I`{.Agda}, which is good, since an element of `I`{.Agda} isn't meant
to be treated as a piece of data.

```
-- Uncomment these and try them out, if you want!
{-
_ : Type
_ = I × I  -- error!

_ : Type
_ = Bool → I -- error!
-}
```

However, since we want to discuss the types of paths in any type, we
have the special rule that for any type `A : Type`, the type `I → A`
of functions from `I` to `A` is a bona-fide type.

```
_ : Type
_ = I → Bool
```

Now we come to paths with specified endpoints. For `x` and `y`, Agda
provides a built-in type `x ≡ y` which is like a function `I → A`, but
where the endpoints are known to be `x` and `y` *by definition*. That
is, starting with `p : x ≡ y`, evaluating `p i0` gives *exactly* `x`,
and evaluating `p i1` gives *exactly* `y`, regardless of what the
definition of the path `p` actually is.

Sometimes, we will want write the type that the path is lying in
explicitly, for this we can use `Path A x y`.

We define new paths just like we define functions: we assume we have
an `i : I`, and then give an element of the type `A` we are making the
path in. The simplest path we can write down is the "reflexivity"
path: for any element `x`, there is a constant path at `x`.

```
refl : {A : Type ℓ} → {x : A} → x ≡ x
refl {x = x} i = x
```

Interpreted as a statement about sameness, this means that `x` is the
same as `x` --- certainly a good start!

Even with such a basic principle, this is already enough to start
proving some useful equalities.

```
∘-assoc : (h : C → D)
        → (g : B → C)
        → (f : A → B)
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
-- Exercise:
∘-assoc h g f i x = {!!}

∘-idˡ : (f : A → B) → f ∘ idfun A ≡ f
-- Exercise:
∘-idˡ f i x = {!!}

∘-idʳ : (f : A → B) → idfun B ∘ f ≡ f
-- Exercise:
∘-idʳ f i x = {!!}
```

We can even show that `Bool` has the structure of a *Boolean algebra*.
In the following, `∀ x` is just syntactic sugar for `(x : _)`. (This
only works when the type of `x` that is left off can be inferred by
Agda.)

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

::: Aside:
You can find all the laws for a Boolean algebra listed on Wikipedia,
or you can peek ahead to 2-2 and take all the laws for a De Morgan
algebra (but where `∧ = and` and `∨ = or` and `~ = not`) together with
the "Law of Excluded Middle": `b or (not b)`.
:::

Types of paths are types like any other, so we can define functions
that accept paths as arguments and produce paths as results.

```
congNonDep : (f : A → B)
  → x ≡ y
  → f x ≡ f y
congNonDep f p i = f (p i)
```

This is the principle that says that doing the same thing to both
sides of an equation gives an equal result --- very useful!

```
cong-bin : (f : A → B → C) {a a' : A} {b b' : B}
         → a ≡ a'
         → b ≡ b'
         → (f a b) ≡ (f a' b')
-- Exercise:
cong-bin f p q = {!!}

cong-∘ : (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → congNonDep (g ∘ f) p ≡ congNonDep g (congNonDep f p)
-- Exercise:
cong-∘ f g p = {!!}
```


## Inductive Types with Path Constructors

Alright, `refl`{.Agda} is great but can we get our hands on any other
paths? One way is to define inductive types that have path
constructors. (These are often called "Higher Inductive Types" or
HITs.)

Our first use of a path constructor is a more symmetrical version of
the integers. Remember that the definition of `ℤ`{.Agda} we gave back
in Lecture 1-2 is a little janky --- we have to treat the negatives
and the positives asymmetrically, assigning `zero`{.Agda} to the
`pos`{.Agda} side and shifting the `negsuc`{.Agda} side down by one.
Now that we have paths, we can define a version of the integers that
treats them the same --- as long as we add in a path between "positive
0" and "negative 0" to make them the same!

```
data ℤ' : Type where
  pos' : ℕ → ℤ'
  neg' : ℕ → ℤ'
  poszero≡negzero : pos' zero ≡ neg' zero
```

Arithmetic using these integers is easier to reasona about than the
version involving `negsuc`{.Agda}. First, here's the successor
function which you should compare to `sucℤ`{.Agda}.

```
sucℤ' : ℤ' → ℤ'
sucℤ' (pos' x) = pos' (suc x)
sucℤ' (neg' zero) = pos' (suc zero)
sucℤ' (neg' (suc x)) = neg' x
sucℤ' (poszero≡negzero i) = pos' (suc zero)
```

On positive integers, we use the ordinary successor of the enclosed
natural number. On negative integers, we check if the natural number
is zero, and if so, give back positive one, and use the enclosed
predecessor otherwise.

Notice that we have defined what the function does on zero twice! Once
as `pos' zero`, and again as `neg' zero`. The final case for the path
constructor forces us to check that we give the same answer both
times. And indeed we do, so that final case can be defined by the
constant path at `pos' (suc zero)`.

It is easy to convert backwards and fowards between these integers and
the original ones.

```
ℤ'→ℤ : ℤ' → ℤ
-- Exercise:
ℤ'→ℤ z = {!!}

ℤ→ℤ' : ℤ → ℤ'
-- Exercise:
ℤ→ℤ' z = {!!}
```

Complete the definition of addition.

```
predℤ' : ℤ' → ℤ'
-- Exercise:
predℤ' z = {!!}

_+ℤ'_ : ℤ' → ℤ' → ℤ'
-- Exercise:
m +ℤ' n = {!!}
```

The simplest non-trivial type involving a path constructor is the
*circle* `S¹`{.Agda}, so named because it contains a point
`base`{.Agda} and a path `loop`{.Agda} which goes from `base`{.Agda}
to `base`{.Agda}, forming a circle.

```
data S¹ : Type where
  base : S¹
  loop : base ≡ base
```

There's not a huge amount we can do with `S¹`{.Agda} without
technology from later sections, but we can at least describe its
recursion principle. The recursion principle for the circle states
that to produce a function `S¹ → A` for any type `A`, we need to
specify a point `a : A`, and a loop `l : a ≡ a` starting and ending at
that point. In other words, we need to draw a circle in the type `A`.

```
S¹-rec : {ℓ : Level} {A : Type ℓ} (a : A) (l : a ≡ a)
       → S¹ → A
S¹-rec a l base = a
S¹-rec a l (loop i) = l i
```


## Paths in Pair and Function Types

Now we can ask what paths look like in various types. Inductive data
types (like `Bool`{.Agda}) will be covered in detail in Lecture 2-3.
Let's begin with something easier: what is a path in a pair type? It's
a pair of paths of the components!

To prove these, remember that any path in `A` is secretly a function
`I → A` so, ignoring the endpoints, the first exercise is asking for a
function `(I → A) × (I → B) → (I → A × B)`. It should be easy to come
up with such a function, and it turns out that this obvious definition
has the correct endpoints.

```
≡-× : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
-- Exercise:
≡-× (p , q) = {!!}

≡-fst : {x y : A × B} → x ≡ y → (fst x ≡ fst y)
-- Exercise:
≡-fst p = {!!}

≡-snd : {x y : A × B} → x ≡ y → (snd x ≡ snd y)
-- Exercise:
≡-snd p = {!!}
```

Similarly, what is a path in a function type? It is a function landing
in paths! This is the principle of "function extensionality": to say that `f`
is the same as `g` means that, for all `x`, `f x` is the same as `g x`.

::: Aside:
The `≡` constructor has low precedence, so `f x ≡ f y` means `(f x) ≡
(f y)`, and not something weird like `f (x ≡ f) y`.
:::

```
funExt : {f g : A → B}
  → ((x : A) → f x ≡ g x)
  → f ≡ g
-- Exercise:
funExt f = {!!}

funExt⁻ : {f g : A → B}
  → f ≡ g
  → ((x : A) → f x ≡ g x)
-- Exercise:
funExt⁻ p = {!!}
```

Try proving function extensionality for binary functions.

```
funExt2 : {f g : A → B → C}
       (p : (x : A) (y : B) → f x y ≡ g x y)
       → f ≡ g
-- Exercise:
funExt2 p i x y = {!!}
```


## Paths over Paths

A path in a type `A` is a function `p : I → A` with fixed endpoints `x
: A` and `y : A`. But what if `A` is itself a path of types `A : I →
Type`? Then we consider dependent functions `p : (i : I) → A i` with
fixed endpoints `x : A i0` and `y : A i`; these are called "paths over
the path `A`", or sometimes simply "pathovers". The name for this in
Agda is `PathP`{.Agda}, for "Path (over) P(ath)". This is a built-in
notion, like `≡`{.Agda} itself.

```
_ : (A : I → Type) (x : A i0) (y : A i1) → Type
_ = PathP
```

Similarly to paths, if we have `p : PathP A x y`, then `p i0 = x` and
`p i1 = y` always, regardless of how `p` is defined.

In fact, the type `Path A x y` is defined in terms of `PathP`, where
the path of types happens to be constant at the type `A`. This is just
like how non-dependent functions `A → B` are exactly dependent
functions `(x : A) → B` where `B` happens to be a constant type and
not depend on `x`.

```
myPath : (A : Type) (x : A) (y : A) → Type
-- Exercise: (easy)
myPath A x y = {!!}
```

We can now clear up a lingering question from the previous section. We
calculated what paths in pair and function types should be, but only
for *non-dependent* pairs and functions. It turns out `PathP`{.Agda}
is exactly the missing ingredient for describing paths in these types.

Function extensionality can be extended to *dependent* function
extensionality. The body of the definition is identical to
`funExt`{.Agda} but the type improves:

```
-- Exercise:
depFunExt : {B : A → I → Type}
     {f : (x : A) → B x i0} {g : (x : A) → B x i1}
     → ((x : A) → PathP {!!} {!!} {!!})
     → PathP {!!} f g

depFunExt p i x = p x i
```

Similarly, we can upgrade `congNonDep`{.Agda} to appy to dependent
functions:

```
-- Exercise:
cong : {B : A → Type ℓ₂} {x y : A}
          (f : (a : A) → B a)
        → (p : x ≡ y)
        → PathP {!!} {!!} {!!}

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

Here we are going to use an "anonymous module", to collect the
parameters that are identical between the two exercises
`ΣPathP→PathPΣ'`{.Agda} and `PathPΣ→ΣPathP'`{.Agda}.

```
module _ {A : Type ℓ} {B : A → Type ℓ₂}
  {x y : Σ[ a ∈ A ] B a}
  where

  -- Exercise:
  ΣPathP→PathPΣ' : Σ[ p ∈ (fst x ≡ fst y) ] PathP {!!} {!!} {!!}
            → x ≡ y

  ΣPathP→PathPΣ' eq i = fst eq i , snd eq i

  -- Exercise:
  PathPΣ→ΣPathP' : x ≡ y
            → Σ[ p ∈ (fst x ≡ fst y) ] PathP {!!} {!!} {!!}

  PathPΣ→ΣPathP' eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
```

There is a second possible notion of dependency: it could be that the
types `A` and `B` themselves are paths of types, that is, they depend
on an element of `I`. Again, the actual definitions are identical; but
their types become more powerful.

```
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₂}
  {x : Σ[ a ∈ A i0 ] B i0 a} {y : Σ[ a ∈ A i1 ] B i1 a}
  where

  -- Exercise:
  ΣPathP→PathPΣ : Σ[ p ∈ PathP {!!} {!!} {!!} ] PathP {!!} {!!} {!!}
            → PathP (λ i → Σ[ a ∈ A i ] B i a) x y

  ΣPathP→PathPΣ eq i = fst eq i , snd eq i

  -- Exercise:
  ΣPathP→ΣPathP : PathP (λ i → Σ[ a ∈ A i ] B i a) x y
            → Σ[ p ∈ PathP {!!} {!!} {!!} ] PathP {!!} {!!} {!!}

  PathPΣ→ΣPathP eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
```

mvrnote: text
```
S¹-ind : {ℓ : Level} {A : S¹ → Type ℓ} (a : A base) (l : PathP (λ i → A (loop i)) a a)
       → (s : S¹) → A s
S¹-ind a l base = a
S¹-ind a l (loop i) = l i
```


## Squares

A path in type of paths is a function with shape `a : I → (I → A)`.
This is equivalent via `curry×`{.Agda} to a function `I × I → A`, and
we can therefore think of paths-between-paths as functions of two
interval variables `i` and `j`. Though we can't use the elements of
`I` as data and so don't let ourselves actually form the type `I × I`,
we can nevertheless think of a function of two interval variables
corresponding to a square.

            a-1
       a01 - - - > a11
        ^           ^
    a0- |           | a1-      ^
        |           |        j |
       a00 — — — > a10         ∙ — >
            a-0                  i

We will see a square like this as a path from left to right between
the paths `a0-` and `a1-`. However, these don't have the same type;
observing the endpoints, we see that `a0- : a00 ≡ a01` and `a1- : a10
≡ a11`. Using the other two paths `a-0` and `a-1`, we may constract a
path of types that continuously transforms from the type of `a0-` to
the type of `a1-`, as we sweep from left to right.

```
SquareSweep : {A : Type ℓ} {a00 a01 a10 a11 : A}
        → (a-0 : a00 ≡ a10) (a-1 : a01 ≡ a11)
        → I → Type ℓ
SquareSweep a-0 a-1 i = a-0 i ≡ a-1 i
```

Plugging in the endpoints of `I`, we indeed see that

* `(SquareSweep a-0 a-1 i0) = (a00 ≡ a01)` and
* `(SquareSweep a-0 a-1 i1) = (a10 ≡ a11)`

by definition.

We want to say that the square is somehow an element of this
continuously varying path type. With `PathP`{.Agda}, we can do exactly
this, and define the type of squares as paths over the continuously
varying path `SquareSweep`{.Agda}:

```
Square : {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (a0- : a00 ≡ a01)
       → (a1- : a10 ≡ a11)
       → (a-0 : a00 ≡ a10)
       → (a-1 : a01 ≡ a11)
       → Type ℓ
Square a0- a1- a-0 a-1 = PathP (SquareSweep a-0 a-1) a0- a1-
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
`A`. But just as we can upgrade `Path`{.Agda} to `PathP`{.Agda} where
the type `A` can vary over the path, we can upgrade `Square`{.Agda} to
`SquareP`{.Agda} where the type can vary over the square.

We will fill in the definition, but try filling in the types of the
sides of the square.

```
-- Exercise:
SquareP :
     (A : I → I → Type ℓ)
     {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
     (a₀- : ?)
     (a₁- : ?)
     (a-₀ : ?)
     (a-₁ : ?)
     → Type ℓ

SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (a₀- : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (a₁- : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a-₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
  (a-₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀- a₁- a-₀ a-₁ = PathP (λ i → PathP (λ j → A i j) (a-₀ i) (a-₁ i)) a₀- a₁-
```

For some practice thinking with squares, write down the function that
flips a square along the diagonal:


             a-1                          a1-           
       a01 - - - > a11              a10 - - - > a11   
        ^           ^                ^           ^    
    a0- |           | a1-   ~~>  a-0 |           | a-1
        |           |                |           |    
       a00 — — — > a10              a00 — — — > a01   
             a-0                          a0-         

```
flipSquare : {A : Type ℓ}            
             {a₀₀ a₀₁ a₁₀ a₁₁ : A }
             (a₀- : PathP (λ j → A) a₀₀ a₀₁)
             (a₁- : PathP (λ j → A) a₁₀ a₁₁)
             (a-₀ : PathP (λ i → A) a₀₀ a₁₀)
             (a-₁ : PathP (λ i → A) a₀₁ a₁₁)
           → Square a₀- a₁- a-₀ a-₁
           → Square a-₀ a-₁ a₀- a₁-
-- Exercise:
flipSquare a₀- a₁- a-₀ a-₁ s = {!!}
```

Once you've figured this out, try to define a similar function
`flipSquareP`{.Agda}, where the type now varies over the square. Here,
the trick is not so much the definition itself --- it will be the same
as `flipSquare`{.Agda} --- but rather the type signature.

```
flipSquareP : 
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (a₀- : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (a₁- : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a-₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
  (a-₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  -- Exercise:
  → SquareP {!A!} a₀- a₁- a-₀ a-₁
  → SquareP {!!} a-₀ a-₁ a₀- a₁-
-- Exercise:
flipSquareP A a₀- a₁- a-₀ a-₁ s = {!!}
```

mvrnote: text

             line1
         pt  - - - > pt
          ^           ^
    line2 |           | line2    ^
          |           |        j |
         pt  — — — > pt          ∙ — >
             line1                 i

```
data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : Square line2 line2 line1 line1
```

```
t2c : Torus → S¹ × S¹
t2c point        = ( base , base )
t2c (line1 i)    = ( loop i , base )
t2c (line2 j)    = ( base , loop j )
t2c (square i j) = ( loop i , loop j )

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl
```


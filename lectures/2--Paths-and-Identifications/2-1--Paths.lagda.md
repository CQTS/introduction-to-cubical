```
module 2--Paths-and-Identifications.2-1--Paths where
```

# Lecture 2-1: Paths

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
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
represent equality in another inductive type, like ``Bool`` or
``ℕ``. It would be tedious to have to define equality separately
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
variable (via ``curry×`` and ``uncurry×``). Using this idea,
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
special "type" ``I`` to act as our type theoretic version of the
unit interval $[0, 1]$, equipped with two elements `i0 : I` and `i1 :
I`, which act as the endpoints $0$ and $1$. A *path* `x ≡ y` from `x`
to `y` of type `A` will then be a function `h : I → A` where `h(i0) =
x` and `h(i1) = y`. Agda will remember the endpoints of our paths, so
that when we later evaluate the path at `i0`, we get `x` exactly, and
similarly for `i1` and `y`.

However, somewhat similarly to ``Level``, the type ``I`` is
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
``I``, which is good, since an element of ``I`` isn't meant
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

```
notnot : (x : Bool) → not (not x) ≡ x
notnot true  = refl
notnot false = refl

or-zeroˡ : (x : Bool) → true or x ≡ true
or-zeroˡ _ = refl

or-zeroʳ : (x : Bool) → x or true ≡ true
or-zeroʳ false = refl
or-zeroʳ true  = refl

or-identityˡ : (x : Bool) → false or x ≡ x
or-identityˡ _ = refl

or-identityʳ : (x : Bool) → x or false ≡ x
or-identityʳ false = refl
or-identityʳ true  = refl

or-comm : (x y : Bool) → x or y ≡ y or x
or-comm false false = refl
or-comm false true  = refl
or-comm true  false = refl
or-comm true  true  = refl

or-assoc : (x y z : Bool) → x or (y or z) ≡ (x or y) or z
or-assoc false y z = refl
or-assoc true  y z = refl

or-idem : (x : Bool) → x or x ≡ x
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
congE : (f : A → B)
  → x ≡ y
  → f x ≡ f y
congE f p i = f (p i)
```

This is the principle that says that doing the same thing to both
sides of an equation gives an equal result --- very useful!

```
congE-bin : (f : A → B → C) {a a' : A} {b b' : B}
         → a ≡ a'
         → b ≡ b'
         → (f a b) ≡ (f a' b')
-- Exercise:
congE-bin f p q = {!!}

congE-∘ : (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → congE (g ∘ f) p ≡ congE g (congE f p)
-- Exercise:
congE-∘ f g p = {!!}
```

``congE`` is simple but on its own already has some useful
applications! Namely: the constructors for inductive types are
injective, so if the same constructor is used on both ends of the
path, we can peel them off.

```
suc-inj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
-- Exercise: (Hint: use `predℕ`!)
suc-inj p = {!!}

inl-inj : {x y : A} → Path (A ⊎ B) (inl x) (inl y) → x ≡ y
inl-inj {A = A} {x = x} p = congE uninl p
  where
    uninl : A ⊎ B → A
    uninl (inl a) = a
    uninl (inr _) = x

inr-inj : {x y : B} → Path (A ⊎ B) (inr x) (inr y) → x ≡ y
-- Exercise:
inr-inj {B = B} {x = x} p = {!!}
```


## Inductive Types with Path Constructors

Alright, ``refl`` is great but can we get our hands on any other
paths? One way is to define inductive types that have path
constructors. (These are often called "Higher Inductive Types" or
HITs.)

Our first use of a path constructor is a more symmetrical version of
the integers. Remember that the definition of ``ℤ`` we gave back
in Lecture 1-2 is a little janky --- we have to treat the negatives
and the positives asymmetrically, assigning ``zero`` to the
``pos`` side and shifting the ``negsuc`` side down by one.
Now that we have paths, we can define a symmetric version of the
integers --- as long as we add in a path between "positive 0" and
"negative 0" to make them the same!

```
data ℤˢ : Type where
  posˢ : ℕ → ℤˢ
  negˢ : ℕ → ℤˢ
  posˢzero≡negˢzero : posˢ zero ≡ negˢ zero
```

Arithmetic using these integers is easier to reasona about than the
version involving ``negsuc``. First, here's the successor
function which you should compare to ``sucℤ``.

```
sucℤˢ : ℤˢ → ℤˢ
sucℤˢ (posˢ x) = posˢ (suc x)
sucℤˢ (negˢ zero) = posˢ (suc zero)
sucℤˢ (negˢ (suc x)) = negˢ x
sucℤˢ (posˢzero≡negˢzero i) = posˢ (suc zero)
```

On positive integers, we use the ordinary successor of the enclosed
natural number. On negative integers, we check if the natural number
is zero, and if so, give back positive one, and use the enclosed
predecessor otherwise.

Notice that we have defined what the function does on zero twice! Once
as `posˢ zero`, and again as `negˢ zero`. The final case for the path
constructor forces us to check that we give the same answer both
times. And indeed we do, so that final case can be defined by the
constant path at `posˢ (suc zero)`.

It is easy to convert backwards and fowards between these integers and
the original ones.

```
ℤˢ→ℤ : ℤˢ → ℤ
-- Exercise:
ℤˢ→ℤ z = {!!}

ℤ→ℤˢ : ℤ → ℤˢ
-- Exercise:
ℤ→ℤˢ z = {!!}
```

Complete the definition of addition.

```
predℤˢ : ℤˢ → ℤˢ
-- Exercise:
predℤˢ z = {!!}

_+ℤˢ_ : ℤˢ → ℤˢ → ℤˢ
-- Exercise:
m +ℤˢ n = {!!}
```

The simplest non-trivial type involving a path constructor is the
*circle* ``S¹``, so named because it contains a point
``base`` and a path ``loop`` which goes from ``base``
to ``base``, forming a circle.

```
data S¹ : Type where
  base : S¹
  loop : base ≡ base
```

There's not a huge amount we can do with ``S¹`` without
technology from later lectures, but we can at least describe its
recursion principle. The recursion principle for the circle states
that to produce a function `S¹ → A` for any type `A`, we need to
specify a point `a : A`, and a loop `l : a ≡ a` starting and ending at
that point. In other words, we need to draw a circle in the type `A`.

```
S¹-rec : {A : Type ℓ} (a : A) (l : a ≡ a)
       → S¹ → A
S¹-rec a l base = a
S¹-rec a l (loop i) = l i
```


## Paths in Pair and Function Types

Now we can ask what paths look like in various types. Inductive data
types (like ``Bool``) will be covered in detail in Lecture 2-3.
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
the path `A`", or sometimes simply "path-overs". The name for this in
Agda is ``PathP``, for "Path (over) P(ath)". This is a built-in
notion, like ``≡`` itself.

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
for *non-dependent* pairs and functions. It turns out ``PathP``
is exactly the missing ingredient for describing paths in these types.

Function extensionality can be extended to *dependent* function
extensionality. The body of the definition is identical to
``funExt`` but the type improves:

```
-- Exercise:
depFunExt : {B : A → I → Type}
     {f : (x : A) → B x i0} {g : (x : A) → B x i1}
     → ((x : A) → PathP {!!} {!!} {!!})
     → PathP {!!} f g

depFunExt p i x = p x i
```

Similarly, we can upgrade ``congE`` to appy to dependent
functions:

```
-- Exercise:
cong : {B : A → Type ℓ₂} {x y : A}
          (f : (a : A) → B a)
        → (p : x ≡ y)
        → PathP {!!} {!!} {!!}

cong f p i = f (p i)
```

Now for dependent pairs. There are actually two places dependency
could show up here. The first is the obvious one, when `B` depends on
`A`. The definitions are the same as in the non-dependent case, so try
to fill in the parameters to the ``PathP`` type.

Here we are going to use an "anonymous module", to collect the
parameters that are identical between the two exercises
``ΣPathP→PathPΣ'`` and ``PathPΣ→ΣPathP'``.

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
on an element of ``I``. Again, the actual definitions are
identical; but their types become more powerful.

```
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₂}
  {x : Σ[ a ∈ A i0 ] B i0 a} {y : Σ[ a ∈ A i1 ] B i1 a}
  where

  -- Exercise:
  ΣPathP→PathPΣ : Σ[ p ∈ PathP {!!} {!!} {!!} ] PathP {!!} {!!} {!!}
         → PathP (λ i → Σ[ a ∈ A i ] B i a) x y

  ΣPathP→PathPΣ eq i = fst eq i , snd eq i

  -- Exercise:
  PathPΣ→ΣPathP : PathP (λ i → Σ[ a ∈ A i ] B i a) x y
         → Σ[ p ∈ PathP {!!} {!!} {!!} ] PathP {!!} {!!} {!!}

  PathPΣ→ΣPathP eq = (λ i → fst (eq i)) , (λ i → snd (eq i))
```

Path-overs are also what is required to describe the induction
principle of the circle; the upgraded version of ``S¹-rec`` for
dependent functions. If we have a type family over the circle rather
than just a single type, the provided point must be an element of the
type family at ``base``, and the loop is a path from that point
to itself, lying over the path of types `A ∘ loop`.

```
S¹-ind : {A : S¹ → Type ℓ}
       → (a : A base)
       → (l : PathP (λ i → A (loop i)) a a)
       → (s : S¹) → A s
S¹-ind a l base = a
S¹-ind a l (loop i) = l i
```


## Squares

A path in type of paths is a function with shape `a : I → (I → A)`.
This is equivalent via ``curry×`` to a function `I × I → A`, and
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
        → (I → Type ℓ)
SquareSweep a-0 a-1 i = a-0 i ≡ a-1 i
```

Plugging in the endpoints of `I`, we indeed see that

* `(SquareSweep a-0 a-1 i0) = (a00 ≡ a01)` and
* `(SquareSweep a-0 a-1 i1) = (a10 ≡ a11)`

by definition.

We want to say that the square is somehow an element of this
continuously varying path type. With ``PathP``, we can do exactly
this, and define the type of squares as paths over the continuously
varying path ``SquareSweep``:

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
`A`. But just as we can upgrade ``Path`` to ``PathP`` where
the type `A` can vary over the path, we can upgrade ``Square`` to
``SquareP`` where the type can vary over the square.

We will fill in the definition, but try filling in the types of the
sides of the square.

```
-- Exercise:
SquareP :
     (A : I → I → Type ℓ)
     {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
     (a₀- : {!!})
     (a₁- : {!!})
     (a-₀ : {!!})
     (a-₁ : {!!})
     → Type ℓ

SquareP A a₀- a₁- a-₀ a-₁ = PathP (λ i → PathP (λ j → A i j) (a-₀ i) (a-₁ i)) a₀- a₁-
```

For some practice thinking with squares, write a version of
``cong`` that applies to squares.
```
congSquare : (f : A → B)
           → {a₀₀ a₀₁ a₁₀ a₁₁ : A}
           → {a₀- : Path A a₀₀ a₀₁}
           → {a₁- : Path A a₁₀ a₁₁}
           → {a-₀ : Path A a₀₀ a₁₀}
           → {a-₁ : Path A a₀₁ a₁₁}
           → Square a₀- a₁- a-₀ a-₁
           → Square (cong f a₀-) (cong f a₁-) (cong f a-₀) (cong f a-₁)
-- Exercise:
congSquare f s = {!!}
```

And write down the function that flips a square along the diagonal:


             a-1                          a1-           
       a01 - - - > a11              a10 - - - > a11   
        ^           ^                ^           ^    
    a0- |           | a1-   ~~>  a-0 |           | a-1
        |           |                |           |    
       a00 — — — > a10              a00 — — — > a01   
             a-0                          a0-         

```
flipSquare : {a₀₀ a₀₁ a₁₀ a₁₁ : A }
             (a₀- : Path A a₀₀ a₀₁)
             (a₁- : Path A a₁₀ a₁₁)
             (a-₀ : Path A a₀₀ a₁₀)
             (a-₁ : Path A a₀₁ a₁₁)
           → Square a₀- a₁- a-₀ a-₁
           → Square a-₀ a-₁ a₀- a₁-
-- Exercise:
flipSquare a₀- a₁- a-₀ a-₁ s = {!!}
```

Once you've figured this out, try to define a similar function
``flipSquareP``, where the type now varies over the square. Here,
the trick is not so much the definition itself --- it will be the same
as ``flipSquare`` --- but rather the type signature.

```
flipSquareP : 
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (a₀- : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (a₁- : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a-₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
  (a-₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  -- Exercise:
  → SquareP {!!} a₀- a₁- a-₀ a-₁
  → SquareP {!!} a-₀ a-₁ a₀- a₁-

flipSquareP A a₀- a₁- a-₀ a-₁ s = λ i j → s j i
```

Agda also provides us the ability to define inductive types that
contain path-of-path constructors. Here's a nice example: the torus,
which consists a basepoint, two circles connected to that basepoint,
and a square region with sides as follows:

             line1
         pt  - - - > pt
          ^           ^
    line2 |           | line2    ^
          |           |        j |
         pt  — — — > pt          ∙ — >
             line1                 i

mvrnote: this will really need some pictures

```
data Torus : Type where
  torus-base  : Torus
  torus-loop1  : torus-base ≡ torus-base
  torus-loop2  : torus-base ≡ torus-base
  torus-square : Square torus-loop2 torus-loop2 torus-loop1 torus-loop1
```

Topologically, the torus is equal to the cartesian product of two
circles. We can prove this directly! mvrnote: refer to the picture

```
Torus→S¹×S¹ : Torus → S¹ × S¹
-- Exercise:
Torus→S¹×S¹ t = {!!}

S¹×S¹→Torus : S¹ × S¹ → Torus
-- Exercise:
S¹×S¹→Torus c = {!!}
```

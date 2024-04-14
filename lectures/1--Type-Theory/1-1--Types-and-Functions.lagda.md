```
module 1--Type-Theory.1-1--Types-and-Functions where
```

# Lecture 1-1: Types and Functions

<!--
```
open import Library.Prelude
```
-->

A type theory is a formal system for keeping track of what type of
thing every mathematical object is. This idea is familiar from
computer science; since everything in a computer is stored as a chunk
of bits, it is important to record what any given chunk of bits is
supposed to mean. Is this chunk of bits meant to be a number or a
piece of text? Or a program that can be run? Since all of these things
are ultimately stored as a bunch of bits, if we don't keep track of
how we were supposed to use them we run the risk of accidentally
considering some text as a very large number and adding it to another
number.

When we say that some piece of data is "meant" to be a number, what we
mean is that we intend to use it like a number -- maybe add or
multiply it with other numbers. A type theory, then, is a formal
language for keeping track of our intentions with data.

In this course, we will focus on mathematical aspects of type
theory. With an expressive enough language for describing our
intentions with data, it turns out that we can formalize essentially
all of mathematics. The basic work of mathematics --- defining
concepts and structures, constructing examples, stating and proving
propositions --- can all be expressed in the language of the
particular type theory we will be using: a variant of Martin-Löf type
theory called Cubical Type Theory.

Agda is a program that acts as a "proof assistant" for writing down
arguments in Cubical Type Theory. The file you are reading right now
is a literate Agda file: all the lines between the triple backticks
are actual Agda code that can be loaded by pressing `C-c C-l`.

The basic statement of any type theory is "this `a` is an `A`" or
"this thing `a` has that type `A`". We write this symbolically using a
colon `a : A`. In the expression `a : A`, the `A` is the "type" and
the `a` is the "element".

The vast majority of an Agda file consists of definitions, which have
two parts. First, a declaration that gives an unused identifier
together with the type that we want it to have. Second, a list of
equations that define the actual meaning of the identifier.

```
three : ℕ      --- This line declares that `three` is a natural number.
three = 3      --- This line defines `three` to be the actual number 3
```

In this case there is only one equation defining the element, but we
will soon see examples with more than one.

## Functions

In the next lecture, we'll see how to define specific types of data
like Booleans and numbers (like the number `3` we used in the above
definition). For this lecture, we'll focus on the most fundamental
concepts in type theory: functions and pairs.

A function `f : A → B` may be thought of in two ways:

1. An operation which takes an element `x : A` as input and produces
   an element `f(x) : B` as output.
2. An element `f(x) : B` whose definition involves a variable element
  `x : A`.

Here is our first Agda function: a function of type `ℕ → ℕ`{.Agda} that
doubles the natural number that you give it.

```
double : ℕ → ℕ
double x = 2 · x
```

Functions are defined by placing a fresh variable name to the left of
the `=` sign, which can then be used on the right. So here,
`double`{.Agda} accepts `x` as input and produces `2 · x` as output.

We can apply a function `f : A → B` to an argument `a : A` by writing
`f a : B` --- note the lack of parentheses around `a`!

```
hopefullySix : ℕ
hopefullySix = double three
```

We can get Agda to actually compute this definition, by hitting `C-c
C-n` (for "normalise") and typing `hopefullySix`{.Agda}.

We can write functions of multiple arguments by listing them to the
left of the `=` sign.

```
cents : ℕ → ℕ → ℕ → ℕ → ℕ
cents quarters dimes nickels pennies =
  (25 · quarters) + (10 · dimes) + (5 · nickels) + pennies

hopefullyOneDollar : ℕ
hopefullyOneDollar = cents 3 1 2 5
```

(Agda doesn't care if the definition spans multiple lines, as long as
there is some whitespace at the beginning of the line so that it
doesn't look like the start of a new definition.)

For your very first exercise, try writing a function of two arguments
that ignores the second argument and just gives back the first.

```
constℕ : ℕ → ℕ → ℕ
-- Exercise:
constℕ a b = {!!}
```

To do this, you can place your cursor in the hole and type your
attempted definition. (Hint: it's `a`). To ask Agda to accept it, type
`C-c C-space`, which is the keybinding for "give solution". If Agda is
satisfied that your definition fits, it will replace the hole with
what you have written.

So far our inputs and outputs have all been `ℕ`{.Agda}, but there is no
particular reason for this. We can even write functions that take
other functions as input. Here's a very simple example: accept a
function and an argument as input, and give back the result of
applying the function to the argument.

```
applyℕ : (ℕ → ℕ) → ℕ → ℕ
applyℕ f a = f a
```

In fact, we have secretly written a couple of functions that give
another function as output already. Agda reads the type of `constℕ`
above as

```
constℕ' : ℕ → (ℕ → ℕ)
constℕ' a b = a
```

How do we make sense of this? The functions `constℕ`{.Agda} and
`constℕ'`{.Agda} are literally identical to Agda, but the way we have
written them suggests two different ways we can think of functions of
multiple arguments:

* The function `constℕ`{.Agda} is a function of two variables `a` and `b`,
  yielding first.
* The function `constℕ'`{.Agda} is a function of a single variable `a`,
  returning the function `ℕ → ℕ` which takes `b : ℕ`, ignores it, and
  yields `a`.

We can use some additional Agda syntax to this second perspective
explicit:

```
constℕ'' : ℕ → (ℕ → ℕ)
constℕ'' a = λ (b : ℕ) → a
```

This is now a function of a *single* argument, that gives back a
function of type `ℕ → ℕ`. This general technique of describing
functions of multiple arguments via functions that return functions is
called "currying", after the computer scientist Haskell Curry (whose
name is also immortalized in the programming language Haskell).

The syntax `λ (x : A) → t` defines the function `A → B` which sends
`x` to `t`, where `t : B` is some expression potentially involving
`x`. The `λ` (Greek letter lambda) comes to us from Church's
λ-calculus, an early formal system for defining functions intended as
a model of general computability.

To write the `λ` symbol in Emacs or VSCode, type `\Gl` or `\lambda`.
If you ever forget how to write a symbol, there are ways to look it
up. In Emacs, place your cursor over the symbol and type `M-x
describe-char`. A window will pop up with details about the symbol:
the line beginning with `to input:` is what you want. In VSCode, use
the command `C-x C-=`. A textbox will appear that you can paste the
character into. Test it out on the symbol here: `⊗`.

The functions we have written so far are all specialised to work with
elements of the type `ℕ`{.Agda}. For example, we can write the "identity"
(i.e. do-nothing) function

```
idfunℕ : ℕ → ℕ
idfunℕ x = x
```

Writing this to only work for `ℕ` is overly restrictive, after all, we
don't actually use any properties of `ℕ` on the right-hand side.
Instead, we can have an identity function `A → A` that works for any
type `A` at all.

```
idfunE : (A : Type) → (A → A)
idfunE A x = x
```

Let's understand why the type of `idfunE`{.Agda} is more complicated than just
`idfunE : A → A`. The extra bit "`(A : Type) →`" is there because the
type `A → A` itself involves a variable: the type `A`. This `A` is
then an additional argument to the function, so it also appears on the
left of the `=` in the definition on the next line.

If we think in terms of currying, `idfunE`{.Agda} is a function of a
variable `A`, which is a type. When applied, `idfunE A` gives
back the identity function `A → A` for that type.

`constℕ`{.Agda} and `applyℕ`{.Agda} can be similarly generalised:
```
constE : (A : Type) → (B : Type) → A → B → A
constE A B a b = a

applyE : (A : Type) → (B : Type) → (A → B) → A → B
applyE A B f a = f a
```

## Implicit Arguments

There is one more trick before we reach the true definition of `id`,
`const` and `apply` that we will actually use. It is necessary for
these functions to have arguments that determine the types that should
be used in the output, but in some sense they are redundant. For
example, the `x` argument to `id` is of type `A`, so if we know `x`,
we know what `A` had to be.

Agda lets us make these arguments *implicit*, so they are reconstructed
from the other arguments. This is done by surrounding them with curly
braces rather than parentheses:

```
idfunI : {A : Type} → A → A
idfunI x = x

constI : {A : Type} → {B : Type} → A → B → A
constI a b = a

applyI : {A : Type} → {B : Type} → (A → B) → A → B
applyI f a = f a
```

This saves a huge amount of typing in the long run. Agda will complain
if it cannot reconstruct an implicit argument from the other arguments
you provide when applying a function.

We can compose functions by applying the second to the result of the
first. Try implementing it:

```
composeI : {A : Type} {B : Type} {C : Type}
    → (B → C)
    → (A → B)
    → (A → C)
-- Exercise:
composeI g f = {!!}
```

Try implementing the following functions.

```
flipI : {A B C : Type}
     → (A → B → C)
     → (B → A → C)
-- Exercise:
flipI = {!!}

-- Should use the provided function on the argument twice.
apply-twice : {A : Type}
     → (A → A)
     → A
     → A
-- Exercise:
apply-twice = {!!}
```

Pen and paper exercise: Check that `f ∘ id` and `id ∘ f` act the same
as `f` on any argument. In Part 2 of this course, we'll be able to
express that fact in theory and have Agda verify that it is correct!

## Pair types

The other basic type forming operation we have is the type of pairs.
The pair of the elements `a : A` and `b : B` is written `(a , b)`,
which is an element of the type `A × B`. The space before the comma is
necessary, or Agda thinks you are referring to a variable called "`a,`".

```
pair× : {A : Type} → {B : Type} → A → B → (A × B)
pair× a b = (a , b)
```

To use a pair, we can "project out" the first and second components
using the in-built functions `fst`{.Agda} and `snd`{.Agda}.

```
my-fst× : {A : Type} → {B : Type} → (A × B) → A
my-fst× p = fst p

my-snd× : {A : Type} → {B : Type} → (A × B) → B
my-snd× p = snd p
```

These can be chained together to work with nested pairs.

```
triple× : {A B C : Type} → A → B → C → ((A × B) × C)
triple× a b c = ((a , b) , c)

my-fst×× : {A B C : Type} → ((A × B) × C) → A
my-fst×× t = fst (fst t)

my-snd×× : {A B C : Type} → ((A × B) × C) → B
my-snd×× t = snd (fst t)

my-trd×× : {A B C : Type} → ((A × B) × C) → C
my-trd×× t = snd t
```

When the argument to the function is a nested pair type, it can be
annoying chaining together `fst`{.Agda}s and `snd`{.Agda}s to get at
the components. Agda allows us to use "pattern matching" on an
argument to decompose it into its components all at once. This also
lets us give the components more meaningful names, rather than having
to remember exactly which combination of `fst`{.Agda} and `snd`{.Agda} is needed
to reach the thing we want.

```
×-assoc-toI : {A B C : Type} → (A × (B × C)) → ((A × B) × C)
×-assoc-toI (a , (b , c)) = (a , b) , c

×-assoc-froI : {A B C : Type} → ((A × B) × C) → (A × (B × C))
-- Exercise:
×-assoc-froI = {!!}

×-commI : {A B C : Type} → (A × B) → (B × A)
-- Exercise:
×-commI = {!!}
```

With pair types we can make precise the currying and uncurrying idea
from earlier, going from a function with a single pair argument to a
function that returns a function, and vice versa.

```
curry× : {A B C : Type}
  → ((A × B) → C)
  → (A → B → C)
curry× f x y = f (x , y)

uncurry× : {A B C : Type}
  → (A → B → C)
  → ((A × B) → C)
uncurry× f p = f (fst p) (snd p)
```
Remember that `((A × B) → C) → (A → (B → C))` is the same as `((A × B)
→ C) → A → B → C`, and so in the definition of `curry×`{.Agda}, we can accept
three arguments `f : ((A × B) → C)`, `x : A` and `y : B`, and produce
a `C` on the right-hand side.

There is nothing special about functions of two arguments here, try
writing similar functions for a function of three arguments. Agda can
help us a lot here. For `curry3`{.Agda}, we know that the right-hand
side is going to be `f` applied to some argument. Place `f` in the
hole, and type `C-c C-r` to "refine" the hole: Agda will accept `f`
and create a new hole for the argument. Agda also knows that the
argument to `f` will have to be a pair, and so hitting `C-c C-r` again
will split the argument into the pair of two new holes. Similarly, for
`uncurry3`{.Agda}, writing `f` and refining will give three new holes, one
for each argument that `f` expects.

```
curry3 : {A B C D : Type}
  → (((A × B) × C) → D)
  → (A → B → C → D)
-- Exercise:
curry3 f x y z = {!!}

uncurry3 : {A B C D : Type}
  → (A → B → C → D)
  → (((A × B) × C) → D)
-- Exercise:
uncurry3 f t = {!!}
```


## Dependent Types and Dependent Functions

We can think of a function `f : A → B` as an element `f x : B` that
depends on an element `x : A` for its definition. What sets Agda (and
other "dependently typed" languages) apart from ordinary functional
programming is that we can have types that depend on elements for
their definition.

As a slightly mathematical example, suppose $n ∈ ℕ$ is a number and
consider the set $\{m : ℕ ∣ ∃ i. m = n · i\}$ of numbers which are
multiples of than $n$. We can define this as an Agda type
`MultiplesOf`{.Agda}. (Don't worry about the actual definition for
now.)

```
MultiplesOf : ℕ → Type
MultiplesOf n = Σ[ m ∈ ℕ ] Σ[ i ∈ ℕ ] m ≡ i · n
```

Notice that the elements that the type `MultiplesOf n`{.Agda} has will *depend*
on the value of `n` that we choose: different choices will yield
genuinely different sets of numbers, and generally speaking an element
of `MultiplesOf n₁` will not also be an element of `MultiplesOf n₂`
for some other `n₂`. In other words, we are describing a function from
natural numbers to types, i.e. a function `ℕ → Type`. A function of
this shape (`A → Type`) is often called a "type family over `A`".

Dependent types let us make our functions more powerful. For ordinary
functions `A → B`, the output type of the function is always an
element of `B`. If instead of a single type `B : Type` we have a type
family `B : A → Type`, Agda allows us to form the type of *dependent*
functions `(x : A) → B x` which send an element `x : A` to an element
`f x : B x`.

As a first example, we can refine our `double`{.Agda} function a
little. Sure, the result is always an element of `ℕ`{.Agda}, but it is
also always a multiple of the input:

```
doubleDep : (n : ℕ) → MultiplesOf n
doubleDep n = double n , 2 , (λ i → 2 · n)
```

(Again, don't worry about the actual definition for now.)

```
tenAsMultiple : MultiplesOf 5
tenAsMultiple = doubleDep 5
```

Non-dependent functions are a special case of dependent functions,
where the type family that we use is constantly the same type.

```
ConstantlyℕFamily : ℕ → Type
ConstantlyℕFamily n = ℕ -- `n` is ignored

doubleNonDep : (n : ℕ) → ConstantlyℕFamily n
doubleNonDep = double
```

Most of the functions in this file have actully been dependent
function types already! In `idfunE : (A : Type) → A → A`, the type `A → A`
depends on `A : Type`, so this is a dependent function using the
type family

```
idfun-family : Type → Type
idfun-family A = A → A
```

That is, when we provide `idfunE`{.Agda} with some type `A`, the resulting
function we get back is the identity function for that specific type
`A`. Notice that `idfun-family`{.Agda} is a type family over `Type`{.Agda}: nothing
stops us from having `Type`{.Agda} on both sides of the function.

Here is function composition, where the two functions involved are
allowed to be dependent.

```
depCompose :
      {A : Type}
      {B : A → Type}
      {C : (x : A) → B x → Type}

      (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
depCompose g f = λ x → g (f x)
```

The type of `depCompose`{.Agda} is a little gnarly, but you should see
that the actual definition of the function is exactly the same as
before. You should work through the type of each of the intermediate
pieces in `λ x → g (f x)`:

* `x` has type `A`, so
* `f x` has type `B x`, so
* `g (f x)` has type `C x (f x)`

## Dependent Pairs

Just as function types generalise to dependent function types, pair
types generalise to dependent pair types, where the type of the second
component is allowed to depend on the value in the first component. If
`A : Type` and `B : A → Type`, then the dependent pair type is written
`Σ[ x ∈ A ] B x`.

Dependent pair types are used just like the non-dependent pair types:
we use the comma `,` to construct a pair and `fst` and `snd` to
deconstruct a pair. Only the types of these things have changed:

```
my-pairΣ : {A : Type} → {B : A → Type}
         → (x : A)
         → B x
         → Σ[ x ∈ A ] B x
my-pairΣ a b = (a , b)

my-fstΣ : {A : Type} → {B : A → Type}
        → Σ[ x ∈ A ] B x
        → A
my-fstΣ p = fst p

my-sndΣ : {A : Type} → {B : A → Type}
        → (p : Σ[ x ∈ A ] B x)
        → B (fst p)
my-sndΣ p = snd p
```

The type of `snd`{.Agda} is a little complicated! When we form `snd p`, the
type of the result depends on the thing that is in the first
component. That is, the type of `snd p` is the value of the input type
family `B : A → Type` when evaluated at `fst p`. To express that in
the type of `my-sndΣ`{.Agda}, we have to use a dependent function so that `B
(fst p)` can refer to the pair `p`.

`curry×`{.Agda} and `uncurry×`{.Agda} can be generalised to work with dependent pairs
and functions.

```
uncurry : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((x : A) → (y : B x) → C x y)
  → (p : Σ[ x ∈ A ] B x) → C (fst p) (snd p)
uncurry f p = f (fst p) (snd p)

curry : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((p : Σ[ x ∈ A ] B x) → C (fst p) (snd p))
  → (x : A) → (y : B x) → C x y
curry f x y = f (x , y)
```

Finally in this section, we have the "universal mapping property" of
pairs: functions `C → A × B` correspond exactly with pairs of
functions `C → A` and `C → B`.

```
×-ump : {A B C : Type}
      → (C → A)
      → (C → B)
      → (C → A × B)
-- Exercise:
×-ump = {!!}
```

We will have a lot to say about universal properties in this course.


## Universe Levels

We might ask what the type of `Type`{.Agda} itself is. One option is to just
say `Type : Type`, this is what Haskell does. This works fine for
practical programming but leads to logical contradictions thanks to
some "Russell-style" paradoxes. (Search up "Girard's paradox" if you
are curious!)

For this reason, Agda allows us to specify "universe levels", usually
written `ℓ`, that stratify types into a heirarchy. `Type`{.Agda} on its own
is secretly `Type₀` the type of all types at level zero. But `Type₀`
itself does not live at level zero, but one step up: `Type₀ : Type₁`.
Similarly, `Type₁ : Type₂`, and so on. In general, the universe `Type
ℓ` lives in universe `Type (ℓ-suc ℓ)` for any level `ℓ`, where `ℓ-suc`
is a built in function that increments a level by one.

When we prove general facts about functions, we might want to apply
them in situations where the type `Type`{.Agda} is involved, or maybe with
things in higher universe levels still. This is accomplished by having
them accept types of any universe level. So as an example, for the
final time, here is a definition of the identity function on any type,
living in any universe.

```
idfun : {ℓ : Level} (A : Type ℓ) → A → A
idfun A x = x
```

`Level`{.Agda} is the magic, built-in collection of universe levels and can't
be mixed together with actual types. For each `ℓ : Level`, there is a
corresponding universe of that level called `Type ℓ`.

Similarly, we can upgrade some of the functions we have defined into
their final, most general versions.

```
const : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A → B → A
const a b = a

apply : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → B x) → (x : A) → B x
apply f a = f a

flip : {ℓ₁ ℓ₂ ℓ₃ : Level}
       {A : Type ℓ₁}
       {B : Type ℓ₂}
       {C : A → B → Type ℓ₃}
     → ((x : A) (y : B) → C x y)
     → ((y : B) (x : A) → C x y)
flip f y x = f x y
```

All the built-in type constructors we have seen, like `×`{.Agda}, are
functions that take types as arguments and produce types as output,
and are written to work with types at any universe level. If you type
`C-c C-d` and enter `_×_`, you should see that it has type

```
_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_ = _×_
```

In this case, `×`{.Agda} accepts types in any universe and gives back
a type in the largest of those two universes. Above we make a
"definition" with name `_`; this signals to Agda to check the type of
what we provide, but then throw away the result. We will use this to
demonstrate the type of some expression without having to invent a new
name for it.

Here is our very final definition of function composition, where all
the types involved might live in different universes.

```
_∘_ : {ℓ ℓ' ℓ'' : Level}
      {A : Type ℓ}
      {B : A → Type ℓ'}
      {C : (x : A) → B x → Type ℓ''}

      (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
```

Agda considers definitions with underscores specially, and lets us
refer to such a definition in two ways: either the normal way, that
is, `_∘_ g f`, or with the arguments replacing the underscores: `g ∘
f`. We will use infix operators like this whenever it is closer to
normal mathematical practice, like this composition operator or
arithmetical operators `+`{.Agda}, `·`{.Agda}, etc.

This final line specifies that the `_∘_`{.Agda} operator associates to
the right, so that `h ∘ g ∘ f` means `h ∘ (g ∘ f)`.

```
infixr 9 _∘_
```

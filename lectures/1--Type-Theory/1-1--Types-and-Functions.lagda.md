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
three : ℕ      -- This line declares that `three` is a natural number.
three = 3      -- This line defines `three` to be the actual number 3
               -- (Eveything after a double dash in a line is a comment.)
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

As in other functional languages, these are functions in the
mathematical sense: providing the same input always yields the same
output, and a function is not allowed to cause side-effects like
changing the state of memory or performing IO.

Here is our first Agda function: a function of type ``ℕ → ℕ``
that doubles the natural number that you give it.

```
double : ℕ → ℕ
double x = 2 · x
```

Functions are defined by placing a fresh variable name to the left of
the `=` sign, which can then be used on the right. So here,
``double`` accepts `x` as input and produces `2 · x` as output.

We can apply a function `f : A → B` to an argument `a : A` by writing
`f a : B` --- note the lack of parentheses around `a`!

```
hopefullySix : ℕ
hopefullySix = double three
```

We can get Agda to actually compute this definition, by hitting `C-c
C-n` (for "normalise") and typing ``hopefullySix``.

We can define functions of multiple arguments by listing them to the
left of the `=` sign. For the type of the function, we chain together
`ℕ →`s to indicate that we are accepting several natural numbers, one
at a time. (We'll come back to this in a minute.)

```
cents : ℕ → ℕ → ℕ → ℕ → ℕ
cents quarters dimes nickels pennies =
  (25 · quarters) + (10 · dimes) + (5 · nickels) + pennies

hopefullyOneDollar : ℕ
hopefullyOneDollar = cents 3 1 2 5
```

(Agda doesn't care if the definition spans multiple lines, as long as
there is some whitespace at the beginning of the line so that it
doesn't look like the start of a different definition.)

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

(Aside: at the time of writing, MacOS may capture `C-space` and open
the spotlight search bar. If you are encountering this problem, use
`C-c C-r` for "refine" as a replacement.)

In this case, you could provide `b` as a solution, and Agda would
also accept it! Agda can only check that your code is *type-correct*, and
not that it actually does what you want. For most future exercises
however, the types involved will be very constraining and you will
struggle to provide any definition other than the intended one.

So far our inputs and outputs have all been ``ℕ``, but there is no
particular reason for this. We can even write functions that take
other functions as input. Here's a very simple example: accept a
function and an argument as input, and give back the result of
applying the function to the argument.

```
applyℕ : (ℕ → ℕ) → ℕ → ℕ
applyℕ f a = f a
```

In fact, we have secretly written a couple of functions that give
another function as output already. For example, the `→` operator on
types associates to the right, so Agda actually reads the above type
of ``constℕ`` as

```
constℕ' : ℕ → (ℕ → ℕ)
constℕ' a b = a
```

How do we make sense of this? The definitions of the functions
``constℕ`` and ``constℕ'`` are literally identical to Agda,
but the way we have written them suggests two different ways we can
think of functions of multiple arguments:

* The function ``constℕ`` is a function of two variables `a` and `b`,
  yielding first.
* The function ``constℕ'`` is a function of a single variable `a`,
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
a model of general computability. Notice also that we are re-using the
`→` symbol: in `A → B` this symbol forms a new type out of `A` and `B`
and in `λ (x : A) → t` this introduces a function given a term `t`
with a free variable `x`.

To write the `λ` symbol in Emacs or VSCode, type `\Gl` or `\lambda`.
We will use a lot of Unicode symbols in these notes, and at the bottom
of each lecture you will find a dictionary of the symbols used and how
to input them. mvrnote: make sure we do this!

::: Aside:
If you ever forget how to write a symbol, there are ways to look it
up. In Emacs, place your cursor over the symbol and type `M-x
describe-char`. A window will pop up with details about the symbol:
the line beginning with `to input:` is what you want. In VSCode, use
the command `C-x C-=`. A text box will appear that you can paste the
character into. Test it out on the symbol here: `⊗`.
:::

Let's test out this perspective on functions, by defining another
function in two different ways.

mvrnote: use `add-one` or something instead?

This should use the provided function
`f` twice, so that `apply-twiceℕ₁ double n` multiplies `n` by 4.

```
apply-twiceℕ₁ : (ℕ → ℕ) → ℕ → ℕ
-- Exercise:
apply-twiceℕ₁ f x = {!!}
```

Now write it again but using a `λ` on the right of the `=`, in the
same style as ``constℕ''``.

```
apply-twiceℕ₂ : (ℕ → ℕ) → (ℕ → ℕ)
-- Exercise:
apply-twiceℕ₂ f = {!!}
```

Finally, a slightly more complicated example with more than one
argument. This function should hand the provided arguments to `f` in
the opposite order. For the version using `λ`, you will have to use
`λ` twice.

```
flipℕ₁ : (ℕ → ℕ → ℕ)
       →  ℕ → ℕ → ℕ
-- Exercise:
flipℕ₁ f x y = {!!}

flipℕ₂ : (ℕ → ℕ → ℕ)
       → (ℕ → ℕ → ℕ)
-- Exercise:
flipℕ₂ f = {!!}
```

In the future, you should feel free to add arguments to the left of
the `=` sign if that will lead to a nicer definition. But be warned:
you will have to re-load the file via `C-c C-l` in order for Agda to
pick up the new arguments, otherwise you will get errors claiming that
the new variables are "not in scope".


## Generic Definitions

The functions we have written so far are all specialised to work with
elements of the type ``ℕ``. For example, we have the "identity"
(i.e. do-nothing) function

```
idfunℕ : ℕ → ℕ
idfunℕ x = x
```

Writing this to only work for ``ℕ`` is overly restrictive, after
all, we don't actually use any properties of ``ℕ`` on the
right-hand side. Instead, we can have an identity function `A → A`
that works for any type `A` at all.

```
idfunE : (A : Type) → (A → A)
idfunE A x = x
```

Let's understand why the type of ``idfunE`` is more complicated
than just `idfunE : A → A`. The extra bit "`(A : Type) →`" is there
because `A → A` itself involves a variable: the type `A`. This `A` is
then an additional argument to the function, so it also appears on the
left of the `=` in the definition on the next line.

If we think in terms of currying, ``idfunE`` is a function of a
variable `A`, which is a type. When applied, `idfunE A` gives
back the identity function `A → A` for that type.

Like every variable in Agda, `A` itself has a type, in this case the
type ``Type``. This is a type whose elements themselves are
types, things like this are often called "type universes".

We can reconstruct ``idfunℕ`` back by providing `ℕ` to
``idfunE``:

```
idfunℕ₂ : ℕ → ℕ
idfunℕ₂ = idfunE ℕ
```

And we can similarly generalise all the functions we have defined so far.

```
constE : (A : Type) → (B : Type) → A → B → A
constE A B a b = a

applyE : (A : Type) → (B : Type) → (A → B) → A → B
applyE A B f a = f a
```

Try the following. You will have to write the argument lists yourself,
or use a bunch of `λ` on the right-hand side. Remember to include the
types as arguments now!

```
apply-twiceE : (A : Type)
     → (A → A)
     → A
     → A
-- Exercise:
apply-twiceE = {!!}

flipE : (A : Type) → (B : Type) → (C : Type)
     → (A → B → C)
     → (B → A → C)
-- Exercise:
flipE = {!!}
```

Let's do one more important example, as a way to introduce a few more
Agda hotkeys. For any three types, we can compose functions between
them:

```
composeE : (A : Type) → (B : Type) → (C : Type)
    → (B → C)
    → (A → B)
    → (A → C)
-- Exercise:
composeE A B C g f = {!!}
```

You may be able to fill this in immedidately, but try the following.
Place your cursor in the goal and type `C-c C-,`. Agda will show you
the type of the goal, in this case `A → C`, and all of the variables
you have available to construct it. Because the type of a goal is a
function, Agda knows that a `λ` expression can go here. Type `C-c C-r`
to "refine" the goal; this will automatically insert a `λ`:

```
-- composeE A B C g f = λ x → {!!}
```

Typing `C-c C-,` again, you will see that the goal is now a term of
type just `C`. We know that we can get a term of `C` by applying `g`
to something, so type `g` in the goal. Now, hit `C-c C-.`, which will
show you both the goal type (`C`), and the type of what you have
placed in the hole right now (`B → C`).

These don't line up, but Agda is clever enough to know that `g` is
still progress: if you type `C-c C-r` again to refine the goal, Agda
will accept `g` in place, and move it out of the hole.

```
-- composeE A B C g f = λ x → g {!!}
```

Now, `C-c C-,` again tells us that the goal is a term of type `B`, and
this time we can produce one using `f`. Putting `f` and hitting `C-c
C-r` again:

```
-- composeE A B C g f = λ x → g (f {!!})
```

Finally, the goal type is `A`, and we have `x` available, so we can
put `x` in the hole and type `C-c C-space` to give it.

```
-- composeE A B C g f = λ x → g (f x)
```

This is the kind of interaction you should expect to do while solving
more complicated exercises: repeatedly using `C-c C-,` to ask Agda
what it expects to see, and then using `C-c C-r` to refine the goal or
`C-c C-space` to give the solution to the goal immediately.


## Implicit Arguments

There is one more trick before we reach the true definitions of
``idfun``, ``const`` and ``apply`` that we will
actually use. For each of these functions, the type arguments are
necessary so that the function can know which types should be used in
the output, but in some sense actually specifying these arguments is
redundant. For example, the `x` argument to ``idfunE`` is of type
`A`, so if we know `x`, we also know what `A` had to be.

Agda lets us make these arguments *implicit* so they are automatically
reconstructed from the other arguments. Implicit arguments are
annotated by surrounding them with curly braces rather than
parentheses:

```
idfunI : {A : Type} → A → A
idfunI x = x
```

In the actual definitions, we no longer write the types as arguments
on the left-hand side of the `=` sign. Formally, those arguments are
still there: we are still defining a function that accepts some types
as arguments: these arguments are just invisible in the code. This
saves a huge amount of typing in the long run.

One more time, we can get ``idfunℕ`` by having Agda realise what
the type `A` has to be:

```
idfunℕ₃ : ℕ → ℕ
idfunℕ₃ = idfunI
```

Agda will complain if it cannot reconstruct an implicit argument from
the other arguments you provide, though if we choose carefully which
arguments to make implicit this will rarely happen. We can force it to
use a particular implicit argument by providing it also surrounded by
curly braces.

```
idfunℕ₄ : ℕ → ℕ
idfunℕ₄ = idfunI {A = ℕ}
```

Here is round 3 of defining our favourite functions:

```
constI : {A : Type} → {B : Type} → A → B → A
constI a b = a

applyI : {A : Type} → {B : Type} → (A → B) → A → B
applyI f a = f a

composeI : {A : Type} → {B : Type} → {C : Type}
    → (B → C)
    → (A → B)
    → (A → C)
-- Exercise:
composeI = {!!}

flipI : {A : Type} → {B : Type} → {C : Type}
     → (A → B → C)
     → (B → A → C)
-- Exercise:
flipI = {!!}

apply-twice : {A : Type}
     → (A → A)
     → A
     → A
-- Exercise:
apply-twice = {!!}
```


## Pair types

The other basic type forming operation we have is the type of pairs.
The pair of the elements `a : A` and `b : B` is written `(a , b)`,
which is an element of the type `A × B`. The space before the comma in
a pair is required: without it Agda thinks you are referring to a
variable called `a,` (which almost certainly doesn't exist).

```
my-pair× : {A : Type} → {B : Type} → A → B → (A × B)
my-pair× a b = (a , b)
```

To use a pair, we can "project" the first and second components
using the in-built functions ``fst`` and ``snd``.

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

::: Aside:
Agda allows us to specify arguments with identical types all at once,
which we have used above to write `{A B C : Type} → ...` rather than
`{A : Type} → {B : Type} → {C : Type} → ...` everywhere.
:::

When the argument to a function is a nested pair type like this, it
can be annoying to chain together ``fst``s and ``snd``s to
get at the component that we actually want to use. Agda allows us to
use "pattern matching" on an argument to decompose it into its
components all at once. This also lets us give the components more
meaningful names, rather than having to remember exactly which
combination of ``fst`` and ``snd`` is needed to reach the
thing we want. Here are some functions that use this style.

```
×-assoc-toI : {A B C : Type} → (A × (B × C)) → ((A × B) × C)
×-assoc-toI (a , (b , c)) = (a , b) , c

×-assoc-froI : {A B C : Type} → ((A × B) × C) → (A × (B × C))
-- Exercise: (Remember to put a spaces around the comma in a pair!)
×-assoc-froI = {!!}

×-commI : {A B C : Type} → (A × B) → (B × A)
-- Exercise:
×-commI = {!!}

×-mapI : {A B C D : Type}
       → (A → B)
       → (C → D)
       → (A × C → B × D)
-- Exercise:
×-mapI = {!!}
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
→ C) → A → B → C`, and so in the definition of ``curry×``, we can accept
three arguments `f : ((A × B) → C)`, `x : A` and `y : B`, and produce
a `C` on the right-hand side.

There is nothing special about functions of two arguments here, try
writing similar functions for a function of three arguments. Agda can
help us a lot here, so use refine (`C-c C-r`) liberally when
completing these. For ``uncurry3``, writing `f` and refining will
give three new holes, one for each argument that `f` expects.

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
uncurry3 f ((x , y) , z) = {!!}
```


## Dependent Types and Dependent Functions

We can think of a function `f : A → B` as an element `f x : B` that
depends on an element `x : A` for its definition. What sets Agda (and
other "dependently typed" languages) apart from ordinary functional
programming languages is that we can have types that depend on
elements for their definition.

As a slightly mathematical example, suppose $n ∈ ℕ$ is a number and
consider the set $\{m : ℕ ∣ ∃ i. m = n · i\}$ of numbers which are
multiples of $n$. We can define this as an Agda type
``MultiplesOf``. (Don't worry about the actual definition for
now.)

```
MultiplesOf : ℕ → Type
MultiplesOf n = Σ[ m ∈ ℕ ] Σ[ i ∈ ℕ ] m ≡ i · n
```

Notice that the elements ``MultiplesOf n`` has will *depend* on
the value of `n` that we choose: different choices will yield
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

As a first example, we can refine our ``double`` function a
little. Sure, the result is always an element of ``ℕ``, but we
can record the fact that the reuslt is always a multiple of the input:

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
ConstantℕFamily : ℕ → Type
ConstantℕFamily n = ℕ -- `n` is ignored

doubleNonDep : (n : ℕ) → ConstantℕFamily n
doubleNonDep = double
```

Most of the functions in this file have actually been dependent
function types already! In `idfunE : (A : Type) → A → A`, the type `A → A`
depends on `A : Type`, so this is a dependent function where the target is the
type family

```
idfun-family : Type → Type
idfun-family A = A → A
```

That is, when we provide ``idfunE`` with some type `A`, the
resulting function we get back is the identity function for that
specific type `A`. Notice that ``idfun-family`` is a type family
over ``Type``: nothing stops us from having ``Type`` on both
sides of the `→`.

Here is function composition again, where the two functions involved
are now allowed to be dependent.

```
depCompose :
      {A : Type}
    → {B : A → Type}
    → {C : (x : A) → B x → Type}

    → (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
depCompose g f = λ x → g (f x)
```

The type of ``depCompose`` is a little gnarly, but you should see
that the actual *definition* is exactly the same as before. You should
work through the type of each of the intermediate pieces in `λ x → g
(f x)`:

* `x` has type `A`, so
* `f x` has type `B x`, so
* `g (f x)` has type `C x (f x)`


## Dependent Pairs

Just as function types generalise to dependent function types, pair
types generalise to dependent pair types where the type of the second
component is allowed to depend on the value in the first component. If
`A : Type` and `B : A → Type`, then the dependent pair type is written
`Σ[ x ∈ A ] B x`. These types are often called Sigma-types, hence the
symbol `Σ`.

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

The type of ``snd`` is a little complicated! When we form `snd p`, the
type of the result depends on what is in the first
component. That is, the type of `snd p` is the value of the input type
family `B : A → Type` when evaluated at `fst p`. To express that in
the type of ``my-sndΣ``, we have to use a dependent function so that `B
(fst p)` can refer to the pair `p`.

Try writing the types for a dependently-typed version of
``×-mapI``. All you need to do is replace the `×` from the
previous definition with an appropriate `Σ`-type.

```
-- Exercise:
Σ-mapI : {A : Type} {B : A → Type} {A' : Type} {B' : A' → Type}
         → (f : A → A')
         → (g : (a : A) → B a → B' (f a))
         → {!!} → {!!}

Σ-mapI f g (a , b) = (f a , g a b)
```

Notice that the type of `g` has changed from the definition
``×-mapI``. Rather than giving a single funciton `B → B'`, we
have to now give a function `B a → B' (f a)` for each possible `a :
A`.

``curry×`` and ``uncurry×`` can be generalised to work with
dependent pairs and functions.

```
uncurryI : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((x : A) → (y : B x) → C x y)
  → (p : Σ[ x ∈ A ] B x) → C (fst p) (snd p)
uncurryI f p = f (fst p) (snd p)

curryI : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((p : Σ[ x ∈ A ] B x) → C (fst p) (snd p))
  → (x : A) → (y : B x) → C x y
curryI f x y = f (x , y)
```

Like `×`, we can chain `Σ` together however we like. The dependent
types do make this a little more complicated though!

Suppose we start with dependent types `A : Type`, `B : A → Type` and
`C : (x : A) → B x → Type`. Suppose we have an `a : A` in mind. Then,
we can use a Σ-type to form the type `Σ[ b ∈ B a ] C a b`. This is a
type family that works for any `a : A`, so we can use another Σ-type
to give giving `Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b` in total. This is the
type that corresponds to the non-dependent triple `A × (B × C)`.

We can also start pairing on the other side, so using the first two
types to form `Σ[ a ∈ A ] B a`. To form another Σ-type, we now need a
type family `Σ[ a ∈ A ] B a → Type`, which doesn't match the type of
`C`. But it's easy to fix that mismatch, by projecting the components
where we need them: `Σ[ p ∈ Σ[ a ∈ A ] B a ] C (fst p) (snd p)`. This
corresponds to the non-dependent triple `(A × B) × C)`.

As with non-dependent pairs, these two types are interconvertible.

```
-- Exercise:
Σ-assoc-toI : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
     → {!!} → {!!}

Σ-assoc-toI (a , (b , c)) = (a , b) , c

-- Exercise:
Σ-assoc-froI : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
     → {!!} → {!!}

Σ-assoc-froI ((a , b) , c) = a , (b , c)
```

## Unicode Dictionary

| Char       | Input          |
|------------|----------------|
| ×          | \times         |
| →          | \-> or \to     |
| ℕ          | \bN            |
| ·          | \cdot          |
| λ          | \Gl or \lambda |
| ₁, ₂, etc. | \_1, \_2, etc. |
| Σ          | \GS or \Sigma  |
| ∈          | \in            |
| ℓ          | \ell           |
| ∘          | \circ          |

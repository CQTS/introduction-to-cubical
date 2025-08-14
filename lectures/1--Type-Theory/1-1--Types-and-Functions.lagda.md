<!--
```
module 1--Type-Theory.1-1--Types-and-Functions where

open import Library.Prelude
```
-->


# Lecture 1-1: Types and Functions

A type theory is a formal system for keeping track of what type of
thing every mathematical object is. This idea is familiar from
computer science; since everything in a computer is stored as a chunk
of bits, it is important to record what any given chunk of bits is
supposed to mean. Is this chunk of bits meant to be a number or a
piece of text? Or a program that can be run? If we don't keep track of
how we are supposed to use some chunk of bits, we run the risk of
accidentally considering some text as a very large number and adding
it to another number.

When we say that some piece of data is "meant" to be a number, what we
mean is that we intend to use it like a number: use it to perform some
arithmetic, or control how many times we repeat a process, etc. A
type theory, then, is a formal language for keeping track of our
intentions with data.

In this course, we will focus on mathematical aspects of type
theory. With an expressive enough language for describing our
intentions with data, it turns out that we can formalize essentially
all of mathematics. The basic work of mathematics --- defining
concepts and structures, constructing examples, stating and proving
propositions --- can all be expressed in the language of the
particular type theory we will be using: a variant of [Martin-Löf type
theory] called *Cubical Type Theory*.

[Martin-Löf type theory]: https://plato.stanford.edu/entries/type-theory-intuitionistic/

To keep us honest, we will be using a program called Agda to check
that the definitions we make in Cubical Type Theory are sensible. Agda
is a so-called "proof assistant" that can not only verify our work,
but help us craft our proofs and arguments in the first place. The
file you are reading right now uses a format called "literate Agda",
which interleaves commentary and code: all the lines between the
triple backticks are actual Agda code that can be loaded, which you
should try now by pressing `C-c C-l`.

::: Aside:
Agda is a programming language, but is unlike most programming
languages used by software engineers. The most similar languages used
in practice are "functional" languages like OCaml, Racket, and
especially Haskell. (Agda is written in Haskell and its syntax has
some similarities.)
:::

The basic statement of any type theory is a claim of the form "this
`a` is a thing of type `A`". We write this symbolically using a colon,
so `a : A`. In the expression `a : A`, the `a` is an "element" of the
type `A`.

The vast majority of any Agda file consists of definitions, which
always have two parts. First, a declaration that specifies the name of
the thing we are defining together with the type it is going to have.
Second, a list of equations that define the actual content of the
definition.

```
three : ℕ   -- This line declares that `three` is a natural number.
three = 3   -- This line defines `three` to be the actual number 3
            -- (Everything after a double dash in a line is a comment.)
```

In this case the definition only requires one equation to be complete,
but we will soon see examples with more than one.

In Lecture 1-2, we'll see how to define specific types of data like
the Booleans and natural numbers (such as the number `3` we used in
the above definition). For this lecture, we'll focus on the most
fundamental concepts in type theory: functions types and pair types.


## Function Types

A function `f : A → B` may be thought of in (at least) two ways:

1. An operation which takes an element `x : A` as input and produces
   an element `f(x) : B` as output.
2. An element `f(x) : B` whose definition involves a variable element
  `x : A`.

As in other functional programming languages, these are functions in
the mathematical sense: providing the same input always yields the
same output, and a function is not allowed to cause side-effects like
changing the state of memory or performing IO.

Here is our first Agda function: a function called ``double`` that has
type `ℕ → ℕ`, which doubles the natural number that you give it.

```
double : ℕ → ℕ
double x = 2 · x
```

Functions are defined by placing a variable name to the left of the
`=` sign, which can then be used on the right. So here, ``double``
accepts `x` as input and produces `2 · x` as output. (We have provided
the actual definition of the multiplication of natural numbers ``·``
behind the scenes.)

We can apply a function `f : A → B` to an argument `a : A` by writing
`f a : B` --- note the lack of parentheses around `a`!

```
hopefully-six : ℕ
hopefully-six = double 3
```

We can get Agda to actually compute this definition by pressing `C-c
C-n` (for "normalise") and typing ``hopefully-six``. Just to make
absolutely sure, the following helper will test that Agda considers
the expressions ``hopefully-six`` and `6` identical.

```
_ = test-identical hopefully-six 6
```

Here we are witnessing the *computation rule* for functions. When
``double`` is applied to an argument, that argument is substituted in
for corresponding variable wherever it appears in the definition of
the function. So in this case, `double 3` computes to `2 · 3`, which
is indeed `6`. (And `2 · 3` is computed in just the same way,
substituting `2` and `3` into our behind-the-scenes definition of
``·``.)

Functions of multiple arguments can be defined by giving multiple
variable names to the left of the `=` sign. For the type of the
function, we chain together "`ℕ →`" to indicate that we are accepting
several natural numbers, one at a time. (We'll come back to this in a
minute.)

```
cents : ℕ → ℕ → ℕ → ℕ → ℕ
cents quarters dimes nickels pennies =
  (25 · quarters) + (10 · dimes) + (5 · nickels) + pennies

hopefully-one-dollar : ℕ
hopefully-one-dollar = cents 3 1 2 5

_ = test-identical hopefully-one-dollar 100
```

::: Aside:
Agda doesn't care if the definition spans multiple lines so long as
there is some whitespace at the beginning of the line so that it
doesn't look like the start of a different definition.
:::

For your very first exercise, try writing a function of two arguments
that ignores the second argument and just gives back the first.

```
constℕ : ℕ → ℕ → ℕ
-- Exercise:
constℕ a b = {!!}
```

The area contained within the curly brackets is known as a *hole*, a
gap in the code where some expression is still required to make the
definition complete. To fill in the hole, place your cursor between
the brackets and enter your attempted definition. (Hint: it's `a`). To
ask Agda to accept it, type `C-c C-space`, which is the keybinding for
"give solution". If Agda is satisfied that your definition fits, the
curly brackets will disappear and the hole will be replaced by what
you have written.

::: Caution:
At the time of writing, MacOS may capture `C-space` and open the
Spotlight search bar. If this happens to you, use `C-c C-r` for
"refine" as a replacement.
:::

In this case, you could also provide `b` as a solution, and Agda would
also accept it! Agda can only check that your code is *type-correct*, and
not that it actually does what you want. For most future exercises
however, the types involved will be very constraining and you will
struggle to provide any definition other than the intended one.

So far our inputs and outputs have all been ``ℕ``, but there is no
particular reason for this. We can even write functions that take
other functions as input. Here's a very simple example: the function
``applyℕ`` we show next accepts a function and a natural number as
input, and give back the result of applying the function to that
argument.

```
applyℕ : (ℕ → ℕ) → ℕ → ℕ
applyℕ f a = f a
```

Although we see the symbols `f a` appearing on both sides, they have
different meanings in each location. On the left, we are specifying
that the function ``applyℕ`` takes two arguments, `f` followed by `a`.
On the right, we are using the function `f` by applying it to `a`.

In fact, we have secretly written a couple of functions that give
another function as output already. For example, the `→` operator on
types associates to the right, so Agda actually reads the above type
of ``constℕ`` as

```
constℕ₂ : ℕ → (ℕ → ℕ)
constℕ₂ a b = a
```

How do we make sense of this? The definitions of the functions
``constℕ`` and ``constℕ₂`` are literally identical to Agda,
but the way we have written them suggests two different ways we can
think of functions of multiple arguments:

* The function ``constℕ`` is a function of two variables `a` and `b`,
  yielding the one.
* The function ``constℕ₂`` is a function of a single variable `a`,
  which returns a new function `ℕ → ℕ` which takes `b : ℕ`, ignores it, and
  yields the original `a`.

We can use some additional Agda syntax to this second perspective
explicit. This is known formally as λ-abstraction.

```
constℕ₃ : ℕ → (ℕ → ℕ)
constℕ₃ a = λ (b : ℕ) → a
```

In a lot of programming languages such expressions are called
*anonymous functions*, so called because the function doesn't get a
name.

The syntax `λ (x : A) → t` defines the function of type `A → B` which
sends `x` to `t`, where `t : B` is some expression potentially
involving the variable `x`. The `λ` (Greek letter lambda) comes to us
from Church's λ-calculus, an early formal system for defining
functions intended as a model of general computability. Notice also
that we are re-using the `→` symbol: in `A → B` this symbol forms a
new type out of `A` and `B`, and in `λ (x : A) → t` it introduces a
function given a term `t` with a free variable `x`.

``constℕ₃`` is now a function of a *single* argument that gives back a
function of type `ℕ → ℕ`. This general technique of describing
functions of multiple arguments via functions that return functions is
called *currying*, after the computer scientist Haskell Curry (whose
name is also immortalized in the programming language Haskell).
Currying is more than just a party trick: it can be very useful in
practice to create functions by "partially applying" a function this
way.

Providing the type of the argument is optional in a λ-abstraction,
so we could just as well have written:

```
constℕ₄ : ℕ → (ℕ → ℕ)
constℕ₄ a = λ b → a
```

Agda knows from the type of ``constℕ₄`` that the type of `b` must be
``ℕ``.

To input the `λ` symbol in Emacs or VSCode yourself, use `\Gl` (for
"Greek l"), or `\lam`, or if you like, `\lambda`. And by the way, you
can type the arrow `→` by typing `\to`. We will use a lot of Unicode
symbols in these notes, and it will be useful to know how to type them
quickly! The file `UNICODE_DICITONARY.md` contains all the symbols we
use and how to input them.

::: Aside:
For any of the Unicode symbols in these notes, you can use your editor
to lookup how they are entered in Agda-mode. In Emacs, place your
cursor over the symbol and type `M-x describe-char`. A window will pop
up with details about the symbol: the line beginning with `to input:`
is what you want. In VSCode, use the command `C-x C-=`. A text box
will appear that you can paste the character into. Test it out on the
symbol here: `⊗`.
:::

Let's test out this perspective on functions by defining another
function in these two different ways. Try writing a function that adds
one to a natural number, where the argument is accepted to the left of
the `=` symbol. As before, place your cursor in the goal, type your
definition, and press `C-c C-space` to give it to Agda.

```
add-one₁ : ℕ → ℕ
-- Exercise:
add-one₁ x = {!!}
```

Now write it again but using a λ-abstraction on the right of the
`=`. You can give the type of the argument explicitly, or let Agda
figure it out itself, to your taste.

```
add-one₂ : ℕ → ℕ
-- Exercise:
add-one₂ = {!!}
```

When applied to an argument, a function defined by λ-abstraction
computes in exactly the same way as an ordinary definition: the
argument is substituted in for the variable wherever it appears.

```
_ = test-identical 
  ((λ (x : ℕ) → x + 1) three)
  (three + 1)
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

::: Aside:
We've broken the type declarations over multiple lines. This is fine
by Agda, as long as the subsequent lines begin with some whitespace.
:::

::: Aside:
In the future, you should feel free to add arguments to the left of
the `=` sign if that will lead to a nicer definition. But be warned:
you will have to re-load the file via `C-c C-l` in order for Agda to
pick up the new arguments, otherwise you will get errors claiming that
the new variables are "not in scope".
:::

Having λ-abstraction available exposes a new concern. From any
function `f : ℕ → ℕ` (or really any function between any two types),
we can define a new function `ℕ → ℕ` which accepts a `ℕ` as input, and
then immediately applies `f` to that input. Really, this a
λ-abstraction version of ``applyℕ`` from above.

```
applyℕ₂ : (ℕ → ℕ) → ℕ → ℕ
applyℕ₂ f = λ x → f x
```

And there's nothing stopping us from repeating this process to produce
more and more functions `ℕ → ℕ`:

    f  ~>  (λ x → f x)  ~>  (λ y → (λ x → f x) y)  ~>  ...

The *uniqueness principle* for functions expresses that any function
is identical to its expanded version that uses a `λ` in this way. So
in fact, all these functions are equal.

```
_ = test-identical double   (λ (x : ℕ) → double x)
_ = test-identical add-one₁ (λ (x : ℕ) → add-one₁ x)

_ = test-identical double   (λ (y : ℕ) → (λ (x : ℕ) → double x) y)
_ = test-identical add-one₁ (λ (y : ℕ) → (λ (x : ℕ) → add-one₁ x) y)
```

This shouldn't be too surprising. If we apply `(λ x → f x)` to some
argument `n`, first we substitute in for `x`, giving `f n`, which is
exactly what we get if we apply `f` to `n` directly.


## Generic Definitions

The functions we have written so far are all specialised to work with
elements of the type ``ℕ``. For example, we have the *identity*
(i.e. do-nothing) function

```
idfunℕ : ℕ → ℕ
idfunℕ x = x
```

Writing this to only work for ``ℕ`` is overly restrictive, after
all, we don't actually use any properties of ``ℕ`` on the
right-hand side. Instead, we can define an identity function `A → A`
that works for any type `A` at all.

```
idfunᵉ : (A : Type) → (A → A)
idfunᵉ A x = x
```

Let's understand why the type of ``idfunᵉ`` is more complicated
than just `idfunᵉ : A → A`. The extra bit "`(A : Type) →`" is there
because `A → A` itself involves a variable: the type `A`. This `A` is
then an additional argument to the function, so it also appears on the
left of the `=` in the definition on the next line.

If we think in terms of currying, ``idfunᵉ`` is a function of a
variable `A`, which is a type. When applied, `idfunᵉ A` gives
back the identity function `A → A` for that type.

Like every variable in Agda, `A` itself has a type, in this case the
type ``Type``. This is a type whose elements themselves are types,
typically these are *type universes*. We will have more to say about
them in Lecture 1-3.

We can reconstruct ``idfunℕ`` back by providing `ℕ` to ``idfunᵉ``:

```
idfunℕ₂ : ℕ → ℕ
idfunℕ₂ = idfunᵉ ℕ
```

And we can similarly generalise all the functions we have defined so far.

```
constᵉ : (A : Type) → (B : Type) → A → B → A
constᵉ A B a b = a

applyᵉ : (A : Type) → (B : Type) → (A → B) → A → B
applyᵉ A B f a = f a
```

::: Aside:
This idea of accepting a type as an argument to a function is similar
to but not quite the same as "parametric polymorphism", which you may
have seen in other programming languages. In a typical language with
polymorphism, one can make generic definitions but there is a strict
separation between the world of types and the world of elements. In a
fully "dependently typed" language like Agda, types can be passed
around and used like any other function argument.
:::

Try the following. You will have to either write the argument lists
yourself, or use a bunch of `λ` on the right-hand side. Remember to
include the types in your list of arguments now!

```
apply-twiceᵉ : (A : Type)
  → (A → A)
  → A
  → A
-- Exercise:
apply-twiceᵉ = {!!}

flipᵉ : (A : Type) → (B : Type) → (C : Type)
  → (A → B → C)
  → (B → A → C)
-- Exercise:
flipᵉ = {!!}
```

Let's do one more important example, as a way to introduce a few more
Agda hotkeys. For any three types, we can compose functions between
them:

```
composeᵉ : (A : Type) → (B : Type) → (C : Type)
  → (B → C)
  → (A → B)
  → (A → C)
-- Exercise:
composeᵉ A B C g f = {!!}
```

You may be able to fill this in immediately, but for some more Agda
practice try the following. Place your cursor in the goal and type
`C-c C-,`. Agda will show you the type of the goal, in this case `A →
C`, and all of the variables you have available to construct it.
Because the type of a goal is a function, Agda knows that a `λ`
expression can go here. Type `C-c C-r` to "refine" the goal; this will
automatically insert a `λ`:

    composeᵉ A B C g f = λ x → {!!}

Typing `C-c C-,` again, you will see that the goal is now a term of
type just `C`. We know that we can get a term of `C` by applying `g`
to something, so type `g` in the goal. Now, hit `C-c C-.`, which will
show you both the goal type (`C`), and the type of what you have
placed in the hole right now (`B → C`).

These don't line up, but Agda is clever enough to know that `g` is
still progress: if you type `C-c C-r` again to refine the goal, Agda
will accept `g` in place, and move it out of the hole.

    composeᵉ A B C g f = λ x → g {!!}

Now, `C-c C-,` again tells us that the goal is a term of type `B`, and
this time we can produce one using `f`. Putting `f` and hitting `C-c
C-r` again:

    composeᵉ A B C g f = λ x → g (f {!!})

Finally, the goal type is `A`, and we have `x` available, so we can
put `x` in the hole and type `C-c C-space` to give it to Agda.

    composeᵉ A B C g f = λ x → g (f x)

This is the kind of interaction you should expect to do while solving
more complicated exercises: repeatedly using `C-c C-,` to ask Agda
what it expects to see, and then using `C-c C-r` to refine the goal or
`C-c C-space` to give a solution that completes the goal immediately.


## Implicit Arguments

There are a couple more tricks before we reach the true definitions of
``idfun``, ``const`` etc. that we will actually use. For each of these
functions, the type arguments are necessary so that the function can
know which types should be used in the input and output, but in some
sense actually specifying these arguments is redundant. For example,
the `x` argument to ``idfunᵉ`` is of type `A`, so if we know what `x`
is, we also know what `A` has to be.

Agda lets us make arguments *implicit* so that they are automatically
reconstructed from the other available information. Implicit arguments are
notated by surrounding them in the type by curly braces rather than
parentheses:

```
idfunⁱ : {A : Type} → A → A
idfunⁱ x = x
```

In the actual definitions, we no longer write these implicit arguments
on the left-hand side of the `=` sign. Formally, those arguments are
still there: we are still defining a function that accepts some types
as arguments: these arguments are just invisible in the code. This is
just a cosmetic difference compared to ``idfunᵉ``, but these implicit
arguments save a huge amount of typing in the long run.

One more time, we can reproduce ``idfunℕ`` by letting Agda realise
what the type `A` has to be:

```
idfunℕ₃ : ℕ → ℕ
idfunℕ₃ = idfunⁱ
```

Agda will complain if it fails to reconstruct an implicit argument
from the other arguments you provide, though if we choose carefully
which arguments to make implicit then this will rarely happen. We can
force it to use a particular choice of implicit argument by providing
that argument surrounded by curly braces, as follows:

```
idfunℕ₄ : ℕ → ℕ
idfunℕ₄ = idfunⁱ {A = ℕ}
```

Here is round 3 of defining our favourite functions (with `ⁱ` standing
for "implicit"):

```
constⁱ : {A : Type} → {B : Type} → A → B → A
constⁱ a b = a

applyⁱ : {A : Type} → {B : Type} → (A → B) → A → B
applyⁱ f a = f a

apply-twiceⁱ : {A : Type}
  → (A → A)
  → A
  → A
-- Exercise:
apply-twiceⁱ = {!!}

flipⁱ : {A : Type} → {B : Type} → {C : Type}
  → (A → B → C)
  → (B → A → C)
-- Exercise:
flipⁱ = {!!}

composeⁱ : {A : Type} → {B : Type} → {C : Type}
  → (B → C)
  → (A → B)
  → (A → C)
-- Exercise:
composeⁱ = {!!}
```


## Pair Types

The other basic type forming operation we have is types of pairs. For
any types `A` and `B`, this is the type `A × B`. The pair of the
elements `a : A` and `b : B` is written `(a , b) : A × B`. The space
before the comma in a pair is required: without it Agda thinks you are
referring to a variable called `a,` (which almost certainly doesn't
exist).

```
my-pair× : {A : Type} → {B : Type} → A → B → (A × B)
my-pair× a b = (a , b)
```

To use a pair, we can "project" the first and second components using
the in-built ``fst`` and ``snd`` projections, which are written to the
right of the element being projected from. This should remind you of
the `.` syntax used to access members of a `struct` or object in
programming languages like C or Java.

```
my-fst× : {A : Type} → {B : Type} → (A × B) → A
my-fst× p = p .fst

my-snd× : {A : Type} → {B : Type} → (A × B) → B
my-snd× p = p .snd
```

An important characteristic of pair types is their "universal mapping
property". For pairs, this is a "mapping in" property, meaning that it
is especially easy to define maps that go *into* pair types. If we
have a function into the first component `A`, and a function
into the second component `B`, then to make a function into
the pair `A × B` we apply each function separately and pair up the result.

```
×-ump-to : {A : Type} → {B : Type} → {C : Type}
  → (C → A) → (C → B) → (C → A × B)
×-ump-to f g c = (f c , g c)
```

We can easily go back: if we have a function into a pair type, then we
can reconstruct the original functions by applying the provided
function and extracting the result from the appropriate side of the
result pair.

```
×-ump-fro : {A : Type} → {B : Type} → {C : Type} → (C → A × B) → (C → A) × (C → B)
×-ump-fro f = (λ c → f c .fst) , (λ c → f c .snd)
```

We will have a lot to say about mapping properties for the various
types we discuss in these notes.

Pair types also have a uniqueness principle. For functions, we had
that any element of a function type is identical to a λ-abstraction.
Here, any element of a pair type is identical to an actual pair. This
might seem tautological, of course `(1 , 2)` is identical to an actual
pair. But this continues to be true even when the pair is some unknown
variable: Agda considers any pair equal to the pairing of its two
components:

```
_ = λ {A : Type} {B : Type} (p : A × B) 
  → test-identical p (p .fst , p .snd)
```

To work with nested pairs, we chain together the uses of the ``,`` and
``fst``/``snd``.

```
triple× : {A B C : Type} → A → B → C → ((A × B) × C)
triple× a b c = ((a , b) , c)

my-fst×× : {A B C : Type} → ((A × B) × C) → A
my-fst×× t = t .fst .fst

my-snd×× : {A B C : Type} → ((A × B) × C) → B
my-snd×× t = t .fst .snd

my-trd×× : {A B C : Type} → ((A × B) × C) → C
my-trd×× t = t .snd

_ = λ {A B C : Type} (t : (A × B) × C) 
  → test-identical t ((t .fst .fst , t .fst .snd) , t .snd)
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
pattern-fst× : {A : Type} → {B : Type} → (A × B) → A
pattern-fst× (a , b) = a

pattern-snd× : {A : Type} → {B : Type} → (A × B) → B
pattern-snd× (a , b) = b

×-assoc-toⁱ : {A B C : Type} → A × (B × C) → (A × B) × C
×-assoc-toⁱ (a , (b , c)) = (a , b) , c

×-assoc-froⁱ : {A B C : Type} → (A × B) × C → A × (B × C)
-- Exercise: (Replace `t` with an appropriate pattern as above.)
×-assoc-froⁱ t = {!!}

×-commⁱ : {A B C : Type} → (A × B) → (B × A)
-- Exercise:
×-commⁱ p = {!!}
```

::: Caution:
Agda will complain if you accidentally include `=` inside the goal
brackets rather than outside. If you're seeing an error message like
`Not a valid pattern:`, this could be what has happened.
:::

Forming the product type is *functorial*, which means that if we have
separate functions that transform the sides of a ``×``, we can put
them together to transform the pair type directly.

```
×-mapⁱ : {A B C D : Type}
  → (A → B)
  → (C → D)
  → (A × C → B × D)
-- Exercise:
×-mapⁱ = {!!}
```

With pair types we can make precise the currying and uncurrying idea
from earlier. There are two ways to define a function that accepts two
arguments. We can either accept them together as a pair, or accept
them one at a time. Here's a helper that converts from the pair
version to the one-at-a-time version:

```
×-curry : {A B C : Type}
  → ((A × B) → C)
  → (A → B → C)
×-curry f x y = f (x , y)
```

Remember that function types are right associative:

    ((A × B) → C) → (A → (B → C))

has exactly the same meaning as

    ((A × B) → C) → A → B → C

and so in the definition of ``×-curry``, we can accept three arguments
`f : ((A × B) → C)`, `x : A` and `y : B`, and produce a `C` on the
right-hand side.

```
×-uncurry : {A B C : Type}
  → (A → B → C)
  → ((A × B) → C)
×-uncurry f p = f (p .fst) (p .snd)
```

There is nothing special about functions of two arguments here. Try
writing similar functions for a function of three arguments. Agda can
help us a lot, so we recommend using refine (`C-c C-r`) liberally when
completing these. For ``×-uncurry3``, writing `f` and refining will give
three new holes, one for each argument that `f` expects.

```
×-curry3 : {A B C D : Type}
  → (((A × B) × C) → D)
  → (A → B → C → D)
-- Exercise:
×-curry3 f x y z = {!!}

×-uncurry3 : {A B C D : Type}
  → (A → B → C → D)
  → (((A × B) × C) → D)
-- Exercise:
×-uncurry3 f ((x , y) , z) = {!!}
```


## Dependent Types and Dependent Functions

We can think of a function `f : A → B` as an element `f x : B` that
depends on an element `x : A` for its definition. What sets Agda (and
other dependently typed languages) apart from ordinary functional
programming languages is that we can have types that depend on
elements for their definition.

As a slightly contrived mathematical example, suppose $n ∈ ℕ$ is a
number and consider the set $\{m : ℕ ∣ ∃ i. m = n · i\}$ of numbers
which are multiples of $n$. We can define this as an Agda type
``Multiples-Of``. (Don't worry about the actual definition for now.)

```
Multiples-Of : ℕ → Type
Multiples-Of n = Σ[ m ∈ ℕ ] Σ[ i ∈ ℕ ] m ≡ i · n
```

Notice that the elements that `Multiples-Of n` has will *depend* on
the value of `n` that we choose: different choices will yield
genuinely different sets of numbers, and generally speaking an element
of `Multiples-Of n₁` will not also be an element of `Multiples-Of n₂`
for some other `n₂`. In other words, we are describing a function from
natural numbers to types, i.e. a function `ℕ → Type`. A function of
this shape (`A → Type`) is often called a "type family over `A`".

Dependent types let us make our functions more powerful. For ordinary
functions `A → B`, the output type of the function is always an
element of `B`. If instead of a single type `B : Type` we have a type
family `B : A → Type`, Agda allows us to form the type of *dependent*
functions `(x : A) → B x` which send an element `x : A` to an element
`f x : B x`.

As a first example, we can refine our ``double`` function to remember
more information about the result. Sure, the result is always an
element of ``ℕ``, but we can record the fact that the result is always
a multiple of the input:

```
doubleᵈ : (n : ℕ) → Multiples-Of n
doubleᵈ n = double n , 2 , (λ i → 2 · n)
```

(Again, don't worry about the actual definition for now.)

```
ten-as-multiple : Multiples-Of 5
ten-as-multiple = doubleᵈ 5
```

Non-dependent functions are a special case of dependent functions,
where the type family that we use is constantly the same type.

```
Constant-ℕ-Family : ℕ → Type
Constant-ℕ-Family n = ℕ -- `n` is ignored

doubleⁿ : (n : ℕ) → Constant-ℕ-Family n
doubleⁿ = double
```

Most of the functions in this file have actually been dependent
function types already! In `idfunᵉ : (A : Type) → (A → A)`, the type
`A → A` depends on `A : Type` to make sense at all, so this is a
dependent function where the target is the type family

```
idfun-family : Type → Type
idfun-family A = A → A
```

That is, when we provide ``idfunᵉ`` with some type `A`, the
resulting function we get back is the identity function for that
specific type `A`. Notice that ``idfun-family`` is a type family
over ``Type``: nothing stops us from having ``Type`` on both
sides of the `→`.

Here is function composition again, where the two functions involved
are now allowed to be dependent.

```
composeᵈ :
      {A : Type}
    → {B : A → Type}
    → {C : (x : A) → B x → Type}

    → (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A) → C a (f a)
composeᵈ g f = λ x → g (f x)
```

The type of ``composeᵈ`` is a little gnarly, but you should see that
the actual *definition* is exactly the same as before. You should work
through the type of each of the intermediate pieces in the expression
`λ x → g (f x)`:

* `x` has type `A`, so
* `f x` has type `B x`, so
* `g (f x)` has type `C x (f x)`


## Dependent Pairs

Just as function types generalise to dependent function types, pair
types generalise to dependent pair types where the type of the second
component is allowed to depend on the value in the first component. If
`A : Type` and `B : A → Type`, then the dependent pair type is written
`Σ[ x ∈ A ] B x`. These types are often called "sum types" hence the
symbol `Σ`.

Dependent pair types are used just like the non-dependent pair types:
we use the comma ``,`` to construct a pair and projections ``fst`` and
``snd`` to deconstruct a pair. Only the types of these things have
changed:

```
my-pairΣ : {A : Type} → {B : A → Type}
         → (x : A)
         → B x
         → Σ[ x ∈ A ] B x
my-pairΣ a b = (a , b)

my-fstΣ : {A : Type} → {B : A → Type}
        → Σ[ x ∈ A ] B x
        → A
my-fstΣ p = p .fst

my-sndΣ : {A : Type} → {B : A → Type}
        → (p : Σ[ x ∈ A ] B x)
        → B (p .fst)
my-sndΣ p = p .snd
```

The type of ``snd`` is a little complicated! When we form `p .snd`,
its type depends on what is in the first component `p .fst`. That is,
the type of `p .snd` is the value of the input type family `B : A →
Type` when evaluated at `p .fst`. To express that in the type of
``my-sndΣ``, we have to use a dependent function so that `B (p .fst)`
can refer to the pair `p`.

Try writing the types for a dependently-typed version of
``×-mapⁱ``. All you need to do is replace the `×` from the
previous definition with an appropriate `Σ`-type.

```
-- Exercise:
Σ-mapⁱ : {A : Type} {B : A → Type} {A' : Type} {B' : A' → Type}
         → (f : A → A')
         → (g : (a : A) → B a → B' (f a))
         → {!!} → {!!}

Σ-mapⁱ f g (a , b) = (f a , g a b)
```

Notice that the type of `g` has changed from the type it had back in
``×-mapⁱ``. Rather than giving a single function `B → B'`, we have to
now give a function `B a → B' (f a)` for each possible `a : A`.

``×-curry`` and ``×-uncurry`` can be generalised to work with
dependent pairs and functions. Remember that currying and uncurrying
let us switch between a function that takes a pair as an argument, and
a function that accepts those arguments one-at-a-time. Here we are
generalising that idea so that the second component of the pair is
allowed to depend on the first component. And not only that, but the
overall result type of the function is allowed to depend on the pair!

```
Σ-curryⁱ : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((p : Σ[ x ∈ A ] B x) → C (p .fst) (p .snd))
  → (x : A) → (y : B x) → C x y
Σ-curryⁱ f x y = f (x , y)

Σ-uncurryⁱ : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((x : A) → (y : B x) → C x y)
  → (p : Σ[ x ∈ A ] B x) → C (p .fst) (p .snd)
Σ-uncurryⁱ f p = f (p .fst) (p .snd)
```

Like `×`, we can chain `Σ` together however we like. The dependent
types do make this a little more complicated though!

Suppose we start with dependent types

* `A : Type`,
* `B : A → Type`, and
* `C : (x : A) → B x → Type`.

Say we already have an element `a : A` in mind. Then,
we can use a Σ-type to form the type `Σ[ b ∈ B a ] C a b`. This is a
type family that works for any `a : A`, so we can use another Σ-type
to give `Σ[ a ∈ A ] (Σ[ b ∈ B a ] C a b)` in total. This is the
type that corresponds to the non-dependent triple `A × (B × C)`.

We can also start pairing on the other side, so using the first two
types to form `Σ[ a ∈ A ] B a`. To combine this with `C` using another
`Σ`, we now need a type family `Σ[ a ∈ A ] B a → Type`, which doesn't
match the type of `C`. But it's easy to fix that mismatch by
projecting the components where we need them:

    Σ[ p ∈ (Σ[ a ∈ A ] B a) ] C (p .fst) (p .snd)

This corresponds to the non-dependent triple `(A × B) × C`.

As with non-dependent pairs, these two types are inter-convertible.

```
-- Exercise:
Σ-assoc-toⁱ : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
     → {!!}
     → {!!}

Σ-assoc-toⁱ (a , (b , c)) = (a , b) , c

-- Exercise:
Σ-assoc-froⁱ : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
     → {!!}
     → {!!}

Σ-assoc-froⁱ ((a , b) , c) = a , (b , c)
```


## References and Further Reading

* The original *[Homotopy Type Theory]* book:
  * Function types: Chapter 1.2, Chapter 1.4
  * Σ types: Chapters 1.5, 1.6
  * Formal Rules: Chapter A.2
* Egbert Rijke's *[Introduction to Homotopy Type Theory]*:
  * Function types: Chapter 2
  * Σ types: Chapter 4.6
* Martin Escardo's [Lecture Notes]: 
  * [Σ types](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmatypes)
  * [function types](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#pitypes)

[Homotopy Type Theory]: https://homotopytypetheory.org/book/
[Introduction to Homotopy Type Theory]: https://arxiv.org/abs/2212.11082
[Lecture Notes]: https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.htmlure-Notes/HoTT-UF-Agda.html

* Agda Documentation
  * [Function Types](https://agda.readthedocs.io/en/latest/language/function-types.html)
  * [Lambda Abstraction](https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html)
  * [Implicit Arguments](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html)

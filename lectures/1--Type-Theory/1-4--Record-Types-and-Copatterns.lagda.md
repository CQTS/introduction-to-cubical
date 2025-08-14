<!--
```
module 1--Type-Theory.1-4--Record-Types-and-Copatterns where

open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
```
-->


# Lecture 1-4: Record Types and Copatterns

On occasion we will want to package together some collection of data
into a single larger type. This is an extremely common pattern in
ordinary programming: think of `struct`s in C or C++, `dataclass`es in
Python, or simply rows in a database.

We already have a way of doing this by nesting Σ-types, which we have
had a taste of in ``Σ-assoc-toⁱ`` and ``Σ-assoc-froⁱ``. But Agda
provides a facility known as *record* types which make these compound
types much more pleasant to use, and which are the topic of this
(fairly short) lecture.


## Defining Records

Whereas an inductive type is specified by a list of constructors, a
record type is specified by a list of *fields* and their types. An
element of the record type will consist of an element of each of the
field types.

Suppose for some reason we want to package a natural number, Boolean,
and element of the unit type into a single type.

```
record Trio : Type where
  field
    one : ℕ
    two : Bool
    thr : ⊤
```

The following line allows us to refer to ``one``, ``two`` and ``thr``
without qualifying them as `Trio.one`, `Trio.two` and `Trio.thr`
everywhere. We will be `open`ing all our records, so we'll have to
make sure we give the fields descriptive names.

```
open Trio
```

Accessing the fields of a record is done by using the field names as
projections, as we saw for Σ-types in Lecture 1-1.

```
get-one : Trio → ℕ
get-one p = p .one

get-two : Trio → Bool
get-two p = p .two

get-thr : Trio → ⊤
get-thr p = p .thr
```

It is occasionally useful to refer to a projection as a function out
of the record, for example when composing the function with something
else or passing it to a higher-order function. This can be done by
leaving off the dot.

```
one-isZero : Trio → Bool
one-isZero = isZero ∘ one
```

This is shorthand for an anonymous function that does the projection
properly.

```
_ = test-identical one (λ p → p .one)
```

Constructing an element of a record type is done via a mirror-image
process to case-splitting on inductive types. For each field of the
record, we provide a value for that field.

```
favourite-trio : Trio
favourite-trio = record
  { one = 19
  ; two = true
  ; thr = tt
  }
```

Records have their own computation rule. If you have a `record`
expression and project one of its fields, you get exactly what was
placed in that field:

```
_ = test-identical
    (record
     { one = 19
     ; two = true
     ; thr = tt
     } .one)
    19

_ = test-identical
    (record
     { one = 19
     ; two = true
     ; thr = tt
     } .two)
    true
```

Using records has some downsides over iterated Σ-types. When we prove
general facts about Σ-types, they will not automatically apply to any
of the record types we have defined. We will have to manually convert
to and from the corresponding Σ-type to make use of those proofs, via
maps along the lines of the following.

```
Trio-to : Trio → ℕ × Bool × ⊤
Trio-to t = t .one , t .two , t .thr

Trio-fro : ℕ × Bool × ⊤ → Trio
Trio-fro s = record
  { one = s .fst
  ; two = s .snd .fst
  ; thr = s .snd .snd
  }
```

Packing some values into a record like this is a common situation.
Agda lets us name a constructor for a record type, so that we don't
have to use non-descriptive `record` keyword each time. This has to be
done at the moment the record type is declared, so here is a new
version of ``Trio`` where we have done this:

```
record Trio' : Type where
  constructor trio'
  field
    one' : ℕ
    two' : Bool
    thr' : ⊤

open Trio'
```

The constructor ``trio'`` is now a function that accepts the fields
of the ``Trio'`` record one at a time, and gives back a trio.

```
favourite-trio' : Trio'
favourite-trio' = trio' 19 true tt
```


## Uniqueness Principle

Records have one additional rule which can come in handy: a
*uniqueness* principle. This states that any element of a record type
can be unpacked into its fields and repacked into a record, and the
result is identical to the record we started with. One gloss on this
is that there is no extra information that can be carried by an
element of a record type: the fields are sufficient to capture
everything.

```
_ = λ (t : Trio) → test-identical
      t
      record
       { one = t .one
       ; two = t .two
       ; thr = t .thr
       }
```

For an inductive type like ``Bool``, a simple uniqueness principle
would look something like the following:

    _ = λ (b : Bool) → test-identical
          b
          (case b of λ
           { true  → true
           ; false → false
           })

That is, every Boolean element can be replaced by one where you do
case analysis on the Boolean immediately.

Unfortunately, it is not possible to support this kind of uniqueness
principle for inductive types and maintain other desirable properties
of the type system. We've taken for granted that Agda can check that
our definitions match the types that we claim they have, and it
doesn't get stuck in an infinite loop or give up. As innocent as this
uniqueness principle looks, general uniqueness for inductive types
ruins the "decidability" of typechecking. (See the references below).

Worse (arguably), a uniqueness principle for all inductive types
destroys all the "higher dimensional" structure of types, which was
one of the motivations for creating Homotopy Type Theory in the first
place!

There is some consolation: we can still prove that, for example, any
element of ``Bool`` must equal ``true`` or ``false``, as we do later
in ``≡Bool-LEM``. We just can't arrange things so Agda knows
automatically that every Boolean is literally identical to one of
``true`` or ``false``.

To summarise this section, there is a nice duality between inductive
types and record types.

| Inductive Types                                               | Record Types                                                   |
|---------------------------------------------------------------|----------------------------------------------------------------|
| Specified by the types of *constructors*                      | Specified by the types of *fields*                             |
| Created by choosing *one* constructor                         | Created by giving a value for *every* field                    |
| Eliminated by giving a value for *every* constructor          | Eliminated by choosing *one* field                             |
| Eliminating a constructor computes to the corresponding value | Projecting the constructor computes to the corresponding value |
| -                                                             | A record is uniquely determined by its projections             |


## Copatterns

There is an analogy with another type constructor we would like to
make: records are quite similar to functions, in that you define one
them by explaining what happens when you eliminate it.

Let's extend the above table:

| Record Types                                                   | Function Types                                        |
|----------------------------------------------------------------|-------------------------------------------------------|
| Specified by the types of *fields*                             | Specified by the types of *argument and result*       |
| Created by giving a value for *every* field                    | Created by giving a value for *any possible* argument |
| Eliminated by choosing *one* field                             | Eliminated by choosing *one* argument                 |
| Projecting the constructor computes to the corresponding value | Applying a λ computes to the corresponding value      |
| A record is uniquely determined by its projections             | A function is uniquely determined by its applications |

Agda takes this analogy seriously, and lets us create records using
the built-in definition syntax we have been using from the start. Just
as the definition of a function gives an equation for what happens
when you apply the function, in this style the definition of a record
gives an equation for what happens when you project the record.

```
favourite-trio'' : Trio
favourite-trio'' .one = 19
favourite-trio'' .two = true
favourite-trio'' .thr = tt
```

Definition clauses like this are called *copatterns*. Ordinary pattern
matching explains what a function does when its input is a particular
constructor. Copattern matching explains what a function does its
output used by a particular *eliminator*.

Using copatterns can really help when working with nested record
types, as we do later in this course. Just as patterns can be nested
to pull apart nested inductive types (look at, for example,
``⊎-assoc-to``), copatterns can construct nested record types:

```
trio×-again : {A B C : Type} → A → B → C → ((A × B) × C)
trio×-again a b c .fst .fst = a
trio×-again a b c .fst .snd = b
trio×-again a b c .snd      = c
```

::: Aside:
In the type-theory literature, types which are determined by their
eliminators are often called *negative* types, as opposed to
*positive* types such as inductive types, which are determined by
their constructors.
:::


## ⊤ as a Record and Σ as an Inductive Type

For some types, there is wiggle room in when to use an inductive type
vs a record type. For example, we could have defined the unit type
``⊤`` as a record without any fields:

```
record Record-⊤ : Type where
  constructor Record-tt
  -- No fields!
```

The named constructor ``Record-tt`` is a function that accepts the
fields in order and gives an element of ``Record-⊤``. But there are no
fields, so already `Record-tt : Record-⊤`.

This definition has the advantage that, because of the uniqueness that
comes with record types, *any* element of ``Record-⊤`` is identical to
``tt`` without needing to do a pattern match to reveal this fact.

```
_ = λ (u : Record-⊤) → test-identical u Record-tt
-- Fails!
-- _ = λ (u : ⊤) → test-identical u tt
```

This is occasionally helpful, but missing it is not a big deal.

Back in Lecture 1-1 (and revisited in Lecture 1-3), we saw the operations
``×-curry`` and ``×-uncurry`` which are mutual inverses. Putting
dependency aside, these state that to produce a map out of a pair type
`A × B → C`, it is enough to produce a map `A → B → C`. This looks
awfully like the universal mapping property of an inductive type, and
indeed we can create another version of the ``×`` type as follows.

```
data Inductive-× {ℓ ℓ' : Level} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  comma : A → B → Inductive-× A B

Inductive-fst : {A : Type} {B : Type} → Inductive-× A B → A
Inductive-fst (comma a b) = a

Inductive-snd : {A : Type} {B : Type} → Inductive-× A B → B
Inductive-snd (comma a b) = b
```

Something similar works for ``Σ``. Losing the eta-rule for ``×`` and
``Σ`` is not a huge problem: we could prove a less convenient version
of it ourselves using the path types we introduce in Part 2. In any
case, we'll stick with the record version of ``Σ`` we've been using so
far.


## References and Further Reading

* Agda Documentation
  * [Record Types](https://agda.readthedocs.io/en/latest/language/record-types.html)
  * [Copatterns](https://agda.readthedocs.io/en/latest/language/copatterns.html)

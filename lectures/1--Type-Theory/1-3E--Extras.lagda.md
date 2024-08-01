```
module 1--Type-Theory.1-3E--Extras where
```
<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
```
-->


# Lecture 1-3E: Extras

This is a file of extra exercises.


## Reconstructing Products and Unions

Here's a basic example. We can think of a dependent function type as a
generalised cartesian product. In a function with type `(x : A) → C
x`, the `x : A` acts like an index, so for each index `x` we have an
element of the corresponding `C x`. This is especially clear when we
pick domain is ``Bool``. When `A` is ``Bool``, the domain
has exactly the two elements ``true`` and ``false``, so
`(x : Bool) → C x` is the binary cartesian product of `C true` and `C
false`. Going the other way, we can easily extract the elements of `C
true` and `C false` from such a function.

The fact that the two types come from the same type family `C` makes
it feel like they have to be somehow related, but we can construct a
type family out of any two types `A` and `B` at all, via another use
of ``Bool-ind``.

```
-- Bool×-family : {ℓ : Level} (A B : Type ℓ) → Bool → Type ℓ
-- Bool×-family A B = Bool-rec A B

-- Bool×-to : {ℓ : Level} {A B : Type ℓ}
--   → ((x : Bool) → Bool×-family A B x) → A × B
-- Bool×-to f = f true , f false

-- -- You are building a function out of `Bool` here, so use `Bool-ind`.
-- Bool×-fro : {ℓ : Level} {A B : Type ℓ}
--   → A × B → ((x : Bool) → Bool×-family A B x)
-- Bool×-fro (a , b) = Bool-ind a b
```

mvrnote: Also do it as an inductive type, discuss the difference?

## Finite Types

```
Fin : ℕ → Type
Fin zero = ∅
Fin (suc n) = ⊤ ⊎ Fin n

Fin-newest : (n : ℕ) → Fin (suc n)
Fin-newest n = inl tt

Fin-oldest : (n : ℕ) → Fin (suc n)
Fin-oldest zero = inl tt
Fin-oldest (suc n) = inr (Fin-oldest n)
```

mvrnote: etc, surely a bit can be said. a good challenge could be `Fin n ⊎ Fin m ≃ Fin (n +ℕ m)`
HoTT book:
Exercise 3.22. As in classical set theory, the finite version of the axiom of choice is a theorem.
Prove that the axiom of choice (3.8.1) holds when X is a finite type Fin(n) (as defined in Exercise 1.9).

## Lists


```
-- A list containing just one entry
[_] : {A : Type} → A → List A
[ a ] = a :: []

testList : List ℕ
testList = 1 :: 0 :: 3 :: 2 :: 0 :: 8 :: []
```

Before we start, the recursion principle for ``List``s has a
special name that you may have seen used in other programming
languages: ``fold``.

```
fold : {A B : Type}
     → (start : B)        -- the starting value
     → (acc : A → B → B)  -- the accumulating function
     → List A → B
fold start acc [] = start
fold start acc (x :: L) = acc x (fold start acc L)
```

Use ``fold`` to write a function that sums a list of numbers.

```
sumℕ : List ℕ → ℕ
sumℕ = fold zero _+ℕ_
```

To test that you did it right, try normalizing the following.
To normalize, use `C-c C-n`, then type in ``test-sum``.

```
test-sum : ℕ
test-sum = sumℕ testList
```

Now do the product:

```
prodℕ : List ℕ → ℕ
prodℕ = fold (suc zero) _·ℕ_

test-prod : ℕ
test-prod = prodℕ testList
```

Write a fuction which applies a function to each element in a list.

```
-- map suc [1,2,3,4] should be [2, 3, 4, 5]
map : {A B : Type} → (A → B) → List A → List B
map f [] = []
map f (x :: L) = (f x) :: (map f L)

map-test : List ℕ
map-test = map suc testList
```

Write a function which filters a list according to a provided
proposition:

```
-- filter isEven [1, 2, 3, 4, 5, 6] should be [2, 4, 6]
filter : {A : Type} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: L) = if p x then (x :: (filter p L)) else (filter p L)

isNonZero : ℕ → Bool
isNonZero zero = false
isNonZero (suc n) = true

filter-test : List ℕ
filter-test = filter isNonZero testList
```

Write a function which reverses a list.

```
-- reverse [1, 2, 3, 4] should be [4, 3, 2, 1]
reverse : {A : Type} → List A → List A
reverse [] = []
reverse (x :: L) = reverse L ++ [ x ]

reverse-test : List ℕ
reverse-test = reverse testList
```

data _∈_ {A : Set}(x : A) : List A → Set where
  first : {xs : List A} → x ∈ x :: xs
  later : {y : A}{xs : List A} → x ∈ xs → x ∈ y :: xs

infix 4 _∈_

_!_ : ∀{A : Set} → List A → ℕ → Maybe A
[] ! _           = nothing
x :: xs ! zero    = just x
x :: xs ! (suc n) = xs ! n

infix 5 _!_

lookup : ∀ {A}{x : A}(xs : List A) → x ∈ xs → Σ ℕ (λ n → xs ! n ≡ just x)

or similar

## Nits

Could also use Nit (with only sacc)
```
data Nit : Type where
  sac : Nit → Nit

imp : Nit → ∅
imp (sac l) = imp l
```

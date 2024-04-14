```
module 1--Type-Theory.1-2E--Extras where
```
<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
```
-->


# Lecture 1-E: Extras

This is a file of extra exercises. Most of them are about lists.

```
-- A list containing just one entry
[_] : {A : Type} → A → List A
[ a ] = a ∷ []

testList : List ℕ
testList = 1 ∷ 0 ∷ 3 ∷ 2 ∷ 0 ∷ 8 ∷ []
```

Before we start, the recursion principle for `List`s has a special
name: `fold`{.Agda}

```
fold : {A B : Type}
     → (start : B)        -- the starting value
     → (acc : A → B → B)  -- the accumulating function
     → List A → B
fold start acc [] = start
fold start acc (x ∷ L) = acc x (fold start acc L)
```

Use `fold`{.Agda} to write a function that sums a list of numbers.

```
sumℕ : List ℕ → ℕ
sumℕ = fold zero _+_
```

To test that you did it right, try normalizing the following.
To normalize, use `C-c C-n`, then type in `test-sum`{.Agda}.

```
test-sum : ℕ
test-sum = sumℕ testList
```

Now do the product:

```
prodℕ : List ℕ → ℕ
prodℕ = fold (suc zero) _·_

test-prod : ℕ
test-prod = prodℕ testList
```

Write a fuction which applies a function to each element in a list.

```
-- map suc [1,2,3,4] should be [2, 3, 4, 5]
map : {A B : Type} → (A → B) → List A → List B
map f [] = []
map f (x ∷ L) = (f x) ∷ (map f L)

map-test : List ℕ
map-test = map suc testList
```

Write a function which filters a list according to a provided
proposition:

```
-- filter isEven [1, 2, 3, 4, 5, 6] should be [2, 4, 6]
filter : {A : Type} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ L) = if p x then (x ∷ (filter p L)) else (filter p L)

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
reverse (x ∷ L) = reverse L ++ [ x ]

reverse-test : List ℕ
reverse-test = reverse testList
```

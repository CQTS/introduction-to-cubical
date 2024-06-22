# Lecture 2-4E: More with `hcomp`s

```
module 2--Paths-and-Identifications.2-4E--More-with-hcomps where

open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Propositions

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C D : Type ℓ
    S : A → Type ℓ
    x y z w : A
```


## Cubes in practice

Using `hcomp`, we can show that the space of paths in a contractible
type is also contractible.

```
-- isContrisContr≡ : {A : Type ℓ} (c : isContr A) (a b : A) → isContr (a ≡ b)
-- isContrisContr≡ (c₀ , c) a b =
--   (λ i → hcomp (λ { j (i = i0) → c a j
--                   ; j (i = i1) → c b j}) c₀)
--   ,
-- -- MVRNOTE: we can actually just leave off the `i = i0` case, and the
-- -- result of the below `hcomp` will be definitionally equal to the
-- -- filler for the above `hcomp` on that boundary. I think the cubists
-- -- call this 'uniformity'
--   λ p i j → hcomp (λ { k (i = i1) → c (p j) k
--                      ; k (j = i0) → c a k
--                      ; k (j = i1) → c b k}) c₀
```

Contractible types are so restricted that we know a lot about their
path types too. (This is all foreshadowing for the next section!)

```
isContr→everythingEqual :
  isContr A
  → ((x y : A) → (x ≡ y))
isContr→everythingEqual (x , p) a b = sym (p a) ∙ p b

everythingEqual→pathsEqual :
    ((x y : A) → (x ≡ y))
  → ((x y : A) → (p q : x ≡ y) → p ≡ q)
```
For this one, we need a cube:

                b - - - - - - - - > b
              / ^                 / ^
         p  /   |               /   |
          /     |             /  q  |
        a - - - - - - - - > a       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       a - - - - - | - - > a
        |     /             |     /
        |   /               |   /
        | /                 | /
        a - - - - - - - - > a


```
everythingEqual→pathsEqual-faces :
  (h : (x y : A) → x ≡ y) (a b : A) (p q : a ≡ b)
  (i : I) → (j : I) → (k : I) → Partial (∂ i ∨ ∂ j) A
everythingEqual→pathsEqual-faces h a b p q i j k (i = i0) = h a (p j) k
everythingEqual→pathsEqual-faces h a b p q i j k (i = i1) = h a (q j) k
everythingEqual→pathsEqual-faces h a b p q i j k (j = i0) = h a a k
everythingEqual→pathsEqual-faces h a b p q i j k (j = i1) = h a b k

everythingEqual→pathsEqual h a b p q i j =
  hcomp (everythingEqual→pathsEqual-faces h a b p q i j) a

everythingEqual→isContrPath :
    ((x y : A) → (x ≡ y))
  → (x y : A) → isContr (x ≡ y)
everythingEqual→isContrPath h x y = h x y , everythingEqual→pathsEqual h x y _

isContr→isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath cA = everythingEqual→isContrPath (isContr→everythingEqual cA)

-- isContr→isEquiv : {A : Type ℓ} {B : Type ℓ'} → isContr A → isContr B → (f : A → B) → isEquiv f
-- isContr→isEquiv {A = A} {B = B} c c' f b = isContrRetract fst g r c
--   where g : A → fiber f b
--         g a = a , trans (sym (snd c' (f a))) (snd c' b)
--         fro-to : retract {A = fiber f b} {B = A} fst g
--         fst (r (a , p) i) = a
--         snd (r (a , p) i) = isContr→everythingEqual (isContr→isContrPath c' (f a) b) (snd (g a)) p i
```
--------


On the other hand, any one-to-one correspondence gives rise to an equivalence.
```
-- module _ {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
--          (fiberFunc : ∀ a → B a → C a)
--          where
--   totalFunc : (Σ[ a ∈ A ] B a) → (Σ[ a ∈ A ] C a)
--   totalFunc (a , b) = a , fiberFunc a b

--   private
--     f : {a : A} {c : C a} → fiber totalFunc (a , c) → fiber (fiberFunc a) c
--     f ( (a , b) , p) = J (λ (a' , c') eq → fiber (fiberFunc a') c') (b , refl) p

--     g : {a : A} {c : C a} → fiber (fiberFunc a) c → fiber totalFunc (a , c)
--     g {a} {c} (b , p) = (a , b) , (λ i → a , p i)

--     f-g : {a : A} {c : C a} → (y : fiber (fiberFunc a) c) → f (g y) ≡ y
--     f-g {a} {c} (b , p) = J (λ _ p' → f (g (b , p')) ≡ (b , p')) body p
--       where body : f (g (b , refl)) ≡ (b , refl)
--             body = JRefl {x = a , fiberFunc a b} (λ (a , c) _ → fiber (fiberFunc a) c) (b , refl)

--     g-f : {a : A} {c : C a} → (z : fiber totalFunc (a , c)) → g (f z) ≡ z
--     g-f ((a , b) , p) = J (λ _ p' → g (f ((a , b) , p')) ≡ ((a , b) , p')) body p
--       where body : g (f ((a , b) , refl)) ≡ ((a , b) , refl)
--             body = cong g (JRefl {x = a , fiberFunc a b}(λ (a , c) _ → fiber (fiberFunc a) c) (b , refl))

--   fiberIsEquiv : (totalIsEquiv : isEquiv totalFunc)
--                → ∀ x → isEquiv (fiberFunc x)
--   fiberIsEquiv totalIsEquiv x y = isContrRetract g f f-g (totalIsEquiv (x , y))

--   totalIsEquiv : (fiberIsEquiv : ∀ x → isEquiv (fiberFunc x))
--                → isEquiv totalFunc
--   totalIsEquiv fiberIsEquiv (x , v) = isContrRetract f g g-f (fiberIsEquiv x v)

-- retract-isFunctionalGraph→Fun-Equiv : {A B : Type} (R : Rel A B) (c : isFunctional R)
--                                       (a : A) (b : B) → (graph (isFunctional→Fun R c) a b) ≃ (R a b)
-- retract-isFunctionalGraph→Fun-Equiv {A} {B} R c a b = to a b , fiberIsEquiv (to a) (totalequiv a) b
--   where
--     f : A → B
--     f = isFunctional→Fun R c

--     to : (a : A)(b : B) → graph f a b → R a b
--     to a b p = subst (λ b → R a b) p (snd (fst (c a)))

--     totalequiv : (a : A) → isEquiv (totalFunc (to a))
--     totalequiv a = isContr→isEquiv (isContrSingl (f a)) (c a) (totalFunc (to a))

{-
OneToOne→Iso : {A B : Type} (R : Rel A B)
               → isOneToOne R → Iso A B
Iso.fun (OneToOne→Iso R (fl , fl')) = isFunctional→Fun R fl
Iso.inv (OneToOne→Iso R (fl , fl')) = isFunctional→Fun (flip R) fl'
Iso.rightInv (OneToOne→Iso R (fl , fl')) b = {!!}
Iso.leftInv (OneToOne→Iso R (fl , fl')) = {!!}
-}
-- OneToOne→Equiv : {A B : Type} (R : Rel A B)
--                → isOneToOne R → A ≃ B
-- OneToOne→Equiv R (is-functional , flip-is-functional) =
--   isFunctional→Fun R is-functional , lemma
--   where lemma : isEquiv (isFunctional→Fun R is-functional)
--         fst (fst (lemma b)) = {!!}
--         snd (fst (lemma b)) = {!!}
--         snd (lemma b) = {!!}
```



```
-- FunIsoFunctionalGraph : {A B : Type} → Iso (A → B) (Σ[ R ∈ Rel A B ] (isFunctional R))
-- FunIsoFunctionalGraph {A} {B} = iso to fro to-fro r
--   where
--     to : (A → B) → Σ[ R ∈ Rel A B ] (isFunctional R)
--     to f = graphRel f , isFunctionalGraph f

--     open import Cubical.Foundations.Function
--     fro : Σ[ R ∈ Rel A B ] (isFunctional R) → (A → B)
--     fro = uncurry isFunctional→Fun

--     to-fro : section to fro
--     to-fro (R , c) = {!!}

--     fro-to : section fro to
--     r f = refl
```

# Bonus: Paths in higher loops commute

```
EH-base : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl)
         → (λ i → α i ∙ refl) ∙ (λ i → refl ∙ β i)
          ≡ (λ i → refl ∙ β i) ∙ (λ i → α i ∙ refl)
EH-base α β i = (λ j → α (~ i ∧ j) ∙ β (i ∧ j)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

EH : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl) → α ∙ β ≡ β ∙ α
EH {A = A} α β i j z =
  hcomp (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ (cong (λ x → lUnit x (~ k)) β)) j
                 ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ (cong (λ x → rUnit x (~ k)) α)) j
                 ; (j = i0) → rUnit refl (~ k)
                 ; (j = i1) → rUnit refl (~ k)})
  (EH-base α β i j) z
```

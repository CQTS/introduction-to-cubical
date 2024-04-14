```
module 2--Paths-and-Identifications.2-9--Univalence where
```

# Lecture 2-9: Univalence

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Isomorphisms-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Transport-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Propositions
open import 2--Paths-and-Identifications.2-7--Sets
open import 2--Paths-and-Identifications.2-8--Equivalences
open import Library.Univalence

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
```
-->

An important feature of Cubical Type Theory is *univalence*. This is
the statement that paths between types are equivalent to equivalences
between those types.

Cubical Type Theory's central accomplishment over other type theories
is allowing the univalence principle to compute. This is done using ---
in addition to all the cubical machinery we've seen so far --- `Glue`
types, whose constructor has the following signature.

`Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'`

`Glue`{.AGda} is a type constructor that takes a type `A`, a formula
`φ`, and a partial element `Te : Partial φ (Σ[ T ∈ Type ] (T ≃ A))` of
pairs of types equipped with an equivalence to `A`. The type we are
taking partial elements of, `Σ[ T ∈ Type ] (T ≃ A)`, is reminiscent of
the singleton types from 2-3; if `(T ≃ A)` were equivalent to `(T ≡
A)`, then this would be the singleton type of `A` in `Type`{.Agda}.

As usual, the formula `φ` plays a crucial role. Consider the case of
`φ = ∂ i`. We can depict an element of the partial type
`Te : Partial (∂ i) (Σ[ T ∈ Type ℓ' ] T ≃ A)` as follows:

                 A i
         A i0  - - - > A i1
           ^             ^
    Te i0  (             ( Te i1                  ^
           )             )                        )
         T i0          T i1                       ∙ — >
                                                    i

where the vertical lines are equivalences, rather than paths. This
looks a lot like the kind of thing we were `hcomp`{.Agda}ing over in Lecture 2-4
(except that it is open on the bottom rather than the top, which is a
conventional choice --- the equivalences go into `A`, rather than out
of it). `Glue`{.Agda} types enable us to "cap off" this open box of types.

That is, if `φ = ∂ i`, then `Glue A Te : Type` is the line of types
living *under* `A` in the capped off version of the above square.

`Glue`{.Agda} types come with some guarantees. Firstly, like `hcomp`{.Agda}, the
line that we get agrees with the partial input anywhere the formula
`φ` holds. In the example, this means `Glue A Te = T i0` when `i = i0`
and `Glue A Te = T i1` when `i = i1`.

Secondly, for any element of `Glue A Te` at all, we can extract the
underlying element of `A` that we started with: this is called
`unglue φ : Glue A Te → A`. Because of the above computation rule, if we
are working where `φ` holds then the domain of this function is `T`.
Luckily, if `φ` holds, we have access to an equivalence `T ≃ A`, from
which we can extract the necessary function `T → A`.

To summarise, `Glue Te` is a version of `A` that has the types `T`
glued on wherever `φ` holds, using the provided equivalences `Te` to
extract an underlying element of `A` when asked.

The first and most important example of a `Glue` type gives us
"univalence".

           B
      B - - - > B
      ^         ^
    e (         ( idEquiv                ^
      )         )                        )
      A         B                        ∙ — >
                                           i

```
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B {φ = ∂ i} (λ { (i = i0) → (A , e)
                                             ; (i = i1) → (B , idEquiv B) })
```

We can show that `ua`{.Agda} of the identity equivalence is `refl`{.Agda}.
```
uaIdEquiv : ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , idEquiv A)
```

And, nicely, transporting over `ua e` is the same as applying the
function underlying `e`.

```
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ fst e x
uaβ e x = transport-refl (equivFun e x)
```

For concrete types this typically holds definitionally, like
`transport`{.Agda}, but for an arbitrary equivalence `e` between
abstract types `A` and `B` we have to prove it. This is an instance of
the computation rule for `transport`{.Agda} on `Glue`{.Agda} types,
which in general is quite complicated.

```
uaβBool : (e : Bool ≃ Bool) (x : Bool) → transport (ua e) x ≡ fst e x
uaβBool e x = refl

-- _ : transport (ua (isoToEquiv not-Iso)) true ≡ false
-- _ = refl

-- mvrnote: circle no-longer defined
-- uaβS¹ : (e : S¹ ≃ S¹) (x : S¹) → transport (ua e) x ≡ fst e x
-- uaβS¹ e x = refl
```

`unglue`{.Agda} works as expected on `ua`{.Agda} - we are able to get
out the element of `B` no matter where we are in the `Glue` type `ua e
i`.

```
ua-unglue : ∀ (e : A ≃ B) (i : I) (x : ua e i) → B
ua-unglue e i x = unglue (∂ i) x

_ :  ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i0) → ua-unglue e i0 x ≡ (fst e) x
_ = λ e i x → refl

_ :  ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i1) → ua-unglue e i1 x ≡ x
_ = λ e i x → refl
```

If ‵x : A` and `y : B`, then to get a `PathP` from `x` to `y` over `ua
e i` is the same as giving a path from `e x` to `y`.

```
ua-PathP→Path : ∀ (e : A ≃ B) {x : A} {y : B}
              → PathP (λ i → ua e i) x y
              → e .fst x ≡ y
ua-PathP→Path e p i = ua-unglue e i (p i)
```

Finally, univalence is the inverse to `pathToEquiv`{.Agda} and so we
have completely characterised paths between types.

```
au : A ≡ B → A ≃ B
au = pathToEquiv

ua-au : (p : A ≡ B) → ua (au p) ≡ p
ua-au = J (λ _ p → ua (au p) ≡ p) path
  where path = ua (au refl)   ≡⟨ cong ua pathToEquivRefl ⟩
               ua (idEquiv _) ≡⟨ uaIdEquiv ⟩
               refl ∎

au-ua : (e : A ≃ B) → au (ua e) ≡ e
au-ua e = equivEq (funExt (uaβ e))

univalenceIso : Iso (A ≡ B) (A ≃ B)
univalenceIso .Iso.fun = au
univalenceIso .Iso.inv = ua
univalenceIso .Iso.rightInv = au-ua
univalenceIso .Iso.leftInv = ua-au
```

Here is an interesting application: we can implement addition in
`ℤ`{.Agda} as composition of paths, and addition with any fixed
integer must be an equivalence.

mvrnote: exercises
```
sucℤ-Path : ℤ ≡ ℤ
sucℤ-Path = ua (isoToEquiv sucℤ-Iso)

add-n-Path : ℕ → ℤ ≡ ℤ
add-n-Path zero = refl
add-n-Path (suc n) = add-n-Path n ∙ sucℤ-Path

predℤ-Path : ℤ ≡ ℤ
predℤ-Path = ua (isoToEquiv (invIso sucℤ-Iso))

sub-n-Path : ℕ → ℤ ≡ ℤ
sub-n-Path zero = refl
sub-n-Path (suc n) = sub-n-Path n ∙ predℤ-Path

_+ℤ'_ : ℤ → ℤ → ℤ
m +ℤ' pos n    = transport (add-n-Path n) m
m +ℤ' negsuc n = transport (sub-n-Path (suc n)) m

-- This agrees with regular addition defined by pattern-matching
+ℤ'≡+ℤ : _+ℤ'_ ≡ _+ℤ_
+ℤ'≡+ℤ i m (pos zero) = m
+ℤ'≡+ℤ i m (pos (suc n)) = sucℤ (+ℤ'≡+ℤ i m (pos n))
+ℤ'≡+ℤ i m (negsuc zero) = predℤ m
+ℤ'≡+ℤ i m (negsuc (suc n)) = predℤ (+ℤ'≡+ℤ i m (negsuc n))

-- So +ℤ' with a fixed element is an equivalence
isEquivAddℤ' : (m : ℤ) → isEquiv (λ n → n +ℤ' m)
isEquivAddℤ' (pos n)    = isEquivTransport (add-n-Path n)
isEquivAddℤ' (negsuc n) = isEquivTransport (sub-n-Path (suc n))

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +ℤ'≡+ℤ isEquivAddℤ'
```

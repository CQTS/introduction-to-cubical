# Lecture 3-1: Structure Identity Principle

```
module 3--Structures.3-1--Structure-Identity-Principle where
```

<!--
```
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets
open import 2--Paths-and-Identifications.2-9--Contractible-Maps

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    S : Type ℓ → Type ℓ'
    C : (a : A) (b : B a) → Type ℓ
```
-->

In lecture 2-9, we saw how the univalence axiom can be used to show that
paths between types are equivalent to equivalences between those types.
In this lecture, we will extend the idea of univalence to the so-called
Structured Identity Principle (SIP). The SIP will show that paths between
structures are equivalent to isomorphisms between those structures. But
what exactly is a structure? A structure, loosely  defined, will be a type
equipped with additional properties such as operators or an identity.


We will start by giving our first example of a structure: the semigroup.
A semigroup is a set equipped with a binary operator as well as 
associativity.

Instead of defining the semigroup with the 'data' keyword, we will use
'record' as it allows us to group related fields together, providing a
better way to talk about structures with their associated properties. 

```
record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where
  no-eta-equality
  constructor issemigroup

  field
    is-set : isSet A
    ·Assoc : (x y z : A) → x · (y · z) ≡ (x · y) · z
```

When we add an identity element to a semigroup, we obtain a monoid.

```
record IsMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor ismonoid

  field
    isSemigroup : IsSemigroup _·_
    ·IdR : (x : A) → x · ε ≡ x
    ·IdL : (x : A) → ε · x ≡ x

  open IsSemigroup isSemigroup public
```

Next, we want to make precise the definition of a structure. TypeWithStr
is a useful type to generalize types with structures defined on them.

```
TypeWithStr : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeWithStr ℓ S = Σ[ X ∈ Type ℓ ] S X
```

MonoidStr encapsulates a type along with its monoid structure.

```
record MonoidStr (A : Type ℓ) : Type ℓ where
  constructor monoidstr

  field
    ε         : A
    _·m_      : A → A → A
    isMonoid  : IsMonoid ε _·m_

  open IsMonoid isMonoid public
```

Monoid' is a type that encapsulates all types with a monoid structure.

```
Monoid' : ∀ ℓ → Type (ℓ-suc ℓ)
Monoid' ℓ = TypeWithStr ℓ MonoidStr
```

Next, we want to construct some more machinery to work with structures,
and also prove the Structure Identity Principle. One thing that is not
immediately obvious is that the SIP does not apply to all structures.
In fact, it only applies to univalent structures. A structure is considered
univalent, trivially, if an equivalence between two structures induces a path
between these structures through the univalence axiom.


The function typ and str extract the underlying type and structure
from a TypeWithStr.

```
typ : TypeWithStr ℓ S → Type ℓ
typ = fst

str : (A : TypeWithStr ℓ S) → S (typ A)
str = snd
```

The StrEquiv type represents the notion of an equivalence between two
TypeWithStr objects. It takes a type constructor S and returns a type
for equivalences between the structured types. The equivalence is given
by an equivalence between the underlying types (typ A ≃ typ B).

```
StrEquiv : (S : Type ℓ → Type ℓ'') (ℓ' : Level) → Type (ℓ-max (ℓ-suc (ℓ-max ℓ ℓ')) ℓ'')
StrEquiv {ℓ} S ℓ' = (A B : TypeWithStr ℓ S) → typ A ≃ typ B → Type ℓ'
```

UnivalentStr represents univalent structures. A structure S is considered
univalent if for any equivalence e between the underlying types of A and B,
the equivalence between the structures ι A B e is equivalent to a path between
the structures induced by the univalence axiom (ua e).

```
UnivalentStr : (S : Type ℓ → Type ℓ') (ι : StrEquiv S ℓ'') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
UnivalentStr {ℓ} S ι =
  {A B : TypeWithStr ℓ S} (e : typ A ≃ typ B)
  → ι A B e ≃ PathP (λ i → S (ua e i)) (str A) (str B)
```

We will now revisit the previous simplified monoid structure to show how
we can construct it as a univalent structure.

```
RawMonoidStructure : Type → Type
RawMonoidStructure X = X × (X → X → X)

RawMonoid : Type₁
RawMonoid = TypeWithStr _ RawMonoidStructure

RawMonoidEquivStr : StrEquiv RawMonoidStructure ℓ-zero
RawMonoidEquivStr (A , (εA , _·A_)) (B , (εB , _·B_)) (x , y) =
  (x εA ≡ εB) × (∀ a b → x (a ·A b) ≡ x a ·B x b)

rawMonoidUnivalentStr : UnivalentStr _ RawMonoidEquivStr
rawMonoidUnivalentStr {A} {B} e = {!   !}
```

Notice how we only used the raw monoid structure to define the univalent
structure above! We did that because there is a need to carefully separate
the raw structure of a type from its axioms. The reason for that is that we 
need to show that every axiom on a structure is also a proposition.


We define an axiom structure as follows:

```
AxiomsStructure : (S : Type ℓ → Type ℓ')
  (axioms : (X : Type ℓ) → S X → Type ℓ'')
  → Type ℓ → Type (ℓ-max ℓ' ℓ'')
AxiomsStructure S axioms X = Σ[ s ∈ S X ] (axioms X s)
```

Next, we need a notion of equivalence between axiom structures.

```
AxiomsEquivStr : {S : Type ℓ → Type ℓ'} (ι : StrEquiv S ℓ'')
  (axioms : (X : Type ℓ) → S X → Type ℓ''')
  → StrEquiv (AxiomsStructure S axioms) ℓ''
AxiomsEquivStr ι axioms (X , (s , a)) (Y , (t , b)) e = ι (X , s) (Y , t) e
```

Finally, we define what it means for axiom structures to be univalent.

```
Σ-contractSnd : ((a : A) → isContr (B a)) → Σ A B ≃ A
Σ-contractSnd c = equiv fst (λ a → a , c a .fst) (λ _ → refl) (λ (a , b) → cong (a ,_) (c a .snd b))

isProp→isContrPath : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath h x y = h x y , isProp→isSet h x y _

axiomsUnivalentStr : {S : Type ℓ → Type ℓ'}
  (ι : (A B : TypeWithStr ℓ S) → A .fst ≃ B .fst → Type ℓ'')
  {axioms : (X : Type ℓ) → S X → Type ℓ'''}
  (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
  (θ : UnivalentStr S ι)
  → UnivalentStr (AxiomsStructure S axioms) (AxiomsEquivStr ι axioms)

_≃⟨_⟩_ : {B : Type ℓ'} {C : Type ℓ''} (X : Type ℓ) → (X ≃ B) → (B ≃ C) → (X ≃ C)
_ ≃⟨ f ⟩ g = compEquiv g f

_■ : (X : Type ℓ) → (X ≃ X)
_■ = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

axiomsUnivalentStr {S = S} ι {axioms = axioms} axioms-are-Props θ {X , s , a} {Y , t , b} e  =
  ι (X , s) (Y , t) e
    ≃⟨ θ e ⟩
  PathP (λ i → S (ua e i)) s t
    ≃⟨ invEquiv (Σ-contractSnd λ _ → isContrRetract (equivRetracts (PathP≃Path _ _ _)) (isProp→isContrPath (axioms-are-Props _ _) _ _)) ⟩
  Σ[ p ∈ PathP (λ i → S (ua e i)) s t ] PathP (λ i → axioms (ua e i) (p i)) a b
    ≃⟨ ΣPath≃PathΣ ⟩
  PathP (λ i → AxiomsStructure S axioms (ua e i)) (s , a) (t , b)
  ■
```

We can now use our new axiom structure to extend the raw monoid structure
to a full monoid with all of its axioms.

```
MonoidAxioms : (M : Type) → RawMonoidStructure M → Type
MonoidAxioms M (e , _·_) = IsSemigroup _·_ × ((x : M) → (x · e ≡ x) × (e · x ≡ x))

MonoidStructure : Type → Type
MonoidStructure = AxiomsStructure RawMonoidStructure MonoidAxioms

Monoid : Type₁
Monoid = TypeWithStr ℓ-zero MonoidStructure

MonoidEquiv : (M N : Monoid) → fst M ≃ fst N → Type
MonoidEquiv (_ , (εᴹ , _·_) , _) (_ , (εᴺ , _∗_) , _) (φ , _) =
  (φ εᴹ ≡ εᴺ) × (∀ x y → φ (x · y) ≡ (φ x) ∗ (φ y))

MonoidEquivStr : StrEquiv MonoidStructure ℓ-zero
MonoidEquivStr = AxiomsEquivStr RawMonoidEquivStr MonoidAxioms

isPropIsSemigroup : {A : Type ℓ} (_·_ : A → A → A) → isProp (IsSemigroup _·_)
isPropIsSemigroup = {!   !}

isPropMonoidAxioms : (M : Type) (s : RawMonoidStructure M) → isProp (MonoidAxioms M s)
isPropMonoidAxioms M (e , _·_) =
  isPropΣ
  (isPropIsSemigroup _·_)
  (λ α → isPropΠ λ _ → isProp× (IsSemigroup.is-set α _ _) (IsSemigroup.is-set α _ _))

monoidUnivalentStr : UnivalentStr MonoidStructure MonoidEquivStr
monoidUnivalentStr = axiomsUnivalentStr _ isPropMonoidAxioms rawMonoidUnivalentStr
```

Now we have shown that monoids are indeed univalent. The only thing left
to apply the SIP on monoids is proving the SIP. First, we define a new operator
for equivalences between structures, to make the proof more readable.

```
_≃[_]_ : (A : TypeWithStr ℓ S) (ι : StrEquiv S ℓ') (B : TypeWithStr ℓ S) → Type (ℓ-max ℓ ℓ')
A ≃[ ι ] B = Σ[ e ∈ typ A ≃ typ B ] (ι A B e)

module _ {S : Type ℓ → Type ℓ'} {ι : StrEquiv S ℓ''}
  (θ : UnivalentStr S ι) (A B : TypeWithStr ℓ S)
  where

  SIP : (A ≃[ ι ] B) ≃ (A ≡ B)
  SIP = compEquiv ΣPath≃PathΣ (Σ-map-≃ (invEquiv univalence) θ)
  
  sip : (A ≃[ ι ] B) → A ≡ B
  sip = equivFun SIP

  sipInv : A ≡ B → A ≃[ ι ] B
  sipInv = equivSec SIP
```

And finally the proof for MonoidΣPath becomes trivial.

```
MonoidΣPath : (M N : Monoid) → (M ≃[ MonoidEquivStr ] N) ≃ (M ≡ N)
MonoidΣPath = SIP monoidUnivalentStr
```

Next, we will take a look at an application of the MonoidΣPath.
We will define monads for the natural numbers in unary and binary
representations and then transport various proofs between them given
this equivalence. This is extremely useful because the representations
have different advantages. The Peano structure of the unary natural
numbers is advantageous for proof theoretic objectives while the
structure of binary numbers is stronger in computational aspects.
For instance, checking whether a binary number is even or odd is
an O(1) operation, even for numbers as large as 2^120. Meanwhile,
checking whether 2^120 is even using a unary representation will
crash your computer.


First, we prepare the proofs for associativity and the identity for
the unary natural number monoid. 

```
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-zero : ∀ m → m + 0 ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)
```

Now, constructing it becomes easy.

```
unaryℕMonoid : Monoid
fst unaryℕMonoid = ℕ
snd unaryℕMonoid = ((0 , _+_)) , unaryMonoidAxioms
    where
    unaryMonoidAxioms : MonoidAxioms ℕ (0 , _+_)
    unaryMonoidAxioms = (issemigroup isSetℕ +-assoc) , (λ x → (+-zero x) , refl)
```

For the binary natural numbers, we will cheat a little bit and
transport their addition as well as other properties from the
unary natural numbers and use that to construct the monoid.

```
-- Forward declaration needed for cyclic depdency
data Binℕ : Type
data Pos : Type

data Binℕ where
  binℕ0   : Binℕ
  binℕpos : Pos → Binℕ

data Pos where
  x0   : Pos  → Pos  -- shifts a positive binary number left (multiplying by 2).
  x1   : Binℕ → Pos  -- shifts a binary number left and adds 1 (encoding the binary digit 1).

-- pos1 is a pattern for the positive binary number 1.
pattern pos1 = x1 binℕ0

-- x1-pos n is a pattern for creating a positive binary number where the least significant bit is 1.
pattern x1-pos n = x1 (binℕpos n)
```

We construct the components of an isomorphism between the unary
and binary natural numbers. Feel free to skip the details here.

```
Binℕ⇒Pos : Binℕ → Pos
sucPos : Pos → Pos
Binℕ⇒Pos binℕ0 = pos1
Binℕ⇒Pos (binℕpos n) = sucPos n
sucPos (x0 ps) = x1-pos ps
sucPos (x1 ps) = x0 (Binℕ⇒Pos ps)

Binℕ→ℕ : Binℕ → ℕ
Pos⇒ℕ : Pos → ℕ
Pos→ℕ : Pos → ℕ

Binℕ→ℕ binℕ0       = zero
Binℕ→ℕ (binℕpos x) = Pos→ℕ x

Pos→ℕ ps            = suc (Pos⇒ℕ ps)

doubleℕ : ℕ → ℕ
doubleℕ zero    = zero
doubleℕ (suc n) = suc (suc (doubleℕ n))

Pos⇒ℕ (x0 ps) = suc (doubleℕ (Pos⇒ℕ ps))
Pos⇒ℕ (x1 ps) = doubleℕ (Binℕ→ℕ ps)

posInd : {P : Pos → Type₀} → P pos1 → ((p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
posInd {P} h1 hs ps = f ps
  where
  H : (p : Pos) → P (x0 p) → P (x0 (sucPos p))
  H p hx0p = hs (x1-pos p) (hs (x0 p) hx0p)

  f : (ps : Pos) → P ps
  f pos1    = h1
  f (x0 ps) = posInd (hs pos1 h1) H ps
  f (x1-pos ps) = hs (x0 ps) (posInd (hs pos1 h1) H ps)

Binℕ⇒Pos⇒ℕ : (p : Binℕ) → Pos⇒ℕ (Binℕ⇒Pos p) ≡ Binℕ→ℕ p
Binℕ⇒Pos⇒ℕ binℕ0 = refl
Binℕ⇒Pos⇒ℕ (binℕpos (x0 p)) = refl
Binℕ⇒Pos⇒ℕ (binℕpos (x1 x)) = λ i → suc (doubleℕ (Binℕ⇒Pos⇒ℕ x i))

Pos⇒ℕsucPos : (p : Pos) → Pos⇒ℕ (sucPos p) ≡ suc (Pos⇒ℕ p)
Pos⇒ℕsucPos p = Binℕ⇒Pos⇒ℕ (binℕpos p)

Pos→ℕsucPos : (p : Pos) → Pos→ℕ (sucPos p) ≡ suc (Pos→ℕ p)
Pos→ℕsucPos p = cong suc (Binℕ⇒Pos⇒ℕ (binℕpos p))

ℕ⇒Pos : ℕ → Pos
ℕ⇒Pos zero    = pos1
ℕ⇒Pos (suc n) = sucPos (ℕ⇒Pos n)

ℕ→Pos : ℕ → Pos
ℕ→Pos zero = pos1
ℕ→Pos (suc n) = ℕ⇒Pos n

Pos⇒ℕ⇒Pos : (p : Pos) → ℕ⇒Pos (Pos⇒ℕ p) ≡ p
Pos⇒ℕ⇒Pos p = posInd refl hs p
  where
  hs : (p : Pos) → ℕ⇒Pos (Pos⇒ℕ p) ≡ p → ℕ⇒Pos (Pos⇒ℕ (sucPos p)) ≡ sucPos p
  hs p hp =
    ℕ⇒Pos (Pos⇒ℕ (sucPos p)) ≡⟨ cong ℕ⇒Pos (Pos⇒ℕsucPos p) ⟩
    sucPos (ℕ⇒Pos (Pos⇒ℕ p)) ≡⟨ cong sucPos hp ⟩
    sucPos p ∎

ℕ⇒Pos⇒ℕ : (n : ℕ) → Pos⇒ℕ (ℕ⇒Pos n) ≡ n
ℕ⇒Pos⇒ℕ zero = refl
ℕ⇒Pos⇒ℕ (suc n) =
  Pos⇒ℕ (ℕ⇒Pos (suc n)) ≡⟨ Pos⇒ℕsucPos (ℕ⇒Pos n) ⟩
  suc (Pos⇒ℕ (ℕ⇒Pos n)) ≡⟨ cong suc (ℕ⇒Pos⇒ℕ n) ⟩
  suc n ∎

ℕ→Binℕ : ℕ → Binℕ
ℕ→Binℕ zero    = binℕ0
ℕ→Binℕ (suc n) = binℕpos (ℕ⇒Pos n)

ℕ→Binℕ→ℕ : (n : ℕ) → Binℕ→ℕ (ℕ→Binℕ n) ≡ n
ℕ→Binℕ→ℕ zero = refl
ℕ→Binℕ→ℕ (suc n) = cong suc (ℕ⇒Pos⇒ℕ n)

Binℕ→ℕ→Binℕ : (n : Binℕ) → ℕ→Binℕ (Binℕ→ℕ n) ≡ n
Binℕ→ℕ→Binℕ binℕ0 = refl
Binℕ→ℕ→Binℕ (binℕpos p) = cong binℕpos (Pos⇒ℕ⇒Pos p)
```

Next, we use univalence to show equivalence and transport addition.

```
-- We derive an equivalence from the isomorphism
Binℕ≃ℕ : Binℕ ≃ ℕ
Binℕ≃ℕ = equiv Binℕ→ℕ ℕ→Binℕ ℕ→Binℕ→ℕ Binℕ→ℕ→Binℕ

-- We use univalence to get an equality from the above equivalence
Binℕ≡ℕ : Binℕ ≡ ℕ
Binℕ≡ℕ = ua Binℕ≃ℕ

-- We transport addition on ℕ to Binℕ
_+Binℕ_ : Binℕ → Binℕ → Binℕ
_+Binℕ_ = transport (λ i → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i)) _+_

addp : PathP (λ i → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i) → Binℕ≡ℕ (~ i)) _+_ _+Binℕ_
addp i = transp (λ j → Binℕ≡ℕ (~ i ∨ ~ j) → Binℕ≡ℕ (~ i ∨ ~ j) → Binℕ≡ℕ (~ i ∨ ~ j)) (~ i) _+_

+-assoc-Binℕ : ∀ m n o → m +Binℕ (n +Binℕ o) ≡ (m +Binℕ n) +Binℕ o
+-assoc-Binℕ = transport (λ i → (m n o : Binℕ≡ℕ (~ i)) → addp i m (addp i n o) ≡ addp i (addp i m n) o) +-assoc

+-zero-Binℕ : ∀ m → m +Binℕ binℕ0 ≡ m
+-zero-Binℕ = {!!}

+-zero-Binℕ' : ∀ m → binℕ0 +Binℕ m ≡ m
+-zero-Binℕ' = {!!}

isSet-Binℕ : isSet Binℕ
isSet-Binℕ x y = {!!}

-- Test: 4 + 1 = 5
private
  _ : binℕpos (x0 (x0 pos1)) +Binℕ binℕpos pos1 ≡ binℕpos (x1-pos (x0 pos1))
  _ = refl
```

It is now time to define our binaryℕMonoid and provide a path
between unaryℕMonoid and binaryℕMonoid.

```
binaryℕMonoid : Monoid
fst binaryℕMonoid = Binℕ
snd binaryℕMonoid = ((binℕ0 , _+Binℕ_)) , binaryℕMonoidAxioms
  where
  binaryℕMonoidAxioms : MonoidAxioms Binℕ (binℕ0 , _+Binℕ_)
  binaryℕMonoidAxioms = ((issemigroup isSet-Binℕ +-assoc-Binℕ)) , λ x → (+-zero-Binℕ x) , (+-zero-Binℕ' x)

unary-binary-ℕ-MonoidPath : binaryℕMonoid ≡ unaryℕMonoid  
unary-binary-ℕ-MonoidPath = MonoidΣPath binaryℕMonoid unaryℕMonoid .fst unarybinaryℕMonoidEquiv
    where

    unarybinaryℕMonoidEquiv : binaryℕMonoid ≃[ MonoidEquivStr ] unaryℕMonoid
    fst (unarybinaryℕMonoidEquiv) = Binℕ≃ℕ
    snd (unarybinaryℕMonoidEquiv) = (identityProof , operationProof)
      
      where
      identityProof : (Binℕ→ℕ binℕ0) ≡ 0
      identityProof = refl
      
      operationProof : ∀ x y → Binℕ→ℕ (x +Binℕ y) ≡ (Binℕ→ℕ x + Binℕ→ℕ y)
      operationProof x y = {!!}        
```

Finally, we give the constant time functions to determine whether a binary
natural number is even or odd, and transport it to unary natural numbers.

```
oddBinℕ : Binℕ → Bool
oddBinℕ binℕ0            = false
oddBinℕ (binℕpos (x0 _)) = false
oddBinℕ (binℕpos (x1 _)) = true

sucBinℕ : Binℕ → Binℕ
sucBinℕ x = binℕpos (Binℕ⇒Pos x)

evenBinℕ : Binℕ → Bool
evenBinℕ n = oddBinℕ (sucBinℕ n)
```

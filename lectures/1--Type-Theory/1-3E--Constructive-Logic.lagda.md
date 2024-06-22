```
module 1--Type-Theory.1-3E--Constructive-Logic where
```

# Lecture 1-3 Extra: Constructive Logic

```
open import Library.Prelude
open import 1--Type-Theory.1-X--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-3--Propositions-as-Types
```

Lots of properties stay the same from ordinary logic, here's a
collection. Some of these are tough! Most of these won't be used
later, so you can comment them out if you get stuck.

```
¬-not-both : {ℓ : Level} → {P : Type ℓ} → ¬ (P × (¬ P))
-- Exercise:
¬-not-both x = ?

¬¬-map : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → ¬ ¬ (P → Q) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-map f = ?

¬¬-func : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-func f = ?

¬¬-bind : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → (P → (¬ ¬ Q)) → ((¬ ¬ P) → (¬ ¬ Q))
-- Exercise:
¬¬-bind f nnp nq = ?
```

Some classical facts *almost* hold, in that we can prove them once
they are surrounded by `¬ ¬`. For both of these, you will need to use
`∅-rec`{.Agda} once you have proven a contradiction.

mvrnote: mention double negation translation?

```
¬¬-implies¬¬ : {ℓ : Level} → {P : Type ℓ} → ¬ ¬ ((¬ ¬ P) → P)
-- Exercise: bit tricky!
¬¬-implies¬¬ f = ?

¬¬-pierce : {ℓ ℓ' : Level} {P : Type ℓ} {Q : Type ℓ'} → ¬ ¬ (((P → Q) → P) → P)
-- Exercise: bit tricky!
¬¬-pierce f = ?
```

The proof of the following works on a similar principle to the proof
of `¬¬LEM`{.Agda}: suppose you have one side and then use it to prove
the other.

```
¬¬-weird : {ℓ : Level} (P Q : Type ℓ) → ¬ ¬ ( (P → Q) ⊎ (Q → P))
-- Exercise:
¬¬-weird P Q x = {!!}
```

Admittedly, decidable types will not be so important for us in the
future, but they are an excellent font of exercises involving
propositions and truncations:

```
Dec→¬¬Stable : {ℓ : Level} {A : Type ℓ} → Dec A → (¬ ¬ A → A)
-- Exercise:
Dec→¬¬Stable d = {!!}

Dec-extract : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → Dec B → ¬ ¬ (A → B) → (A → B)
-- Exercise:
Dec-extract d f = {!!}

Dec-Idem : {ℓ : Level} {A : Type ℓ} → Dec (Dec A) → Dec A
-- Exercise:
Dec-Idem d = {!!}
```

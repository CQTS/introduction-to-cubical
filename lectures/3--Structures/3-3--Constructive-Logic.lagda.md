<!--
```
module 3--Structures.3-3--Constructive-Logic where

-- mvrnote: check redundant imports/variables
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-4--Propositions-as-Types
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
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B : A → Type ℓ
```
-->

# Lecture 3-3: Constructive Logic

mvrnote: global choice implies excluded middle
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#global-choice

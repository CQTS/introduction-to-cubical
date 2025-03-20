<!--
```
module 3--Topics.3-3--Constructive-Logic where

-- mvrnote: check redundant imports/variables
open import Library.Prelude
open import 1--Type-Theory.1-1--Types-and-Functions
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universes-and-More-Inductive-Types
open import 1--Type-Theory.1-5--Propositions-as-Types
open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets-and-Higher-Types
open import 2--Paths-and-Identifications.2-9--Contractible-Maps

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B : A → Type ℓ
```
-->

# Lecture 3-3: Constructive Logic

mvrnote: under construction

mvrnote: global choice implies excluded middle
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#global-choice

https://mathoverflow.net/questions/391996/assuming-decidable-equality-but-not-lem-in-hott
Note that Σ𝐴
 is the same set that appears in the Diaconescu-Goodman-Myhill proof that the axiom of choice implies excluded middle. –
Mike Shulman
 CommentedMay 12, 2021 at 15:51
2
@MikeShulman: and indeed the D–G–M proof can usefully be factored as “If all subsets of A satisfy choice, then A has decidable equality” (which doesn’t need general quotients/suspension, just propositional truncation) and “if all sets have decidable equality, then LEM holds” (using set quotients/suspension as you say). –
Peter LeFanu Lumsdaine
 CommentedMay 12, 2021 at 17:42

https://arxiv.org/pdf/1602.04530
https://people.mpi-sws.org/~dreyer/papers/pedrot-exceptional/paper.pdf

https://inria.hal.science/hal-04584831/file/cohen-forster-kirst-paiva-rahli-separating-markovs-principles-lics24.pdf

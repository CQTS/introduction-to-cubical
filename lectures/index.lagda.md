```
module index where
```

Introduction to Cubical Type Theory in Agda
===========================================

All of these module names are links you can click.

mvrnote: explain which files are required and which are independent (once we know)

```
open import 1--Type-Theory.1-1--Types-and-Functions -- Start here!
open import 1--Type-Theory.1-2--Inductive-Types
open import 1--Type-Theory.1-3--Universe-Levels-and-More-Inductive-Types
open import 1--Type-Theory.1-3E--Extras
open import 1--Type-Theory.1-4--Propositions-as-Types

open import 2--Paths-and-Identifications.2-1--Paths
open import 2--Paths-and-Identifications.2-2--Equivalences-and-Path-Algebra
open import 2--Paths-and-Identifications.2-3--Substitution-and-J
open import 2--Paths-and-Identifications.2-4--Composition-and-Filling
open import 2--Paths-and-Identifications.2-4E--More-with-hcomps
open import 2--Paths-and-Identifications.2-5--Transport
open import 2--Paths-and-Identifications.2-6--Univalence
open import 2--Paths-and-Identifications.2-7--Propositions
open import 2--Paths-and-Identifications.2-8--Sets
open import 2--Paths-and-Identifications.2-9--Contractible-Maps
-- open import 2--Paths-and-Identifications.2-8E--Embeddings-and-Surjections
open import 2--Paths-and-Identifications.2-10--Higher-Types

-- open import 3--Structures.3-1--Structure-Identity-Principle
```

## Troubleshooting Agda

mvrnote: collect common issues
* Variable not in scope because you undo filling a hole
* _I can't input Unicode characters in Emacs any more!_ You may have
   accidentally disabled the input mode, type `C-\` to turn it on
   again.

## Differences to other cubical libraries

Cubical:
* We use biinvertible map for equivalence
* `fiber` has the path flipped to usual
* `compEquiv` uses non-diagrammatic order
* We don't define `hfill` in general, just the special cases that we
  need. This is to avoid introducing cubical subtypes

## Attribution

This course was written by David Jaz Myers and Mitchell Riley.

The online notes use the infrastructure of the [1lab](https://1lab.dev/), by
Amélia Liao, to typeset and link everything nicely.

Content and exercises were inspired by (stolen from) many sources, in
particular:

* The [`cubical` Agda library](https://github.com/agda/cubical) by Anders Mörtberg, Felix Cherubini, Evan Cavallo, Axel Ljungström and others
* The [1lab](https://1lab.dev/) by Amélia Liao, Astra Kolomatskaia, Reed Mullanix and others
* The [Cubical Agda tutorial](https://github.com/martinescardo/HoTTEST-Summer-School/tree/main/Agda/Cubical) at the [HoTTEST Summer School 2022](https://www.uwo.ca/math/faculty/kapulkin/seminars/hottest_summer_school_2022.html) by Anders Mörtberg
* The [`cubicaltt` tutorial](https://github.com/mortberg/cubicaltt/tree/master/lectures) by Anders Mörtberg
* [Cubical Synthetic Homotopy Theory](https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf) by Anders Mörtberg and Loïc Pujet
* [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) by Martín Escardó
* [Introduction to Homotopy Type Theory](https://arxiv.org/abs/2212.11082) by Egbert Rijke
* mvrnote: favonia's notes

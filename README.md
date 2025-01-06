# Introduction to Homotopy Type Theory in Cubical Agda

*by David Jaz Myers and Mitchell Riley, with contributions from Wen
Rahme and Zyad Yasser Hassan. Supported by [Tamkeen] under the [NYUAD
Research Institute] grant `CG008`.*

This course teaches the fundamentals of [Homotopy Type Theory] through
hands-on experience with the [Agda] proof assistant and its [cubical]
features.

Homotopy Type Theory type systems whose types are interpreted as
spaces that can have higher dimensional structure, rather than mere
sets or discrete collections of elements. In ordinary mathematics the
notion of space is defined from more basic building blocks, but in
HoTT, all constructions that we can perform have an intrinsic spacial
nature. One way to view HoTT is as an alternative foundation for
mathematics where everything is "natively homotopical".

A type system is much like a programming language, and as with any
programming language, computer tools can help us write our work and
check its correctness. Throughout these notes, we will be using the
programming language and proof assistant called Agda. Agda lets us
develop our proofs interactively: at each step, Agda keeps track of
what we have done and what part of the argument needs to be handled
next.

In the first versions of HoTT, the higher-dimensional structure of
types is made accessible by the [univalence axiom], which explains
what it means for two types to be connected by an equality. This axiom
is left as an unproven assumption, so any construction that uses it
may become "stuck" when evaluated and not completely reduce to an
answer. This is unsatisfying: we have a programming language where not
every program that promises to return an integer will actually produce
an explicit number when evaluated.

Cubical Type Theory is an extension of HoTT whose central achievement
is a computational interpretation of this univalence axiom: the
univalence axiom becomes a *theorem* that has computational content,
and programs that use it are guaranteed to not get stuck. In this
extension, paths are represented as functions from a special
"interval" type, and higher-dimensional structures --- like paths
between paths --- arise as functions from products of intervals,
forming cubes.

The course has three parts.

1. **Part 1:** An introduction to dependent type theory, independent
   of any cubical features or homotopy theory. This covers functions,
   inductive types and pattern matching, records, and the
   "propositions-as-types" paradigm.
2. **Part 2:** A tutorial on the cubical features of Cubical Agda,
   covering paths, higher inductive types, transport, composition and
   univalence.
3. **Part 3:** Lectures on topics at the frontier of HoTT research,
   which can be read and completed independently of each other. There
   are currently three topics covered.
    - **The Structure Identity Principle**, following [Angiuli,
      Cavallo, Mörtberg and Zeuner]
    - **Modalities**, following [Rijke, Shulman and Spitters]
    - **Constructive Logic**, following ?


[Tamkeen]: https://www.tamkeenuae.com/projects/nyuad.html
[NYUAD Research Institute]: https://nyuad.nyu.edu/en/research/faculty-labs-and-projects/cqts.html
[Homotopy Type Theory]: https://homotopytypetheory.org/
[Agda]: https://wiki.portal.chalmers.se/agda/pmwiki.php
[cubical]: https://agda.readthedocs.io/en/latest/language/cubical.html
[univalence axiom]: https://ncatlab.org/nlab/show/univalence+axiom
[Angiuli, Cavallo, Mörtberg and Zeuner]: https://dl.acm.org/doi/10.1145/3434293
[Rijke, Shulman and Spitters]: https://lmcs.episciences.org/6015


## Getting Started

To edit Agda files, you will need to install Agda and an editor that
supports `agda-mode`: currently that is either VSCode or Emacs.
Detailed installation instructions are given
[here](INSTALLING_AGDA.html).

Once your editor is set up, clone or download [this repository] and
open the file

    lectures/1--Type-Theory/1-1--Types-and-Functions.lagda.md 

in your editor to get started.

::: Caution:
The notes are intended to be read either on the website or in your
editor. Reading directly on GitHub is not recommended; the formatting
and code highlighting does not work correctly.
:::

[this repository]: https://github.com/CQTS/introduction-to-cubical


## Why Another Agda Course?

I don't know, but too much cost has been sunk to stop now.


## Goals of this Course

These notes were written with the following goals in mind.

* **Be readable linearly**: These notes are not a reference text,
  rather, they are designed to be read front-to-back. Effort has gone
  into ordering the concepts that are introduced so that nothing is
  used before it can be properly explained in isolation.
* **Provide innumerable exercises**: Most proofs are left as exercises,
  with hints provided as necessary. 
* **Avoid black boxes**: There are no postulates or big "trust me!"
  results that are never explained or put off until later. Every
  exercise is possible with only the tools readers have proven
  themselves before that point.
* **Be readable without a tutor**: The notes should be understandable,
  and the exercises possible to complete, without in-person help from
  an experienced Cubical Agda user. mvrnote: we may not have achieved
  this
* **Cover some meaty topics**: After the reader has finished these
  notes, we want them to feel prepared to read work that is on the
  forefront of research in Homotopy Type Theory and Cubical Agda. We
  believe that the topics lectures in Part 3 will get them there.

On the other hand, we are not concerned with any of the following
goals. We:

* **Don't cover implementation details**: We consider Cubical Type
  Theory mostly as a background theory in which to teach Homotopy Type
  Theory, in particular, we do not discuss cubical subtypes and
  filling in the maximum possible generality.
* **Don't stay compatible with other Agda libraries**: We use
  different names and different definitions to existing Agda
  libraries, whenever this improves readability.
* **Don't showcase Agda's features**: We don't discuss Agda's powerful
  modules, typeclasses, modalities, reflection faculties; anything not
  related to Agda's cubical features.
* **Don't optimise performance**: The definitions we use are not
  chosen with either type-checking or normalisation performance in
  mind. In some places faster options are available, but were avoided
  for being more complex or for sequencing reasons.

## License

???

## Comparison with other Cubical Agda libraries

mvrnote: For experts

* We use biinvertible map for equivalence
* ``fiber`` has the path flipped to usual
* ``∘e`` i.e. `compEquiv` uses non-diagrammatic order
* We don't go into detail on cubical subtypes
* Consequently, we don't prove `hfill` in general, just the special
  cases that we need
* The type used in ``idfun`` is implicit
* ``→-map-≃`` takes the domain equivalence flipped to avoid some path
  algebra, letting us introduce it earlier
* We use ``⊤`` and ``∅`` for the unit type and empty type respectively
* We use "1-lab style" ``hcomp``, so that the bottom face is provided
  as part of the partial element.
* ``FunctionEquivStr`` doesn't use implicit arguments, so we don't
  have to fuss around with an implicit version of ``Π-map-cod≃``


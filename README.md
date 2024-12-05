# Introduction to Cubical Type Theory in Agda

by David Jaz Myers and Mitchell Riley, with contributions from Wen
Rahme and Zyad Yasser Hassan.

Supported by Tamkeen under the NYUAD Research Institute grant `CG008`.

## Getting Started

Clone or download [this repository] and open the file

    lectures/1--Type-Theory/1-1--Types-and-Functions.lagda.md 

in your editor to get started.

[this repository]: https://github.com/CQTS/introduction-to-cubical

To edit Agda files, you will need to install Agda and an editor that
supports `agda-mode`: currently that is either VSCode or Emacs.
Detailed instructions are given [here](INSTALLING_AGDA.html).

## Why another Agda Course?

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

* **Don't stay compatible with other libraries**: We use different names
  and slightly different definitions to existing Agda libraries,
  whenever that improves readability of the text.
* **Don't showcase Agda's features**: We don't discuss Agda's powerful
  module system, typeclasses, modalities, reflection, anything not
  related to Agda's cubical features.
* **Don't optimise performance**: The definitions we use were not chosen
  with either type-checking or normalisation performance in mind. In
  some places much faster choices are available, but were avoided for
  being more complex, or for sequencing reasons.

## License

???

## Comparison with other Cubical Agda libraries

mvrnote: For experts

* We use biinvertible map for equivalence
* ``fiber`` has the path flipped to usual
* ``∘e`` i.e. `compEquiv` uses non-diagrammatic order
* We don't introduce or use cubical subtypes
* Consequently, we don't prove `hfill` in general, just the special
  cases that we need
* The type used in ``idfun`` is implicit
* ``→-map-≃`` takes the domain equivalence flipped to avoid some path
  algebra, letting us introduce it earlier
* We use ``⊤`` and ``∅`` for the unit type and empty type respectively
* We use "1-lab style" ``hcomp``, so that the bottom face is provided
  with the partial element.
* ``FunctionEquivStr`` doesn't use implicit arguments, so we don't
  have to fuss around with an implicit version of ``Π-map-cod≃``


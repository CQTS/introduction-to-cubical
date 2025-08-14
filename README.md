# Introduction to Homotopy Type Theory in Cubical Agda

<div style="display:flex;">
<div style="flex: 50%; align-self: center;">

*by David Jaz Myers and Mitchell Riley, with contributions from Wen
Rahme. Supported by [Tamkeen] under the [NYUAD Research Institute]
grant `CG008`.*

</div>
<div style="flex: 50%;">

![CQTS](images/cqts.png)

</div>
</div>

This course teaches the fundamentals of [Homotopy Type Theory] through
hands-on experience with the [Agda] proof assistant and its [cubical]
features.

Homotopy Type Theory (HoTT) is a type system whose types behave like
spaces that can have higher dimensional features, rather than mere
sets or collections of discrete elements. Ordinary mathematics builds
the notion of space from more basic building blocks, but in HoTT, all
constructions that we perform have an intrinsic spacial nature. One
way to view HoTT is as an alternative foundation for mathematics where
everything is "natively homotopical".

A type system is much like a programming language, and as with any
programming language, computer tools can help us write our work and
check its correctness. Throughout these notes, we will be using
[Agda], a programming language with an associated "proof assistant".
Agda lets us develop our proofs interactively: at each step, Agda
keeps track of what we have done and what part of the argument needs
to be dealt with next.

In the first versions of HoTT, the higher-dimensional structure of
types is made accessible by the [univalence axiom], which explains
what it means for two types to be equal. This axiom is provided as an
unproven assumption, so any construction that uses it may become
"stuck" when evaluated and not completely reduce to an answer. This is
unsatisfying: we have a programming language where not every program
that promises to produce an integer will actually produce an explicit
number when evaluated.

Cubical Type Theory is an extension of HoTT whose central achievement
is a computational interpretation of this univalence axiom: the
univalence axiom becomes a *theorem* that has computational content,
and programs that use it are guaranteed to not get stuck. In this
extension, paths are represented as functions from a special
"interval" type, and higher-dimensional structures --- like paths
between paths --- arise as functions from products of intervals,
forming cubes.

The course has three parts.

- **Part 1:** An introduction to dependent type theory, independent of
  any cubical features or homotopy theory. This covers functions,
  inductive types and pattern matching, records, and the
  "propositions-as-types" paradigm.
- **Part 2:** A tutorial on the cubical features of Cubical Agda,
  covering paths, higher inductive types, transport, composition and
  univalence.
- **Part 3:** (Under construction.) Lectures on topics at the frontier
  of HoTT research, which can be read and completed independently of
  each other. There are currently three topics covered.
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


## How to Complete this Course

These notes are not a reference text, rather, they are designed to be
read front-to-back starting with Lecture 1-1. Each Lecture is
accessible by clicking the links in the menu to the left.

To read Agda files, you will need to install Agda and an editor that
supports `agda-mode`: currently that is either [VSCode] or [Emacs].
Detailed installation instructions are given
[here](INSTALLING_AGDA.html).

Once your editor is ready, clone or download [this repository] and
open the file

    lectures/1--Type-Theory/1-1--Types-and-Functions.lagda.md 

in your editor to get started.

Each section ends with links and references to other resources. There
is a good chance these other sources present topics in a different
order to the one we have chosen, but it may still come in handy to see
the content presented in a different way.

::: Caution:
The notes are intended to be read either on the website or in your
editor. Reading directly on GitHub is not recommended; the formatting
and code highlighting does not work correctly.
:::

[VSCode]: https://code.visualstudio.com/
[Emacs]: https://www.gnu.org/software/emacs/
[this repository]: https://github.com/CQTS/introduction-to-cubical


## Goals of this Course

These notes were written with the following goals in mind. The
lectures should:

* **Be readable linearly**: Concepts introduced in this course are
  carefully sequenced so that nothing is used before it can be
  properly explained in isolation.
* **Provide innumerable exercises**: Most proofs are left to the
  reader to complete, with hints provided as necessary.
* **Avoid black boxes**: There are no postulates or big "trust me!"
  results that are unexplained or put off until later. Every exercise
  is possible with only the results readers have proven themselves
  before that point.
* **Be readable without a tutor**: The notes should be understandable,
  and the exercises possible to complete, without in-person help from
  an experienced Cubical Agda user. 
* **Cover some meaty topics**: After the reader has finished these
  notes, they should feel prepared to read work that is on the
  forefront of research in Homotopy Type Theory and Cubical Agda. We
  believe that the topics lectures in Part 3 will get them there.

On the other hand, we are not focused on any of the following goals
goals. These notes:

* **Don't cover implementation details**: We consider Cubical Type
  Theory mostly as a background theory in which to teach Homotopy Type
  Theory, in particular, we do not discuss cubical subtypes and
  filling problems in the maximum possible generality.
* **Don't stay compatible with other Agda libraries**: We use
  different names and different definitions to existing Agda
  libraries whenever this improves readability.
* **Don't showcase Agda's features**: We don't discuss Agda's powerful
  module system, typeclasses, modalities, reflection features.
* **Don't optimise performance**: The definitions we use are not
  chosen with type-checking or normalisation performance in mind. In
  some places faster options are available, but were avoided for
  complexity or sequencing reasons.

## License

This work is licensed under a
[Creative Commons Attribution-NonCommercial 4.0 International License][cc-by-nc].

[cc-by-nc]: https://creativecommons.org/licenses/by-nc/4.0/

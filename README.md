We use techniques from denotational semantics to prove the well-known fact that the Gödel's System T definable functions on the Baire type (ℕ → ℕ) with values on the natural numbers are continuous, and their retriction to the Cantor type (ℕ → 𝟚) are uniformly continuous.

This repository has both the source of [the paper](https://doi.org/10.1016/j.entcs.2013.09.010) and associated Agda files.

* [How to cite this paper](HowToCite.bib)

* The directory [latex](latex) has the literate Agda file that generates the latex file and the pdf file of [the paper](https://doi.org/10.1016/j.entcs.2013.09.010).

* The directory [source](source) has various Agda files:

  1. [laconic-dialogue](source/laconic-dialogue.lagda) is the above literate Agda file with the comments removed. This works with the combinatory combinatory version of system T.

  1. [dialogue-lambda](source/dialogue-lambda.lagda) works with the lambda-calculus version of system T instead. Additionally, we now let `Rec` be the primitive recursion combinator rather than the iteration combinator.

  1. [dialogue-lambda-internal](source/dialogue-lambda-internal.lagda) internalizes this to system T using Church encoding of dialogue trees in system T rather than external inductive definition of such trees.

  1. [church-dialogue](source/dialogue-lambda-internal.lagda) variation of the above.

  1. [church-dialogue-internal](source/dialogue-lambda-internal.lagda) variation of the above.

  1. [dialogue-without-oracle](source/dialogue-without-oracle.agda) is a file by Vincent Rahli (2015) that shows how to get rid of the use of oracles.

  1. [dialogue-to-brouwer](dialogue-to-brouwer.lagda), by Paulo Oliva and me (2017) converts from dialogue trees to Brouwer trees.

* [Renderings in html](https://www.cs.bham.ac.uk/~mhe/dialogue/) at my institutional web page.

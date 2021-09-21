We use techniques from denotational semantics to prove the well-known result that the Goedel's System T definable functions on the Baire type with values on the natural numbers are continuous, and their retriction to the Cantor type are uniformly continuous.

* Cite as M. H. Escardo. "Continuity of Godel's system T functionals via effectful forcing". Proceedings of MFPS'2013. Electronic Notes in Theoretical Computer Science 01/2013, volume 298, pages 119-141.

* The directory [latex](latex) has the literate Agda file that generates the latex file and the pdf file of the [paper](https://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.pdf).

* The directory [source](source) has various agda files:

  1. [laconic-dialogue](laconic-dialogue.lagda) is the above literate Agda file with the comments removed. This works with the combinatory combinatory version of system T.

  1. [dialogue-lambda](dialogue-lambda.lagda) works with the lambda-calculus version of system T instead. Additionally, we now let `Rec` be the primitive recursion combinator rather than the iteration combinator.

  1. [dialogue-lambda-internal](dialogue-lambda-internal.lagda) internalizes this to system T using Church encoding of dialogue trees in system T rather than external inductive definition of such trees.

  1. [church-dialogue](dialogue-lambda-internal.lagda) variation of the above.

  1. [church-dialogue-internal](dialogue-lambda-internal.lagda) variation of the above.

* [Renderings in html](https://www.cs.bham.ac.uk/~mhe/dialogue/) at my institutional web page.

# A formalization of type theory in Coq

This Coq library formalizes dependent type theory in the style of Per Martin-Löf. The
formalization is *configurable* in the sense that various components can be turned on or
off, or be left ambivalent. It is thus easy to instantiate many variants of type theory,
such as extensional vs. intensional, with or without universes, etc. The library also
formalizes several meta-theorems about type theory.

## Requirements

### Requirements for compiling the library

The library works with Coq 8.6, and probably with many other recent versions as well, as
it does not use any special features of Coq. You may find out about the best way to install Coq at the [Coq web site](If you do not have Coq, visit).

To compile the library you need Coq and [`make`](https://www.gnu.org/software/make/).

### Requirements for generating the LaTeX version of rules

In order to generate the LaTeX version of the rules you
need [Python](https://www.python.org) (either version 2.7 or 3.x) and (obviously) LaTeX,
as well as the [mathpartir](http://cristal.inria.fr/~remy/latex/) package
by [Didier Rémy](http://cristal.inria.fr/~remy/).

Since the `mathpartir` package is GNU-licensed, and we do not want a viral license, the
compilation script attempts to download it using the `curl` and `wget` commands. If
neither is available, you will have
to [download `mathpartir` manually](http://cristal.inria.fr/~remy/latex/mathpartir.sty)
and place it in the `latex` subfolder of the repository.

## Download

The best way to download the library is
to [clone it from GitHub](https://github.com/TheoWinterhalter/formal-type-theory). If you
do not use git (you should) then you can
just
[download the ZIP file](https://github.com/TheoWinterhalter/formal-type-theory/archive/master.zip) of
the latest version. Even better, you can fork the repository so that you can easily send
us your improvements (see the section on contributions below).

## Compiling

To compile the library and the LaTeX version of the rules run
```bash
make
```
from the command line. The library is in the `src` subfolder and the PDF with the rules is `latex/rules.pdf`.

Specific targets for `make` are:

* `clean` -- clean files
* `latex/rules.pdf` -- the rules in PDF, the file can be found in `latex/rules.pdf`
* `latex/rulesParanoid.pdf` -- the rules in PDF, but *with preconditions*
* `library` -- compile the library only

For example, `make latex/rules.pdf` generates the file `latex/rules.pdf`.

## Structure of the library

### The files

The `src` folder contains the Coq files. The more important ones are:

* `config.v` -- configuration options, abstract presyntax
* `config_tactics.v` -- tactics for dealing with configuration options
* `daring_syntax.v` -- definition of presyntax with implicit substitutions, Russel universes, less annotations than the abstract syntax
* `ett.v` -- economic type theory
* `ett2ptt.v` -- proof that we can pass from economic to paranoid type theory
* `ett_sanity.v` -- proof that economic type theory is sane
* `negfunext.v` -- proof that function extensionality is not provable in MLTT
* `paranoid_syntax.v` -- definition of paranoid presytnax
* `ps_uniqueness.v` -- proof of uniqueness of typing for paranoid syntax
* `ptt.v` -- paranoid type theory
* `ptt2ett.v` -- proof that we can pass from paranoid to economic type theory
* `ptt_admissible.v` -- various admissibility lemmas for paranoid type theory
* `ptt_inversion.v` -- inversion principles for paranoid type theory
* `ptt_sanity.v` -- proof that paranoid type theory is sane
* `tactics.v` -- tactics for working with the library
* `tt.v` -- all the rules of type theory

### Old `README`

(Below is still the old version of the README.)

We formalise various meta-theoretic properties in a modular fashion. We provide a unique notion of type theory that can be parametrised over the rules and constructors it has.
For instance, we differentiate between economic and paranoid variants of type theory regarding the amount of premises a rule should have and show a theorem stating that they prove the exact same judgments.

One can see the difference between the two in the introduction rule for the identity type:
```
    Γ ⊢ u : A                      Γ ctx     Γ ⊢ A type     Γ ⊢ u : A
------------------(economic)  or   ------------------------------------(paranoid).
Γ ⊢ refl u : u = u                         Γ ⊢ refl u : u = u
```
We also provide proofs of sanity (`Γ ⊢ u : A` implies `Γ ctx` and `Γ ⊢ A` for instance) and of uniqueness of typing that are agnostic
on the parameters of the type theory (whether it's economic or paranoid, has simple products or not, universes or not…).
This also comes with tactics to type check terms automatically (although time-consuming for the time being).


### Git branches

The user should focus on `master`, the rest is here for legacy.

* `master` contains the current status of the translation (sanity is being handled, as well as uniqueness of typing),
* `zero-shift` contains another formulation of type theory where substitutions have context annotations,
* `simpler-substitutions` removes all annotations from substitutions but this results in the loss of uniqueness of typing,
* `faster-magic` is its counter-part and maybe should be kept instead of `simpler-substitutions`,
* `untyped-refl` corrresponds to an experiment regarding the removal of typing annotation to `refl`,
* `inversion` corresponds to inversion lemmata (probably subsumed by more recent work),
* `into-coq` and `into-coq-attempt` were branches where we were trying to eliminate reflection by translation from our formalised type theory to Coq directly,
* `bool-disjoint` is about showing that true = false -> Empty (but inside the theory),
* `bool-large-elim` is about adding large elimination for Bool.

## Contributors

* [Théo Winterhalter]()
* [Andrej Bauer](http://www.andrej.com/)
* [Philipp Haselwarter](http://www.haselwarter.org/~philipp/)

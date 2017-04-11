# Sanity of type theory for elimination of equality reflection

The ultimate goal is to be able to eliminate equality reflection, hopefully using weaker axioms than previous works (like UIP for instance), in the hope of being compatible with HoTT.
This results in a formalisation setting for meta-theory of translations.

## Structure of the repository

* `formalization` contains a coq formalization of various types theories and the ongoing translation,
* `paper` contains a LaTeX version of the rules (of ETT) (This is old and might need to be removed).

Refer to the `README` inside the folder to get more information about its strucutre.

## Getting the rules in LaTeX / PDF

By typing 
```bash
make rules.pdf
```
in the root directory, you run a python script that extracts ETT and PTT from their respective coq files and then compiles them into a PDF file.

## Branches

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

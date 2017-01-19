# Sanity of type theory for elimination of equality reflection

The ultimate goal is to be able to eliminate equality reflection, hopefully using weaker axioms than previous works (like UIP for instance), in the hope of being compatible with HoTT.

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

## Branches of interest

* `master` contains the current status of the sanity formalization,
* `translation` is the branch where the translation is being made, it also contains a definition of ITT.

# Meta-theoretic results for formalisation of translations

We formalise various meta-theoretic properties in a modular fashion. We provide a unique notion of type theory that can be parametrised 
over the rules and constructors it has.
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

## Structure of the repository

`src` contains the formalisaton as advertised above.  
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

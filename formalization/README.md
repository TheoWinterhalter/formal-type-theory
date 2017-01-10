# Formalization of type theories and translation

## Sanity

The purpose here is to state and prove theorems about the sanity of different type theories.
* `syntax.v`: Syntax of our type theories with type annotations,
* `ett.v`: Typing rules of ETT (Extensional Type Theory) using syntax from `syntax.v`,
* `ptt.v`: Typing rules of PTT (Paranoid Type Theory) using the same syntax, it has more premises to make sure everything is sane,
* `ett2ptt.v`: Translation from ETT to PTT, this is a sanity result as it means that we can elaborate the missing premises,
* `ptt2ett.v`: Translation from PTT to ETT,
* `preadmissibility.v`: Some admissibility rules for ETT, used for the sanity theorem,
* `sanity.v`: Sanity theorem for ETT,
* `uniqueness.v`: Proof of uniqueness of typing for ETT.

## Translation

The main translation goes from PTT to CTT, the complete scheme being:
ETT → **PTT → CTT** → ITT
* `ctt.v`: Syntax and typing rules of CTT (Coercive Type Theory) that goes with explicit coercions,
* `itt.v`: ITT (Intentional Type Theory), its syntax and typing rules, doesn't have equality reflection or type annotations on application when compared with ETT,
* `eval.v`: Evaluate coercions of CTT to get ITT expressions,
* `translation.v`: Proof of translation between PTT and CTT (CTT is only typed through it's evaluation into ITT).

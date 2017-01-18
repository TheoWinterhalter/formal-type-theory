(* Reordering of arguments in constructors.
   This is supposed to be a temporary measure until
   we reorder the arguments in the constructrs. *)

Require Import syntax.
Require Import ptt.

Lemma mySubstSym :
  forall {G D sbs sbt},
    eqsubst sbs sbt G D ->
    issubst sbs G D ->
    issubst sbt G D ->
    isctx G ->
    isctx D ->
    eqsubst sbt sbs G D.
Proof.
  intros. apply SubstSym ; assumption.
Defined.

Lemma myEqTySym :
  forall {G A B},
    eqtype G A B ->
    istype G A ->
    istype G B ->
    isctx G ->
    eqtype G B A.
Proof.
  intros. apply (EqTySym H2 H0 H1 H).
Defined.

Lemma myEqSym :
  forall {G A u v},
    eqterm G v u A ->
    isterm G u A ->
    isterm G v A ->
    istype G A ->
    isctx G ->
    eqterm G u v A.
Proof.
  intros. apply EqSym ; assumption.
Defined.

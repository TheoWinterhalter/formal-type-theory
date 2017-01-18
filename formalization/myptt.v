(* Reordering of arguments in constructors.
   This is supposed to be a temporary measure until
   we reorder the arguments in the constructrs. *)

Require Import syntax.
Require Import ptt.

Lemma myCongTermSubst :
  forall {G D A u1 u2 sbs sbt},
    eqsubst sbs sbt G D ->
    eqterm D u1 u2 A ->
    isctx G ->
    isctx D ->
    istype D A ->
    isterm D u1 A ->
    isterm D u2 A ->
    issubst sbs G D ->
    issubst sbt G D ->
    eqterm G
           (subst u1 sbs)
           (subst u2 sbt)
           (Subst A sbs).
Proof.
  intros. eapply CongTermSubst.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Defined.

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

Lemma myEqSubstFalse :
  forall {G D sbs},
    issubst sbs G D ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst false sbs)
           false
           Bool.
Proof.
  intros. eapply EqSubstFalse.
  - assumption.
  - exact H1.
  - assumption.
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

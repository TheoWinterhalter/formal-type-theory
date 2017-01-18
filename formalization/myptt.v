(* Reordering of arguments in constructors.
   This is supposed to be a temporary measure until
   we reorder the arguments in the constructrs. *)

Require Import syntax.
Require Import ptt.

Lemma myEqSubstComp :
  forall {G D E A u sbs sbt},
    isterm E u A ->
    issubst sbs G D ->
    issubst sbt D E ->
    isctx G ->
    isctx D ->
    isctx E ->
    istype E A ->
    eqterm G
           (subst (subst u sbt) sbs)
           (subst u (sbcomp sbt sbs))
           (Subst A (sbcomp sbt sbs)).
Proof.
  intros. eapply EqSubstComp.
  - assumption.
  - exact H3.
  - exact H4.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myEqSubstRefl :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    isctx G ->
    isctx D ->
    istype D A ->
    eqterm G
           (subst (refl A u) sbs)
           (refl (Subst A sbs) (subst u sbs))
           (Id (Subst A sbs) (subst u sbs) (subst u sbs)).
Proof.
  intros. eapply EqSubstRefl.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
  - assumption.
Defined.

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

Lemma myEqSubstTrue :
  forall {G D sbs},
    issubst sbs G D ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst true sbs)
           true
           Bool.
Proof.
  intros. eapply EqSubstTrue.
  - assumption.
  - exact H1.
  - assumption.
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

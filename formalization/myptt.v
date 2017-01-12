(* Reordering of arguments in constructors.
   This is supposed to be a temporary measure until
   we reorder the arguments in the constructrs. *)

Require Import syntax.
Require Import ptt.

(* TySubst and TermSubst ask questions in the wrong order when eapplied. *)
Lemma myTySubst :
  forall {G D A sbs},
    issubst sbs G D ->
    istype D A ->
    isctx G ->
    isctx D ->
    istype G (Subst A sbs).
Proof.
  intros ; eapply TySubst ; eassumption.
Defined.

Lemma myTermSubst :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    isctx G ->
    istype D A ->
    isctx D ->
    isterm G (subst u sbs) (Subst A sbs).
Proof.
  intros ; eapply TermSubst ; eassumption.
Defined.

(* Same for some other substitution tasks. *)
Lemma mySubstShift :
  forall {G D A sbs},
    issubst sbs G D ->
    istype D A ->
    isctx G ->
    isctx D ->
    issubst (sbshift G A sbs)
            (ctxextend G (Subst A sbs))
            (ctxextend D A).
Proof.
  intros ; eapply SubstShift ; eassumption.
Defined.

Lemma mySubstComp :
  forall {G D E sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    isctx G ->
    isctx D ->
    isctx E ->
    issubst (sbcomp sbt sbs) G E.
Proof.
  intros ; eapply SubstComp.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myEqTyTrans :
  forall {G A B C},
    eqtype G A B ->
    eqtype G B C ->
    isctx G ->
    istype G A ->
    istype G B ->
    istype G C ->
    eqtype G A C.
Proof.
  intros ; eapply EqTyTrans.
  - assumption.
  - assumption.
  - exact H3.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myEqTySubstComp :
  forall {G D E A sbs sbt},
    istype E A ->
    issubst sbs G D ->
    issubst sbt D E ->
    isctx G ->
    isctx D ->
    isctx E ->
    eqtype G
           (Subst (Subst A sbt) sbs)
           (Subst A (sbcomp sbt sbs)).
Proof.
  intros ; eapply EqTySubstComp.
  - assumption.
  - exact H3.
  - exact H4.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myEqTrans :
  forall {G A u v w},
    eqterm G u v A ->
    eqterm G v w A ->
    isctx G ->
    istype G A ->
    isterm G u A ->
    isterm G v A ->
    isterm G w A ->
    eqterm G u w A.
Proof.
  intros. eapply EqTrans.
  - assumption.
  - assumption.
  - assumption.
  - exact H4.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myEqTyConv :
  forall {G A B u v},
    eqterm G u v A ->
    eqtype G A B ->
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u A ->
    isterm G v A ->
    eqterm G u v B.
Proof.
  intros. eapply EqTyConv.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Defined.

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

Lemma myTermTyConv :
  forall {G A B u},
    isterm G u A ->
    eqtype G A B ->
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B.
Proof.
  intros. eapply TermTyConv.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
  - assumption.
Defined.

Lemma myCongTySubst :
  forall {G D A B sbs sbt},
    eqsubst sbs sbt G D ->
    eqtype D A B ->
    isctx G ->
    isctx D ->
    istype D A ->
    istype D B ->
    issubst sbs G D ->
    issubst sbt G D ->
    eqtype G (Subst A sbs) (Subst B sbt).
Proof.
  intros. eapply CongTySubst.
  - assumption.
  - exact H2.
  - assumption.
  - assumption.
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

Lemma myEqTySubstId :
  forall {G D A u v sbs},
    issubst sbs G D ->
    istype D A ->
    isterm D u A ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqtype G
           (Subst (Id A u v) sbs)
           (Id (Subst A sbs) (subst u sbs) (subst v sbs)).
Proof.
  intros. eapply EqTySubstId.
  - assumption.
  - exact H4.
  - assumption.
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

Lemma myCongSubstZero :
  forall {G1 G2 A1 A2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqterm G1 u1 u2 A1 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 A2 ->
    isterm G1 u1 A1 ->
    isterm G1 u2 A1 ->
    eqsubst (sbzero G1 A1 u1)
            (sbzero G2 A2 u2)
            G1
            (ctxextend G1 A1).
Proof.
Admitted.

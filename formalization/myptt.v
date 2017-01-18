(* Reordering of arguments in constructors.
   This is supposed to be a temporary measure until
   we reorder the arguments in the constructrs. *)

Require Import syntax.
Require Import ptt.

(* TySubst and TermSubst ask questions in the wrong order when eapplied. *)

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
  intros.
  apply CongSubstZero ; assumption.
Defined.

Lemma myCongSubstShift :
  forall {G1 G2 D A1 A2 sbs1 sbs2},
    eqctx G1 G2 ->
    eqsubst sbs1 sbs2 G1 D ->
    eqtype D A1 A2 ->
    isctx G1 ->
    isctx G2 ->
    isctx D ->
    istype D A1 ->
    istype D A2 ->
    issubst sbs1 G1 D ->
    issubst sbs2 G1 D ->
    eqsubst (sbshift G1 A1 sbs1)
            (sbshift G2 A2 sbs2)
            (ctxextend G1 (Subst A1 sbs1))
            (ctxextend D A1).
Proof.
  intros.
  apply CongSubstShift ; assumption.
Defined.

Lemma myCongSubstWeak :
  forall {G1 G2 A1 A2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 A2 ->
    eqsubst (sbweak G1 A1)
            (sbweak G2 A2)
            (ctxextend G1 A1)
            G1.
Proof.
  intros.
  apply CongSubstWeak ; assumption.
Defined.

Lemma myEqSubstCtxConv :
  forall {G1 G2 D1 D2 sbs sbt},
    eqsubst sbs sbt G1 D1 ->
    eqctx G1 G2 ->
    eqctx D1 D2 ->
    isctx G1 ->
    isctx G2 ->
    isctx D1 ->
    isctx D2 ->
    issubst sbs G1 D1 ->
    issubst sbt G1 D1 ->
    eqsubst sbs sbt G2 D2.
Proof.
  intros.
  eapply EqSubstCtxConv ; [
    exact H2
  | assumption
  | exact H4
  | assumption ..
  ].
Defined.

Lemma myCtxSym :
  forall {G D},
    eqctx G D ->
    isctx G ->
    isctx D ->
    eqctx D G.
Proof.
  intros. apply CtxSym ; assumption.
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

Lemma myTermCtxConv :
  forall {G D A u},
    isterm G u A ->
    eqctx G D ->
    isctx G ->
    isctx D ->
    istype G A ->
    isterm D u A.
Proof.
  intros.
  eapply TermCtxConv ; [
    exact H1
  | assumption ..
  ].
Defined.

Lemma myEqTySubstProd :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isctx G ->
    isctx D ->
    eqtype G
           (Subst (Prod A B) sbs)
           (Prod (Subst A sbs) (Subst B (sbshift G A sbs))).
Proof.
  intros.
  eapply EqTySubstProd ; [
    assumption
  | exact H3
  | assumption ..
  ].
Defined.

Lemma myEqTySubstEmpty :
  forall {G D sbs},
    issubst sbs G D ->
    isctx G ->
    isctx D ->
    eqtype G
           (Subst Empty sbs)
           Empty.
Proof.
  intros. eapply EqTySubstEmpty.
  - assumption.
  - exact H1.
  - assumption.
Defined.

Lemma myEqTySubstUnit :
  forall {G D sbs},
    issubst sbs G D ->
    isctx G ->
    isctx D ->
    eqtype G
           (Subst Unit sbs)
           Unit.
Proof.
  intros. eapply EqTySubstUnit.
  - assumption.
  - exact H1.
  - assumption.
Defined.

Lemma myEqTySubstBool :
  forall {G D sbs},
    issubst sbs G D ->
    isctx G ->
    isctx D ->
    eqtype G
           (Subst Bool sbs)
           Bool.
Proof.
  intros. eapply EqTySubstBool.
  - assumption.
  - exact H1.
  - assumption.
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

Lemma myEqTyCtxConv :
  rule
    parameters: {G D A B},
    premise: eqtype G A B
    premise: eqctx G D
    premise: istype G A
    premise: istype G B
    premise: isctx G
    premise: isctx D
    conclusion:
      eqtype D A B
  endrule.
Proof.
  intros. eapply EqTyCtxConv ; [ exact H3 | assumption .. ].
Defined.

Lemma mySubstTrans :
  rule
    parameters: {G D sb1 sb2 sb3},
    premise: eqsubst sb1 sb2 G D
    premise: eqsubst sb2 sb3 G D
    premise: issubst sb1 G D
    premise: issubst sb2 G D
    premise: issubst sb3 G D
    premise: isctx G
    premise: isctx D
    conclusion:
      eqsubst sb1 sb3 G D
  endrule.
Proof.
  intros.
  eapply SubstTrans ;
    [ assumption .. | exact H2 | assumption | assumption | assumption ].
Defined.

Lemma myCongSubstComp :
  rule
    parameters: {G D E sbs1 sbs2 sbt1 sbt2},
    premise: eqsubst sbs1 sbs2 G D
    premise: eqsubst sbt1 sbt2 D E
    premise: issubst sbs1 G D
    premise: issubst sbs2 G D
    premise: issubst sbt1 D E
    premise: issubst sbt2 D E
    premise: isctx G
    premise: isctx D
    premise: isctx E
    conclusion:
      eqsubst (sbcomp sbt1 sbs1)
              (sbcomp sbt2 sbs2)
              G
              E
  endrule.
Proof.
  intros.
  eapply @CongSubstComp with (D := D) ; assumption.
Defined.

Lemma myCompAssoc :
  rule
    parameters: {G D E F sbs sbt sbr},
    premise: issubst sbs G D
    premise: issubst sbt D E
    premise: issubst sbr E F
    premise: isctx G
    premise: isctx D
    premise: isctx E
    premise: isctx F
    conclusion:
      eqsubst (sbcomp sbr (sbcomp sbt sbs))
              (sbcomp (sbcomp sbr sbt) sbs)
              G
              F
  endrule.
Proof.
  intros.
  eapply @CompAssoc with (D := D) (E := E) (F := F) ; assumption.
Defined.

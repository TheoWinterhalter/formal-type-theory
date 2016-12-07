(* Admissibility rules and tactics (before sanity). *)

Require Import ett.

(* Some tactic to compose substitutions. *)
Lemma eqtype_subst_left :
  forall {G D E A B sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    istype E A ->
    eqtype G (Subst A (sbcomp sbs sbt)) B ->
    eqtype G (Subst (Subst A sbt) sbs) B.
Proof.
  intros.
  eapply EqTyTrans.
  - eapply EqTySubstComp.
    + eassumption.
    + eassumption.
    + assumption.
  - assumption.
Defined.

Lemma eqterm_subst_left :
  forall {G D E A u v sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    istype E A ->
    isterm E u A ->
    eqterm G (subst u (sbcomp sbs sbt)) v (Subst A (sbcomp sbs sbt)) ->
    eqterm G (subst (subst u sbt) sbs) v (Subst (Subst A sbt) sbs).
Proof.
  intros.
  eapply EqTrans.
  - eapply EqTyConv.
    + eapply EqSubstComp.
      * eassumption.
      * eassumption.
      * assumption.
    + apply EqTySym.
      eapply EqTySubstComp.
      * eassumption.
      * eassumption.
      * assumption.
  - eapply EqTyConv.
    + eassumption.
    + apply EqTySym.
      eapply EqTySubstComp.
      * eassumption.
      * eassumption.
      * assumption.
Defined.

Ltac compsubst1 :=
  match goal with
  | |- eqtype ?G (Subst (Subst ?A ?sbt) ?sbs) ?B =>
    eapply eqtype_subst_left ; try eassumption
  | |- eqtype ?G ?A (Subst (Subst ?B ?sbt) ?sbs) =>
    eapply EqTySym ; eapply eqtype_subst_left ; try eassumption
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply eqterm_subst_left ; try eassumption
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply EqSym ; eapply eqterm_subst_left ; try eassumption
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v ?A =>
    eapply EqTyConv ;
    [try eapply eqterm_subst_left ; try eassumption | try eassumption]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; eapply EqTyConv ;
    [try eapply eqterm_subst_left ; try eassumption | try eassumption]
  | _ => fail
  end.


(* Some tactic to push substitutions inside one step. *)
(* Partial for now. *)
Ltac pushsubst1 :=
  match goal with
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply EqTyTrans ; [
      eapply EqTySubstId ; try eassumption
    | try eassumption
    ]
  | _ => fail
  end.
(* Some admissibility lemmata. *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B (sbweak D A)) (sbshift G A sbs))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
Proof.
  intros G D A B sbs H H0 H1.
  eapply EqTyTrans.
  - eapply EqTySubstComp.
    + eassumption.
    + eapply SubstShift.
      * eassumption.
      * assumption.
    + eapply SubstWeak. assumption.
  - { eapply EqTyTrans.
      - eapply CongTySubst.
        + eapply WeakNat ; assumption.
        + now apply EqTyRefl.
      - apply EqTySym.
        eapply EqTySubstComp.
        + eassumption.
        + eapply SubstWeak. eapply TySubst.
          * eassumption.
          * assumption.
        + assumption.
    }
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G (Subst (Subst A (sbweak G B)) (sbzero G B u)) A.
Proof.
  intros G A B u H H0 H1.
  eapply EqTyTrans.
  - eapply EqTySubstComp.
    + eassumption.
    + eapply SubstZero. assumption.
    + eapply SubstWeak. assumption.
  - { eapply EqTyTrans.
      - eapply CongTySubst.
        + eapply WeakZero. assumption.
        + now eapply EqTyRefl.
      - now apply EqTyIdSubst.
    }
Defined.

Lemma EqTyShiftZero :
  forall {G D A B v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm D v A ->
    eqtype
      G
      (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros.
  compsubst1.
  - eapply SubstZero.
    eapply TermSubst ; eassumption.
  - eapply SubstShift ; assumption.
  - compsubst1.
    + eapply SubstZero. assumption.
    + eapply CongTySubst.
      * eapply SubstSym.
        eapply ShiftZero ; assumption.
      * apply EqTyRefl ; assumption.
Defined.

Lemma EqTyCongZero :
  forall {G A1 A2 B1 B2 u1 u2},
    isctx G ->
    eqtype G A1 B1 ->
    eqterm G u1 u2 A1 ->
    eqtype (ctxextend G A1) A2 B2 ->
    eqtype G
           (Subst A2 (sbzero G A1 u1))
           (Subst B2 (sbzero G B1 u2)).
Proof.
  intros.
  eapply CongTySubst.
  - eapply CongSubstZero.
    + apply CtxRefl. assumption.
    + assumption.
    + assumption.
  - assumption.
Defined.

Lemma EqTyCongShift :
  forall {G1 G2 D A1 A2 B1 B2 sbs1 sbs2},
    eqctx G1 G2 ->
    eqsubst sbs1 sbs2 G1 D ->
    eqtype D A1 A2 ->
    eqtype (ctxextend D A1) B1 B2 ->
    eqtype (ctxextend G1 (Subst A1 sbs1))
           (Subst B1 (sbshift G1 A1 sbs1))
           (Subst B2 (sbshift G2 A2 sbs2)).
Proof.
  intros.
  eapply CongTySubst.
  - eapply CongSubstShift ; eassumption.
  - assumption.
Defined.

Lemma EqTyCongWeak :
  forall {G1 G2 A1 A2 B1 B2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    eqtype (ctxextend G1 A1)
           (Subst B1 (sbweak G1 A1))
           (Subst B2 (sbweak G2 A2)).
Proof.
  intros.
  eapply CongTySubst.
  - eapply CongSubstWeak ; assumption.
  - assumption.
Defined.

Lemma EqSubstWeakNat :
  forall {G D A B u sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B -> (* It seems like we need to put it in. *)
    isterm D u B ->
    eqterm (ctxextend G (Subst A sbs))
           (subst (subst u (sbweak D A)) (sbshift G A sbs))
           (subst (subst u sbs) (sbweak G (Subst A sbs)))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
Proof.
  intros G D A B u sbs H H0 H1 H2.
  eapply EqTyConv.
  - { eapply EqTrans.
      - eapply EqSubstComp.
        + eassumption.
        + eapply SubstShift.
          * eassumption.
          * assumption.
        + eapply SubstWeak. assumption.
      - { eapply EqTrans.
          - eapply CongTermSubst.
            + eapply WeakNat ; assumption.
            + now apply EqRefl.
          - apply EqSym.
            { eapply EqTyConv.
              - eapply EqSubstComp.
                + eassumption.
                + eapply SubstWeak. eapply TySubst.
                  * eassumption.
                  * assumption.
                + assumption.
              - eapply CongTySubst.
                + eapply SubstSym. eapply WeakNat.
                  * assumption.
                  * assumption.
                + now apply EqTyRefl.
            }
        }
    }
  - { eapply EqTyTrans.
      - eapply EqTySym.
        eapply EqTySubstComp.
        + eassumption.
        + eapply SubstShift.
          * eassumption.
          * eassumption.
        + eapply SubstWeak.
          eassumption.
      - apply EqTyWeakNat.
        + assumption.
        + assumption.
        + assumption.
    }
Defined.

Lemma EqSubstWeakZero :
  forall {G A B u v},
    istype G A ->
    istype G B ->
    isterm G u A ->
    isterm G v B ->
    eqterm G
           (subst (subst u (sbweak G B)) (sbzero G B v))
           u
           A.
Proof.
  intros G A B u v H H0 H1 H2.
  eapply EqTrans.
  - { eapply EqTyConv.
      - eapply EqSubstComp.
        + eassumption.
        + eapply SubstZero. assumption.
        + eapply SubstWeak. assumption.
      - { eapply EqTyTrans.
          - eapply CongTySubst.
            + eapply WeakZero. assumption.
            + now eapply EqTyRefl.
          - now apply EqTyIdSubst.
        }
    }
  - { eapply EqTrans.
      - eapply EqTyConv.
        + eapply CongTermSubst.
          * now eapply WeakZero.
          * eapply EqRefl. eassumption.
        + { eapply EqTyTrans.
            - eapply CongTySubst.
              + eapply WeakZero. assumption.
              + now eapply EqTyRefl.
            - now apply EqTyIdSubst.
          }
      - now apply EqIdSubst.
    }
Defined.

Lemma EqTermShiftZero :
  forall {G D A B u v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm (ctxextend D A) u B ->
    isterm D v A ->
    eqterm
      G
      (subst (subst u (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (subst (subst u (sbzero D A v)) sbs)
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros.
  compsubst1.
  - eapply SubstZero. assumption.
  - compsubst1.
    + eapply SubstZero.
      eapply TermSubst ; eassumption.
    + eapply SubstShift ; assumption.
    + { eapply CongTermSubst.
        - eapply ShiftZero ; assumption.
        - apply EqRefl. assumption.
      }
    + compsubst1.
      * eapply SubstZero.
        eapply TermSubst ; eassumption.
      * eapply SubstShift ; assumption.
      * { eapply CongTySubst.
          - eapply ShiftZero ; assumption.
          - apply EqTyRefl. assumption.
        }
Defined.

Lemma EqTermCongWeak :
  forall {G1 G2 A1 A2 B1 B2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    eqterm G1 u1 u2 B1 ->
    eqterm (ctxextend G1 A1)
           (subst u1 (sbweak G1 A1))
           (subst u2 (sbweak G2 A2))
           (Subst B1 (sbweak G1 A1)).
Proof.
  intros.
  eapply CongTermSubst.
  - eapply CongSubstWeak ; assumption.
  - assumption.
Defined.

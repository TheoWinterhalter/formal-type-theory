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
  | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        eapply SubstRefl ; try eassumption
      | pushsubst1
      ]
    | try eassumption
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply EqTyTrans ; [
      eapply EqTySubstId ; try eassumption
    | try eassumption
    ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; eapply EqTyTrans ; [
      eapply EqTySubstId ; try eassumption
    | try eassumption
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTrans ; [
      eapply EqSubstRefl ; try eassumption
    | try eassumption
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTyConv ; [
      eapply EqTrans ; [
        eapply EqSubstRefl ; try eassumption
      | try eassumption
      ]
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

(* For admitting purposes *)
Lemma todo : False.
Admitted.

(* A tactic to type substitutions. *)
Ltac substproof :=
  match goal with
  | |- issubst (sbzero ?G ?A ?u) ?G1 ?G2 =>
    eapply SubstZero ; substproof
  | |- issubst (sbweak ?G ?A) ?G1 ?G2 =>
    eapply SubstWeak ; substproof
  | |- issubst (sbshift ?G ?A ?sbs) ?G1 ?G2 =>
    eapply SubstShift ; substproof
  (* | |- issubst (sbshift ?G ?A ?sbs) ?G1 ?G2 => *)
  (*   eapply SubstCtxConv ; [ *)
  (*     substproof *)
  (*   | try eassumption *)
  (*   | try eassumption *)
  (*   ] *)
  | |- issubst (sbid ?G) ?G1 ?G2 =>
    eapply SubstId ; eassumption
  | |- issubst (sbcomp ?sbs ?sbt) ?G1 ?G2 =>
    eapply SubstComp ; substproof
  (* We also deal with cases where we have substitutions on types or terms *)
  | |- istype ?G (Subst ?A ?sbs) =>
    eapply TySubst ; substproof
  | |- isterm ?G (subst ?u ?sbs) (Subst ?A ?sbs) =>
    eapply TermSubst ; substproof
  | |- isterm (ctxextend ?G ?A) (var 0) (Subst ?A (sbweak ?G ?A)) =>
    apply TermVarZero ; eassumption
  | _ => eassumption
  end.

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try substproof.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try substproof.


(* The big lemma that we need for EqSusbtJ *)
Lemma JTyConv :
  forall {G D A C u v w p sbs},
    isctx G ->
    isctx D ->
    issubst sbs G D ->
    istype D A ->
    isterm D u A ->
    isterm D v A ->
    isterm D p (Id A u v) ->
    istype
      (ctxextend
         (ctxextend D A)
         (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
      )
      C ->
    isterm
      D
      w
      (Subst
         (Subst
            C
            (sbshift
               D
               (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
               (sbzero D A u))) (sbzero D (Id A u u) (refl A u))) ->
    isterm D v A ->
    isterm D p (Id A u v) ->
    eqtype
      G
      (Subst
         (Subst
            (Subst C
                   (sbshift
                      D
                      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                      (sbzero D A v)
                   )
            )
            (sbzero D (Id A u v) p)
         )
         sbs
      )
      (Subst
         (Subst
            (Subst C
                   (sbshift
                      (ctxextend G (Subst A sbs))
                      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                      (sbshift G A sbs)
                   )
            )
            (sbshift
               G
               (Id
                  (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
                  (subst (subst u sbs) (sbweak G (Subst A sbs)))
                  (var 0)
               )
               (sbzero G (Subst A sbs) (subst v sbs))
            )
         )
         (sbzero
            G
            (Id (Subst A sbs) (subst u sbs) (subst v sbs))
            (subst p sbs)
         )
      ).
Proof.
  intros.
  (* First let's have some assertions that we won't keep proving. *)
  assert (isterm D (refl A u) (Id A u u)).
  { now apply TermRefl. }
  assert (
    istype (ctxextend D A)
           (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
  ).
  { apply TyId ; substproof. }
  assert (eqctx D D).
  { now apply CtxRefl. }
  assert (eqtype D (Subst (Subst A (sbweak D A)) (sbzero D A v)) A).
  { now apply EqTyWeakZero. }
  assert (isterm D u (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply TermTyConv.
    - eassumption.
    - apply EqTySym. assumption.
  }
  assert (
    eqterm D
           (subst (subst u (sbweak D A)) (sbzero D A v)) u
           (Subst (Subst A (sbweak D A)) (sbzero D A v))
  ).
  { apply EqSubstWeakZero ; try assumption. substproof. }
  assert (eqterm D (subst (var 0) (sbzero D A v)) v
    (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply EqTyConv.
    - now eapply EqSubstZeroZero.
    - apply EqTySym. assumption.
  }
  assert (
    eqtype
      D
      (Id
         (Subst (Subst A (sbweak D A)) (sbzero D A v))
         (subst (subst u (sbweak D A)) (sbzero D A v))
         (subst (var 0) (sbzero D A v)))
      (Id A u v)
  ).
  { apply CongId ; assumption. }
  assert (
    eqtype D
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbzero D A v)) (Id A u v)
  ).
  { gopushsubst. }
  assert (
    eqctx
      (ctxextend
         D
         (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                (sbzero D A v)))
      (ctxextend D (Id A u v))
  ).
  { now apply EqCtxExtend. }
  assert (isctx (ctxextend D A)).
  { now apply CtxExtend. }
  assert (isctx
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))).
  { now apply CtxExtend. }
  assert (isterm G (refl (Subst A sbs) (subst u sbs))
    (Id (Subst A sbs) (subst u sbs) (subst u sbs))).
  { apply TermRefl. substproof. }
  assert (
    isterm (ctxextend G (Subst A sbs)) (var 0)
    (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
  ).
  { apply TermVarZero. substproof. }
  assert (istype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (subst (subst u sbs) (sbweak G (Subst A sbs))) (var 0))
  ).
  { apply TyId ; substproof. }
  assert (eqctx G G).
  { apply CtxRefl. assumption. }
  assert (
    eqsubst
      (sbcomp
         (sbcomp
            (sbzero G (Subst A sbs) (subst v sbs))
            (sbweak G (Subst A sbs))
         )
         sbs
      )
      sbs
      G D
  ).
  { eapply SubstTrans.
    - eapply CongSubstComp.
      + eapply WeakZero. substproof.
      + eapply SubstRefl. assumption.
    - eapply SubstTrans.
      + eapply CompIdLeft. assumption.
      + eapply SubstRefl. assumption.
  }
  assert (eqtype D A A).
  { apply EqTyRefl. assumption. }
  assert (eqtype G
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)).
  { gocompsubst. gocompsubst. eapply CongTySubst ; eassumption. }
  assert (eqterm D u u A).
  { apply EqRefl. assumption. }
  assert (
    eqterm G
    (subst (subst (subst u sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs))) (subst u sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst. eapply CongTermSubst ; eassumption. }
  assert (
    eqterm G (subst (var 0) (sbzero G (Subst A sbs) (subst v sbs)))
    (subst v sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply EqTyConv.
    - eapply EqSubstZeroZero. substproof.
    - apply EqTySym. assumption.
  }
  assert (
    eqtype G
    (Subst
       (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
          (subst (subst u sbs) (sbweak G (Subst A sbs)))
          (var 0)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { gopushsubst. apply CongId ; assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
             (subst (subst u sbs) (sbweak G (Subst A sbs)))
             (var 0)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
  ).
  { now apply EqCtxExtend. }
  assert (isctx (ctxextend G (Subst A sbs))).
  { apply CtxExtend.
    - assumption.
    - substproof.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
    (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
  ).
  { apply EqTyWeakNat ; assumption. }
  assert (
    eqterm (ctxextend G (Subst A sbs))
    (subst (subst u (sbweak D A)) (sbshift G A sbs))
    (subst (subst u sbs) (sbweak G (Subst A sbs)))
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { eapply EqTyConv.
    - eapply EqSubstWeakNat ; eassumption.
    - apply EqTySym. assumption.
  }
  assert (eqterm (ctxextend G (Subst A sbs)) (subst (var 0) (sbshift G A sbs))
    (var 0) (Subst (Subst A (sbweak D A)) (sbshift G A sbs))).
  { eapply EqTyConv.
    - eapply EqSubstShiftZero ; eassumption.
    - apply EqTySym. assumption.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (subst (subst u sbs) (sbweak G (Subst A sbs))) (var 0))
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbshift G A sbs))
  ).
  { gopushsubst. now apply CongId. }
  assert (
    eqctx
    (ctxextend (ctxextend G (Subst A sbs))
       (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
          (subst (subst u sbs) (sbweak G (Subst A sbs)))
          (var 0)))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)))
  ).
  { apply EqCtxExtend.
    - apply CtxRefl. assumption.
    - assumption.
  }
  assert (
    issubst
      (sbshift D
               (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
               (sbzero D A v))
      (ctxextend D (Id A u v))
      (ctxextend
         (ctxextend D A)
         (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv.
    - substproof.
    - assumption.
    - apply CtxRefl. assumption.
  }
  assert (istype D (Id A u v)).
  { apply TyId ; assumption. }
  assert (isctx (ctxextend G (Subst (Id A u v) sbs))).
  { apply CtxExtend ; substproof. }
  assert (
    issubst (sbshift G (Id A u v) sbs) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend D
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbzero D A v)))
  ).
  { eapply SubstCtxConv.
    - substproof.
    - apply CtxRefl ; assumption.
    - apply CtxSym. assumption.
  }
  assert (
    eqsubst (sbcomp (sbcomp sbs (sbzero D A v)) (sbweak D A)) sbs G D
  ).
  { eapply SubstTrans.
    - eapply CompAssoc ; substproof.
    - eapply SubstTrans.
      + eapply CongSubstComp.
        * eapply SubstRefl. eassumption.
        * eapply WeakZero. assumption.
      + apply CompIdRight. assumption.
  }
  assert (
    eqtype G (Subst A (sbcomp (sbcomp sbs (sbzero D A v)) (sbweak D A)))
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp sbs (sbzero D A v)))
  ).
  { gocompsubst. gocompsubst. gocompsubst.
    eapply CongTySubst.
    - eapply SubstTrans.
      + eapply CompAssoc ; substproof.
      + eapply SubstTrans.
        * { eapply CongSubstComp.
            - eapply SubstRefl. substproof.
            - eapply WeakZero. assumption.
          }
        * eapply CompIdRight.
          substproof.
    - assumption.
  }
  assert (
    eqterm G (subst u sbs)
    (subst (subst u (sbweak D A)) (sbcomp sbs (sbzero D A v)))
    (Subst A sbs)
  ).
  { eapply EqTyConv.
    - eapply EqSym. eapply EqTrans.
      + eapply eqterm_subst_left.
        * substproof.
        * substproof.
        * shelve.
        * eassumption.
        * eapply EqRefl. substproof.
          Unshelve. substproof.
      + { eapply EqTyConv.
          - eapply CongTermSubst.
            + eassumption.
            + eassumption.
          - assumption.
        }
    - gocompsubst. gocompsubst. gocompsubst.
      eapply CongTySubst.
      + eapply SubstTrans.
        * eapply CompAssoc ; substproof.
        * eapply SubstTrans.
          { eapply CongSubstComp.
            - eapply SubstRefl. substproof.
            - eapply WeakZero. assumption.
          }
          eapply SubstTrans.
          { eapply CompAssoc ; substproof. }
          eapply SubstTrans.
          { eapply CongSubstComp.
            - eapply SubstRefl. substproof.
            - eapply CompIdRight. substproof.
          }
          eapply SubstTrans.
          { eapply CompAssoc ; substproof. }
          eapply SubstTrans.
          { eapply CongSubstComp.
            - eapply SubstRefl. eassumption.
            - eapply WeakZero. assumption.
          }
          eapply CompIdRight. assumption.
      + assumption.
  }
  assert (
    eqterm G
           (subst v sbs)
           (subst (var 0) (sbcomp sbs (sbzero D A v)))
           (Subst A sbs)
  ).
  { apply EqSym. eapply EqTrans.
    { eapply EqTyConv.
      - eapply EqSym. eapply EqSubstComp.
        + shelve.
        + eassumption.
        + substproof.
        Unshelve. Focus 2. apply TermVarZero. assumption.
      - gocompsubst. eapply CongTySubst.
        + eapply SubstTrans.
          { eapply CompAssoc ; substproof. }
          eapply SubstTrans.
          { eapply CongSubstComp.
            - eapply SubstRefl. eassumption.
            - eapply WeakZero. assumption.
          }
          eapply CompIdRight. assumption.
        + assumption.
    }
    eapply CongTermSubst.
    - eapply SubstRefl. eassumption.
    - eapply EqSubstZeroZero. assumption.
  }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp sbs (sbzero D A v))) (Subst (Id A u v) sbs)
  ).
  { gopushsubst. gopushsubst. apply CongId.
    - gocompsubst. eapply CongTySubst ; eassumption.
    - assumption.
    - assumption.
  }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp sbs (sbzero D A v)))) (ctxextend G (Subst (Id A u v) sbs))
  ).
  { apply EqCtxExtend.
    - assumption.
    - assumption.
  }
  assert (
    eqsubst
    (sbcomp (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs))
       (sbweak D A)) sbs G D
  ).
  { eapply SubstTrans.
    { eapply CongSubstComp.
      - eapply ShiftZero ; eassumption.
      - eapply SubstRefl. substproof.
    }
    eapply SubstTrans.
    { eapply CompAssoc ; substproof. }
    eapply SubstTrans.
    { eapply CongSubstComp.
      - eapply SubstRefl. substproof.
      - eapply WeakZero. assumption.
    }
    eapply CompIdRight. assumption.
  }
  assert (
    eqtype G
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
    (Subst A sbs)
  ).
  { gocompsubst. eapply CongTySubst ; eassumption. }
  assert (
    eqterm G
    (subst (subst u (sbweak D A))
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
    (subst u sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
  ).
  { gocompsubst. eapply CongTermSubst ; eassumption. }
  assert (
    isterm (ctxextend D A) (var 0) (Subst A (sbweak D A))
  ).
  { apply TermVarZero. assumption. }
  assert (
    eqterm G
    (subst (var 0)
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
    (subst v sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
  ).
  { eapply EqTrans.
    { eapply EqSym. eapply EqSubstComp ; substproof. }
    eapply EqTrans.
    { eapply EqTyConv.
      - eapply CongTermSubst.
        + eapply SubstRefl. substproof.
        + eapply EqSubstShiftZero ; eassumption.
      - gocompsubst. gocompsubst. gocompsubst.
        eapply CongTySubst.
        + eapply SubstTrans. eassumption.
          apply SubstSym. assumption.
        + assumption.
    }
    eapply EqTyConv.
    - eapply EqSubstZeroZero. substproof.
    - apply EqTySym. assumption.
  }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs)))
    (Subst (Id A u v) sbs)
  ).
  { gopushsubst. gopushsubst. apply EqTySym. apply CongId ; assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbzero G (Subst A sbs) (subst v sbs)) (sbshift G A sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  { now apply EqCtxExtend. }
  assert (istype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))).
  { apply TyId ; substproof. }
  assert (
    eqtype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))
    (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { apply EqTyRefl. assumption. }
  assert (
     eqtype G
            (Subst (Id A u v) sbs)
            (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { gopushsubst. }
  assert (
    isterm G (subst p sbs) (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { eapply TermTyConv.
    - eapply TermSubst.
      * eassumption.
      * eassumption.
    - assumption.
  }
  (* Now let's proceed with the proof. *)
  gocompsubst. gocompsubst. gocompsubst.
  - eapply SubstCtxConv ; substproof.
  - gocompsubst.
    + eapply SubstComp.
      * substproof.
      * eapply SubstCtxConv ; substproof.
    + eapply CongTySubst.
      * (* Now we're back to where we're supposed to be,
               where the proof is in my notebook. *)
        (* We go from the rhs. *)
        { eapply SubstSym. eapply SubstTrans.
          { (* Then we only look on the lhs of the composition. *)
            eapply CongSubstComp.
            - (* We exchange the substs. *)
              eapply SubstSym. eapply ShiftZero ; assumption.
            - (* We don't touch the rhs. *)
              eapply SubstRefl. eassumption.
          }
          (* We're using associativity to look at the rhs. *)
          eapply SubstTrans.
          { eapply CompAssoc ; substproof. }
          (* We can now have a look at the rhs of the composition. *)
          eapply SubstTrans.
          { eapply CongSubstComp.
            - (* On the left we remain unchanged. *)
              eapply SubstRefl. substproof.
            - (* On the right we have a composition of shifts, thus we
                 use fonctoriality to progress.
                 However we need to apply congruence again to rewrite
                 the type in the left shift.
               *)
              eapply CongSubstComp.
              + eapply @CongSubstShift
                with (A2 := Subst
                             (Id (Subst A (sbweak D A))
                                 (subst u (sbweak D A))
                                 (var 0))
                             (sbzero D A v)
                     ).
                * eassumption.
                * eapply SubstRefl ; eassumption.
                * apply EqTySym. assumption.
              + (* We don't change the other substitution. *)
                eapply SubstRefl. substproof.
          }
          (* Now that we rewrote the type, we can use fonctoriality. *)
          (* Note this could be meged with the next couple steps. *)
          eapply SubstTrans.
          { eapply CongSubstComp.
            - (* On the left we remain unchanged. *)
              eapply SubstRefl. substproof.
            - eapply EqSubstCtxConv.
              + eapply CompShift ; substproof.
              + assumption.
              + apply CtxRefl. assumption.
          }
          (* Now that we have a composition inside the shift, we want
             to proceed with an exchange by using ShiftZero. *)
          eapply SubstTrans.
          { eapply CongSubstComp.
            - (* We leave the left unchanged. *)
              eapply SubstRefl. substproof.
            - eapply EqSubstCtxConv.
              + eapply CongSubstShift.
                * eassumption.
                * eapply SubstSym. now eapply ShiftZero.
                * apply EqTyRefl. assumption.
              + assumption.
              + apply CtxRefl. assumption.
          }
          (* Now we need to apply CompShift again to put the composition outside
             and apply associativity. *)
          eapply SubstTrans.
          { eapply CongSubstComp.
            - (* On the left we remain unchanged. *)
              eapply SubstRefl. substproof.
            - eapply SubstSym. eapply EqSubstCtxConv.
              + eapply CompShift ; substproof.
              + assumption.
              + apply CtxRefl. assumption.
          }
          (* Now, it's time to apply associativity guys. *)
          eapply SubstTrans.
          { eapply SubstSym. eapply CompAssoc.
            - substproof.
            - eapply SubstCtxConv.
              + substproof.
              + destruct todo.
              + eapply CtxRefl. destruct todo.
            - substproof.
          }
          (* Now we should finally have the same structure for the substitutions
             and thus be able to apply congruences. *)
          eapply CongSubstComp.
          - eapply CongSubstComp.
            + eapply CongSubstZero.
              * eassumption.
              * destruct todo.
              * destruct todo.
            + { eapply EqSubstCtxConv.
                - eapply CongSubstShift.
                  + assumption.
                  + destruct todo.
                  + destruct todo.
                - apply EqCtxExtend.
                  + assumption.
                  + destruct todo.
                - apply CtxRefl. destruct todo.
              }
          - apply SubstRefl. apply SubstShift.
            + substproof.
            + assumption.
        }
      * eapply EqTyRefl. eassumption.
Defined.

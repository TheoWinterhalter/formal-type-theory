Require Import ett.

Fixpoint TyIdInversion {G A u v} (H : istype G (Id A u v)) {struct H} :
  istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H.

  - { split ; [split | idtac].
      - apply (@TyCtxConv G0 G).
        + now apply TyIdInversion with (u := u) (v := v).
        + assumption.
      - apply (@TermCtxConv G0 G).
        + now apply TyIdInversion with (u := u) (v:= v).
        + assumption.
      - apply (@TermCtxConv G0 G).
        + now apply TyIdInversion with (u := u) (v:= v).
        + assumption. }

  - { split ; [split | idtac].
      - assumption.
      - assumption.
      - assumption. }

Defined.

(* Tactic to apply one the induction hypotheses. *)
(* Unfortunately the straightforward definition below insn't accepted. *)
(* Ltac ih := *)
(*   match goal with *)
(*   | _ : issubst ?sbs ?G ?D |- _ => now apply (sane_issubst G D sbs) *)
(*   | _ : istype ?G ?A |- _ => now apply (sane_istype G A) *)
(*   | _ : isterm ?G ?u ?A |- _ => now apply (sane_isterm G A u) *)
(*   | _ : eqctx ?G ?D |- _ => now apply (sane_eqctx G D) *)
(*   | _ : eqtype ?G ?A ?B |- _ => now apply (sane_eqtype G A B) *)
(*   | _ : eqterm ?G ?u ?v ?A |- _ => now apply (sane_eqterm G u v A) *)
(*   | _ => fail *)
(*   end. *)

(* More tedious version. *)
Ltac ih :=
  match goal with
  | f : forall G D sbs, issubst sbs G D -> isctx G * isctx D ,
    _ : issubst ?sbs ?G ?D
    |- _ => now apply (f G D sbs)
  | f : forall G A, istype G A -> isctx G ,
    _ : istype ?G ?A
    |- _ => now apply (f G A)
  | f : forall G A u, isterm G u A -> isctx G * istype G A ,
    _ : isterm ?G ?u ?A |- _ => now apply (f G A u)
  | f : forall G D, eqctx G D -> isctx G * isctx D ,
    _ : eqctx ?G ?D |- _ => now apply (f G D)
  | f : forall G A B, eqtype G A B -> isctx G * istype G A * istype G B ,
    _ : eqtype ?G ?A ?B |- _ => now apply (f G A B)
  | f : forall G u v A,
        eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A ,
    _ : eqterm ?G ?u ?v ?A |- _ => now apply (f G u v A)
  | _ => fail
  end.


Fixpoint sane_issubst {G D sbs} (H : issubst sbs G D) {struct H} :
       isctx G * isctx D

with sane_istype {G A} (H : istype G A) {struct H} :
       isctx G

with sane_isterm {G A u} (H : isterm G u A) {struct H} :
       isctx G * istype G A

with sane_eqctx {G D} (H : eqctx G D) {struct H} :
       isctx G * isctx D

with sane_eqtype {G A B} (H : eqtype G A B) {struct H} :
       isctx G * istype G A * istype G B

with sane_eqterm {G u v A} (H : eqterm G u v A) {struct H} :
       isctx G * istype G A * isterm G u A * isterm G v A.

Proof.
  (****** sane_issubst ******)
  - destruct H ; split.

    (* SubstZero *)
    + ih.
    + apply CtxExtend ; ih.

    (* SubstWeak *)
    + apply CtxExtend.
      * ih.
      * assumption.
    + ih.

    (* SubstShift *)
    + apply CtxExtend.
      * ih.
      * now apply @TySubst with (D := D).
    + apply CtxExtend.
      * ih.
      * assumption.

  (****** sane_istype ******)
  - destruct H.

    (* TyCtxConv *)
    + ih.

    (* TySubst *)
    + ih.

    (* TyProd *)
    + ih.

    (* TyId *)
    + ih.

    (* TyEmpty *)
    + assumption.

    (* TyUnit *)
    + assumption.

    (* TyBool *)
    + assumption.

  (****** sane_isterm ******)
  - destruct H; split.

    (* TermTyConv *)
    + ih.
    + now eapply (sane_eqtype G A B).

    (* TermCtxConv *)
    + ih.
    + apply (@TyCtxConv G D A).
      * ih.
      * assumption.

    (* TermSubst *)
    + ih.
    + apply @TySubst with (D := D).
      * assumption.
      * ih.

    (* TermVarZero *)
    + apply CtxExtend.
      * ih.
      * assumption.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * assumption.

    (* TermVarSucc *)
    + apply CtxExtend.
      * ih.
      * assumption.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * ih.

    (* TermAbs *)
    + ih.
    + apply TyProd.
      * assumption.
      * ih.

    (* TermApp *)
    + ih.
    + apply @TySubst with (D := ctxextend G A).
      * now apply SubstZero.
      * assumption.

    (* TermRefl *)
    + ih.
    + apply TyId.
      * ih.
      * assumption.
      * assumption.

    (* TermJ *)
    + ih.
    + admit.

    (* TermExfalso *)
    + ih.
    + assumption.

    (* TermUnit *)
    + assumption.
    + now apply TyUnit.

    (* TermTrue *)
    + assumption.
    + now apply TyBool.

    (* TermFalse *)
    + assumption.
    + now apply TyBool.

    (* TermCond *)
    + ih.
    + apply @TySubst with (D := ctxextend G Bool).
      * now apply SubstZero.
      * assumption.

  (****** sane_eqctx ******)
  - destruct H; split.

    (* EqCtxEmpty *)
    + exact CtxEmpty.
    + exact CtxEmpty.

    (* EqCtxExtend *)
    + apply CtxExtend ; ih.
    + apply CtxExtend ; ih.

  (****** sane_eqtype ******)
  - destruct H; (split ; [split | idtac]).

    (* EqTyCtxConv *)
    + ih.
    + apply @TyCtxConv with (G := G).
      * ih.
      * assumption.
    + apply @TyCtxConv with (G := G).
      * ih.
      * assumption.

    (* EqTyRefl: forall {G A}*)
    + ih.
    + assumption.
    + assumption.

    (* EqTySym *)
    + ih.
    + ih.
    + ih.

    (* EqTyTrans *)
    + ih.
    + ih.
    + ih.

    (* EqTyWeakNat *)
    + apply CtxExtend.
      * ih.
      * now apply @TySubst with (D := D).
    + eapply TySubst.
      * eapply SubstShift; eassumption.
      * eapply TySubst.
        { eapply SubstWeak; eassumption. }
        { assumption. }
    + eapply TySubst.
      * eapply SubstWeak.
        now apply @TySubst with (D := D).
      * now apply @TySubst with (D := D).

    (* EqTyWeakZero *)
    + ih.
    + eapply TySubst.
      * now eapply SubstZero.
      * eapply TySubst.
        { apply SubstWeak. ih. }
        { assumption. }
    + assumption.

    (* EqTyShiftZero *)
    + ih.
    + eapply TySubst.
      * apply SubstZero.
        now apply @TermSubst with (D := D).
      * eapply TySubst.
        { eapply SubstShift.
          - eassumption.
          - ih.
        }
        { assumption. }
    + eapply TySubst.
      * eassumption.
      * eapply TySubst.
        { now apply SubstZero. }
        { assumption. }

    (* EqTyCongZero *)
    + ih.
    + eapply TySubst.
      * apply SubstZero.
        ih.
      * ih.
    + eapply TySubst.
      * apply SubstZero.
        apply @TermTyConv with (A := A1).
        { ih. }
        { assumption. }
      * eapply @TyCtxConv.
        { ih. }
        { now apply EqCtxExtend. }

    (* EqTySubstProd *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * now apply TyProd.
    + apply TyProd.
      * eapply TySubst.
        { eassumption. }
        { assumption. }
      * eapply TySubst.
        { eapply SubstShift. eassumption. assumption. }
        { assumption. }

    (* EqTySubstId *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * now apply TyId.
    + apply TyId.
      * now apply @TySubst with (D := D).
      * now apply @TermSubst with (D := D).
      * now apply @TermSubst with (D := D).

    (* EqTySubstEmpty *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * apply TyEmpty. ih.
    + apply TyEmpty. ih.

    (* EqTySubstUnit *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * apply TyUnit. ih.
    + apply TyUnit. ih.

    (* EqTySubstBool *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * apply TyBool. ih.
    + apply TyBool. ih.

    (* EqTyExfalso *)
    + ih.
    + assumption.
    + assumption.

    (* CongProd *)
    + ih.
    + apply TyProd.
      * ih.
      * ih.
    + apply TyProd.
      * ih.
      * apply @TyCtxConv with (G := ctxextend G A1).
        { ih. }
        { now apply EqCtxExtend. }


    (* CongId *)
    + ih.
    + apply TyId.
      * ih.
      * ih.
      * ih.
    + apply TyId.
      * ih.
      * apply @TermTyConv with (A := A).
        { ih. }
        { assumption. }
      * apply @TermTyConv with (A := A).
        { ih. }
        { assumption. }

    (* CongTySubst *)
    + ih.
    + apply @TySubst with (D := D).
      * assumption.
      * ih.
    + apply @TySubst with (D := D).
      * assumption.
      * ih.


  (****** sane_eqterm ******)
  - destruct H ;
    (split ; [(split ; [split | idtac]) | idtac]).


    (* EqTyConv *)
    + ih.
    + ih.
    + eapply TermTyConv.
      * ih.
      * assumption.
    + eapply TermTyConv.
      * ih.
      * assumption.

    (* EqCtxConv *)
    + ih.
    + eapply TyCtxConv.
      * ih.
      * assumption.
    + eapply TermCtxConv.
      * ih.
      * assumption.
    + eapply TermCtxConv.
      * ih.
      * assumption.

    (* EqRefl *)
    + ih.
    + ih.
    + assumption.
    + assumption.

    (* EqSym *)
    + ih.
    + ih.
    + ih.
    + ih.

    (* EqTrans *)
    + ih.
    + ih.
    + ih.
    + ih.

    (* EqSubstWeak *)
    + apply CtxExtend.
      * ih.
      * assumption.
    + apply @TySubst with (D := G).
      * now apply SubstWeak.
      * ih.
    + apply @TermSubst with (D := G).
      * now apply SubstWeak.
      * assumption.
    + now apply @TermVarSucc.

    (* EqSubstZeroZero *)
    + ih.
    + ih.
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply TermVarZero.
            ih. }
      * { apply EqTyWeakZero.
          - ih.
          - assumption. }
    + assumption.

    (* EqSubstZeroSucc *)
    + ih.
    + ih.
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply @TermVarSucc with (A := A).
            + assumption.
            + ih. }
      * { apply EqTyWeakZero.
          - ih.
          - assumption. }
    + assumption.

    (* EqSubstShiftZero *)
    + apply CtxExtend.
      * ih.
      * { eapply TySubst.
          - eassumption.
          - assumption. }
    + { eapply TySubst.
        - apply SubstWeak.
          now apply @TySubst with (D := D).
        - now apply @TySubst with (D := D). }
    + { eapply TermTyConv.
        - eapply TermSubst.
          + eapply SubstShift.
            * eassumption.
            * assumption.
          + now apply TermVarZero.
        - now apply EqTyWeakNat. }
    + apply TermVarZero.
      now apply @TySubst with (D := D).

    (* EqSubstShiftSucc *)
    + apply CtxExtend.
      * ih.
      * now apply @TySubst with (D := D).
    + { eapply TySubst.
        - apply SubstWeak.
          now apply @TySubst with (D := D).
        - apply @TySubst with (D := D).
          + assumption.
          + ih. }
    + { eapply TermTyConv.
        - eapply TermSubst.
          + eapply SubstShift.
            * eassumption.
            * assumption.
          + eapply TermVarSucc.
            * eassumption.
            * assumption.
        - apply EqTyWeakNat.
          + assumption.
          + assumption.
          + ih. }
    + { eapply TermSubst.
        - apply SubstWeak.
          now apply @TySubst with (D := D).
        - now apply @TermSubst with (D := D). }

    (* EqSubstAbs *)
    + ih.
    + { apply TyProd.
        - now apply @TySubst with (D := D).
        - eapply TySubst.
          + now apply @SubstShift with (D := D).
          + ih. }
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermAbs.
        - apply @EqTySubstProd with (D := D).
          + assumption.
          + assumption.
          + ih. }
    + { apply TermAbs.
        - now apply @TySubst with (D := D).
        - eapply TermSubst.
          + eapply SubstShift.
            * eassumption.
            * assumption.
          + assumption. }

    (* EqSubstApp *)
    + ih.
    + { eapply TySubst.
        - eassumption.
        - eapply TySubst.
          + now apply SubstZero.
          + assumption. }
    + { apply @TermSubst with (D := D).
        - assumption.
        - now apply TermApp. }
    + { eapply TermTyConv.
        - apply TermApp.
          + { eapply TySubst.
              - eapply SubstShift.
                + eassumption.
                + ih.
              - assumption. }
          + { eapply TermTyConv.
              - apply @TermSubst with (D := D).
                + assumption.
                + eassumption.
              - eapply EqTySubstProd.
                + eassumption.
                + ih.
                + assumption. }
          + now apply @TermSubst with (D := D).
        - now apply EqTyShiftZero. }

    (* EqSubstRefl *)
    + ih.
    + { apply TyId.
        - apply @TySubst with (D := D).
          + assumption.
          + ih.
        - now apply @TermSubst with (D := D).
        - now apply @TermSubst with (D := D). }
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermRefl.
        - apply @EqTySubstId with (D := D).
          + assumption.
          + ih.
          + assumption.
          + assumption. }
    + apply TermRefl.
      now apply @TermSubst with (D := D).

    (* EqSubstJ *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstExfalso *)
    + ih.
    + eapply TySubst.
      * eassumption.
      * assumption.
    + eapply TermSubst.
      * eassumption.
      * apply TermExfalso ; assumption.
    + apply TermExfalso.
      * now apply @TySubst with (D := D).
      * { eapply TermTyConv.
          - apply @TermSubst with (D := D).
            + assumption.
            + eassumption.
          - now apply @EqTySubstEmpty with (D := D).
        }

    (* EqSubstUnit *)
    + ih.
    + apply TyUnit. ih.
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermUnit. ih.
        }
      * now apply @EqTySubstUnit with (D := D).
    + apply TermUnit. ih.

    (* EqSubstTrue *)
    + ih.
    + apply TyBool. ih.
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermTrue. ih.
        }
      * now apply @EqTySubstBool with (D := D).
    + apply TermTrue. ih.

    (* EqSubstFalse *)
    + ih.
    + apply TyBool. ih.
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermFalse. ih.
        }
      * now apply @EqTySubstBool with (D := D).
    + apply TermFalse. ih.

    (* EqSubstCond *)
    + ih.
    + { eapply TySubst.
        - eassumption.
        - apply @TySubst with (D := ctxextend D Bool).
          + now apply SubstZero.
          + assumption.
      }
    + eapply TermSubst.
      * eassumption.
      * now apply TermCond.
    + { eapply TermTyConv.
        - apply TermCond.
          + { eapply TermTyConv.
              - eapply TermSubst.
                + eassumption.
                + eassumption.
              - now apply @EqTySubstBool with (D := D).
            }
          + { eapply TyCtxConv.
              - eapply TySubst.
                + eapply SubstShift.
                  * eassumption.
                  * ih.
                + assumption.
              - apply EqCtxExtend. now apply @EqTySubstBool with (D := D).
            }
          + { eapply TermTyConv.
              - eapply TermSubst.
                + eassumption.
                + eassumption.
              - eapply EqTyTrans.
                + eapply EqTySym. apply EqTyShiftZero.
                  * assumption.
                  * assumption.
                  * apply TermTrue. ih.
                + { apply EqTyCongZero.
                    - now apply @EqTySubstBool with (D := D).
                    - eapply EqTyConv.
                      + now apply @EqSubstTrue with (D := D).
                      + apply EqTySym. now apply @EqTySubstBool with (D := D).
                    - apply EqTyRefl. apply @TySubst with (D := ctxextend D Bool).
                      + apply SubstShift.
                        * assumption.
                        * ih.
                      + assumption.
                  }
            }
          + { eapply TermTyConv.
              - eapply TermSubst.
                + eassumption.
                + eassumption.
              - eapply EqTyTrans.
                + eapply EqTySym. apply EqTyShiftZero.
                  * assumption.
                  * assumption.
                  * apply TermFalse. ih.
                + { apply EqTyCongZero.
                    - now apply @EqTySubstBool with (D := D).
                    - eapply EqTyConv.
                      + now apply @EqSubstFalse with (D := D).
                      + apply EqTySym. now apply @EqTySubstBool with (D := D).
                    - apply EqTyRefl. apply @TySubst with (D := ctxextend D Bool).
                      + apply SubstShift.
                        * assumption.
                        * ih.
                      + assumption.
                  }
            }
        - apply EqTySym. eapply EqTyTrans.
          + eapply EqTySym. now apply EqTyShiftZero.
          + { apply EqTyCongZero.
              - now apply @EqTySubstBool with (D := D).
              - apply EqRefl. now apply @TermSubst with (D := D).
              - apply EqTyRefl. apply @TySubst with (D := ctxextend D Bool).
                + apply SubstShift.
                  * assumption.
                  * ih.
                + assumption.
            }
      }

    (* EqTermExfalso *)
     + ih.
    + assumption.
    + assumption.
    + assumption.

    (* UnitEta *)
    + ih.
    + ih.
    + assumption.
    + assumption.

    (* EqReflection *)
    + ih.
    + eapply TyIdInversion.
      ih.
    + apply @TyIdInversion with (u := u) (v := v).
      ih.
    + apply @TyIdInversion with (u := u) (v := v).
      ih.

    (* ProdBeta *)
    + ih.
    + { eapply TySubst.
        - now apply SubstZero.
        - ih. }
    + apply TermApp.
      * ih.
      * { apply TermAbs.
          - ih.
          - assumption. }
      * assumption.
    + { eapply TermSubst.
        - now apply SubstZero.
        - assumption. }

    (* CongTrue *)
    + ih.
    + eapply TySubst.
      * apply SubstZero. apply TermTrue.
        ih.
      * assumption.
    + apply TermCond ; try assumption.
      apply TermTrue.
      ih.
    + assumption.

    (* CongFalse *)
    + ih.
    + eapply TySubst.
      * apply SubstZero. apply TermFalse.
        ih.
      * assumption.
    + apply TermCond ; try easy.
      apply TermFalse.
      ih.
    + assumption.

    (* ProdEta *)
    + ih.
    + ih.
    + assumption.
    + assumption.

    (* JRefl*)
    + admit.
    + admit.
    + admit.
    + admit.

    (* CongAbs *)
    + ih.
    + apply TyProd.
      * ih.
      * ih.
    + apply TermAbs.
      * ih.
      * ih.
    + { eapply TermTyConv.
        - apply TermAbs.
          + ih.
          + { eapply TermCtxConv.
              - eapply TermTyConv.
                + ih.
                + assumption.
              - now apply EqCtxExtend. }
        - apply CongProd.
          + now apply EqTySym.
          + { eapply EqTyCtxConv.
              - now apply @EqTySym with (G := ctxextend G A1).
              - now apply EqCtxExtend. } }

    (* CongApp *)
    + ih.
    + { eapply TySubst.
        - apply SubstZero.
          ih.
        - ih. }
    + apply TermApp.
      * ih.
      * ih.
      * ih.
    + { eapply TermTyConv.
        - apply TermApp.
          + { eapply TyCtxConv.
              - ih.
              - now apply EqCtxExtend. }
          + { eapply TermTyConv.
              - ih.
              - now apply CongProd. }
          + { eapply TermTyConv.
              - ih.
              - assumption. }
        - apply EqTySym.
          now apply EqTyCongZero. }

    (* ConfRefl *)
    + ih.
    + apply TyId.
      * ih.
      * ih.
      * ih.
    + apply TermRefl.
      ih.
    + { eapply TermTyConv.
        - apply TermRefl.
          { eapply TermTyConv.
            - ih.
            - assumption. }
        - apply EqTySym.
          now apply CongId. }

    (* CongJ *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* CongCond *)
    + ih.
    + eapply TySubst.
      * apply SubstZero. ih.
      * ih.
    + apply TermCond.
      * ih.
      * ih.
      * ih.
      * ih.
    + { eapply TermTyConv.
        - { apply TermCond.
            - ih.
            - ih.
            - eapply TermTyConv.
              + ih.
              + apply @CongTySubst with (D := ctxextend G Bool).
                * apply SubstZero. apply TermTrue.
                  ih.
                * assumption.
            - eapply TermTyConv.
              + ih.
              + apply @CongTySubst with (D := ctxextend G Bool).
                * apply SubstZero. apply TermFalse.
                  ih.
                * assumption.
          }
        - apply EqTySym. eapply EqTyTrans.
          + eapply CongTySubst.
            * apply SubstZero. ih.
            * eassumption.
          + apply EqTyCongZero.
            * apply EqTyRefl. ih.
            * assumption.
            * apply EqTyRefl. ih.
      }

    (* CongTermSubst *)
    + ih.
    + apply @TySubst with (D := D).
      * assumption.
      * ih.
    + apply @TermSubst with (D := D).
      * assumption.
      * ih.
    + apply @TermSubst with (D := D).
      * assumption.
      * ih.

(* Defined. *)
Admitted.
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

(* Magic tactic. *)
Ltac magic :=
  try ih ;
  try easy ;
  try (constructor ; try (ih || easy)).

(* For admitting purposes *)
Lemma todo : False.
Admitted.


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
  - destruct H ; split ; magic.
    (* SubstShift *)
    now apply @TySubst with (D := D).

  (****** sane_istype ******)
  - destruct H ; magic.

  (****** sane_isterm ******)
  - destruct H; split ; magic.

    (* TermCtxConv *)
    + apply (@TyCtxConv G D A) ; magic.

    (* TermSubst *)
    + apply @TySubst with (D := D) ; magic.

    (* TermVarZero *)
    + apply (@TySubst _ G) ; magic.

    (* TermVarSucc *)
    + apply (@TySubst _ G) ; magic.

    (* TermApp *)
    + apply @TySubst with (D := ctxextend G A) ; magic.

    (* TermJ *)
    + { apply @TySubst with (D := ctxextend G (Id A u v)).
        - now apply SubstZero.
        - { apply @TyCtxConv
            with (G :=
                    ctxextend G
                              (Subst
                                 (Id
                                    (Subst A (sbweak G A))
                                    (subst u (sbweak G A))
                                    (var 0))
                                 (sbzero G A v))).
            - { eapply TySubst.
                - eapply SubstShift.
                  + now eapply SubstZero.
                  + magic ; magic.
                    * { eapply TySubst.
                        - apply SubstWeak. magic.
                        - magic.
                      }
                    * { eapply @TermSubst.
                        - magic.
                        - magic.
                      }
                - magic.
              }
            - magic. eapply EqTyTrans.
              + { eapply EqTySubstId.
                  - magic.
                  - eapply TySubst.
                    + magic.
                    + magic.
                  - eapply TermSubst.
                    + magic.
                    + magic.
                  - magic.
                }
              + { apply CongId.
                  - apply EqTyWeakZero.
                    + magic.
                    + magic.
                  - destruct todo. (* This is the missing rule. *)
                  - eapply EqTyConv.
                    + apply EqSubstZeroZero. magic.
                    + apply EqTySym. apply EqTyWeakZero ; magic.
                }
          }
      }

    (* TermCond *)
    + apply @TySubst with (D := ctxextend G Bool) ; magic.

  (****** sane_eqctx ******)
  - destruct H; split ; magic.

  (****** sane_eqtype ******)
  - destruct H; (split ; [split | idtac]) ; magic.

    (* EqTyCtxConv *)
    + apply @TyCtxConv with (G := G) ; magic.
    + apply @TyCtxConv with (G := G) ; magic.

    (* EqTyWeakNat *)
    + now apply @TySubst with (D := D).
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
    + eapply TySubst.
      * now eapply SubstZero.
      * eapply TySubst.
        { apply SubstWeak. ih. }
        { assumption. }

    (* EqTyShiftZero *)
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
    + eapply TySubst ; magic.
    + eapply TySubst.
      * apply SubstZero.
        apply @TermTyConv with (A := A1).
        { ih. }
        { assumption. }
      * eapply @TyCtxConv.
        { ih. }
        { now apply EqCtxExtend. }

    (* EqTySubstProd *)
    + eapply TySubst.
      * eassumption.
      * now apply TyProd.
    + eapply TySubst.
      { eassumption. }
      { assumption. }
    + eapply TySubst.
      { eapply SubstShift. eassumption. assumption. }
      { assumption. }

    (* EqTySubstId *)
    + eapply TySubst.
      * eassumption.
      * now apply TyId.
    + now apply @TySubst with (D := D).
    + now apply @TermSubst with (D := D).
    + now apply @TermSubst with (D := D).

    (* EqTySubstEmpty *)
    + eapply TySubst.
      * eassumption.
      * apply TyEmpty. ih.

    (* EqTySubstUnit *)
    + eapply TySubst.
      * eassumption.
      * apply TyUnit. ih.

    (* EqTySubstBool *)
    + eapply TySubst.
      * eassumption.
      * apply TyBool. ih.

    (* CongProd *)
    + apply @TyCtxConv with (G := ctxextend G A1).
      { ih. }
      { now apply EqCtxExtend. }

    (* CongId *)
    + apply @TermTyConv with (A := A).
      { ih. }
      { assumption. }
    + apply @TermTyConv with (A := A).
      { ih. }
      { assumption. }

    (* CongTySubst *)
    + apply @TySubst with (D := D).
      * assumption.
      * ih.
    + apply @TySubst with (D := D).
      * assumption.
      * ih.


  (****** sane_eqterm ******)
  - destruct H ;
    (split ; [(split ; [split | idtac]) | idtac]) ; magic.

    (* EqTyConv *)
    + eapply TermTyConv.
      * ih.
      * assumption.
    + eapply TermTyConv.
      * ih.
      * assumption.

    (* EqCtxConv *)
    + eapply TyCtxConv.
      * ih.
      * assumption.
    + eapply TermCtxConv.
      * ih.
      * assumption.
    + eapply TermCtxConv.
      * ih.
      * assumption.

    (* Eqsubstweak *)
    + apply @TySubst with (D := G).
      * now apply SubstWeak.
      * ih.
    + apply @TermSubst with (D := G).
      * now apply SubstWeak.
      * assumption.

    (* EqSubstZeroZero *)
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply TermVarZero.
            ih. }
      * { apply EqTyWeakZero.
          - ih.
          - assumption. }

    (* EqSubstZeroSucc *)
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply @TermVarSucc with (A := A).
            + assumption.
            + ih. }
      * { apply EqTyWeakZero.
          - ih.
          - assumption. }

    (* EqSubstShiftZero *)
    + now apply @TySubst with (D := D).
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
    + now apply @TySubst with (D := D).

    (* EqSubstShiftSucc *)
    + now apply @TySubst with (D := D).
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
    + now apply @TySubst with (D := D).
    + eapply TySubst.
      * now apply @SubstShift with (D := D).
      * ih.
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermAbs.
        - apply @EqTySubstProd with (D := D).
          + assumption.
          + assumption.
          + ih. }
    + now apply @TySubst with (D := D).
    + { eapply TermSubst.
        - eapply SubstShift.
          + eassumption.
          + assumption.
        - assumption.
      }

    (* EqSubstApp *)
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
    + apply @TySubst with (D := D) ; magic.
    + now apply @TermSubst with (D := D).
    + now apply @TermSubst with (D := D).
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermRefl.
        - apply @EqTySubstId with (D := D).
          + assumption.
          + ih.
          + assumption.
          + assumption. }
    + now apply @TermSubst with (D := D).

    (* EqSubstJ *)
    + destruct todo.
    + destruct todo.
    + destruct todo.

    (* EqSubstExfalso *)
    + eapply TySubst.
      * eassumption.
      * assumption.
    + eapply TermSubst.
      * eassumption.
      * apply TermExfalso ; assumption.
    + now apply @TySubst with (D := D).
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + eassumption.
        - now apply @EqTySubstEmpty with (D := D).
      }

    (* EqSubstUnit *)
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermUnit. ih.
        }
      * now apply @EqTySubstUnit with (D := D).

    (* EqSubstTrue *)
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermTrue. ih.
        }
      * now apply @EqTySubstBool with (D := D).

    (* EqSubstFalse *)
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermFalse. ih.
        }
      * now apply @EqTySubstBool with (D := D).

    (* EqSubstCond *)
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

    (* EqReflection *)
    + eapply TyIdInversion. magic.
    + apply @TyIdInversion with (u := u) (v := v). magic.
    + apply @TyIdInversion with (u := u) (v := v). magic.


    (* ProdBeta *)
    + { eapply TySubst.
        - now apply SubstZero.
        - ih. }
    + { apply TermAbs.
        - ih.
        - assumption. }
    + { eapply TermSubst.
        - now apply SubstZero.
        - assumption. }

    (* CongTrue *)
    + constructor. ih.

    (* CongFalse *)
    + constructor. ih.

    (* JRefl*)
    + destruct todo.

    (* CongAbs *)
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
    + { eapply TySubst.
        - apply SubstZero.
          ih.
        - ih. }
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
    + { eapply TermTyConv.
        - apply TermRefl.
          { eapply TermTyConv.
            - ih.
            - assumption. }
        - apply EqTySym.
          now apply CongId. }

    (* CongJ *)
    + destruct todo.
    + destruct todo.
    + destruct todo.

    (* CongCond *)
    + eapply TySubst.
      * apply SubstZero. ih.
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
    + apply @TySubst with (D := D).
      * assumption.
      * ih.
    + apply @TermSubst with (D := D).
      * assumption.
      * ih.
    + apply @TermSubst with (D := D).
      * assumption.
      * ih.

Defined.
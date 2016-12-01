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
    + now apply (sane_isterm G A u).
    + apply CtxExtend.
      now apply (sane_isterm G A u).

    (* SubstWeak *)
    + now apply CtxExtend.
    + now apply (sane_istype G A).

    (* SubstShift *)
    + apply CtxExtend.
      now apply @TySubst with (D := D).
    + now apply CtxExtend.

  (****** sane_istype ******)
  - destruct H.

    (* TyCtxConv *)
    + now apply (sane_eqctx G D).

    (* TySubst *)
    + now apply (sane_issubst G D sbs).

    (* TyProd *)
    + now apply (sane_istype G A).

    (* TyId *)
    + now apply (sane_istype G A).

    (* TyEmpty *)
    + assumption.

    (* TyUnit *)
    + assumption.

    (* TyBool *)
    + assumption.

  (****** sane_isterm ******)
  - destruct H; split.

    (* TermTyConv *)
    + now apply (sane_eqtype G A B).
    + now eapply (sane_eqtype G A B).

    (* TermCtxConv *)
    + now apply (sane_eqctx G D).
    + apply (@TyCtxConv G D A).
      * now apply (sane_isterm G A u).
      * assumption.

    (* TermSubst *)
    + now apply (sane_issubst G D sbs).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_isterm D A u).

    (* TermVarZero *)
    + now apply CtxExtend.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * assumption.

    (* TermVarSucc *)
    + now apply CtxExtend.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * now apply (sane_isterm G A (var k)).

    (* TermAbs *)
    + now apply (sane_istype G A).
    + apply TyProd.
      * assumption.
      * now apply (sane_isterm _ B u).

    (* TermApp *)
    + now apply (sane_isterm G (Prod A B) u).
    + apply @TySubst with (D := ctxextend G A).
      * now apply SubstZero.
      * assumption.

    (* TermRefl *)
    + now apply (sane_isterm G A u).
    + apply TyId.
      * now apply (sane_isterm G A u).
      * assumption.
      * assumption.

    (* TermExfalso *)
    + now apply (sane_istype G A).
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
    + now apply (sane_isterm G Bool u).
    + apply @TySubst with (D := ctxextend G Bool).
      * now apply SubstZero.
      * assumption.

  (****** sane_eqctx ******)
  - destruct H; split.

    (* EqCtxEmpty *)
    + exact CtxEmpty.
    + exact CtxEmpty.

    (* EqCtxExtend *)
    + apply CtxExtend.
      now apply (sane_eqtype G A B).
    + apply CtxExtend.
      now apply (sane_eqtype G A B).


  (****** sane_eqtype ******)
  - destruct H; (split ; [split | idtac]).

    (* EqTyCtxConv *)
    + now apply (sane_eqctx G D).
    + apply @TyCtxConv with (G := G).
      * now apply (sane_eqtype G A B).
      * assumption.
    + apply @TyCtxConv with (G := G).
      * now apply (sane_eqtype G A B).
      * assumption.

    (* EqTyRefl: forall {G A}*)
    + now apply (sane_istype G A).
    + assumption.
    + assumption.

    (* EqTySym *)
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).

    (* EqTyTrans *)
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G B C).

    (* EqTyWeakNat *)
    + apply CtxExtend.
      now apply @TySubst with (D := D).
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
    + now apply (sane_istype G A).
    + eapply TySubst.
      * now eapply SubstZero.
      * eapply TySubst.
        { apply SubstWeak. now apply (sane_isterm G B u). }
        { assumption. }
    + assumption.

    (* EqTyShiftZero *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * apply SubstZero.
        now apply @TermSubst with (D := D).
      * eapply TySubst.
        { eapply SubstShift.
          - eassumption.
          - now apply (sane_isterm D A v).
        }
        { assumption. }
    + eapply TySubst.
      * eassumption.
      * eapply TySubst.
        { now apply SubstZero. }
        { assumption. }

    (* EqTyCongZero *)
    + now apply (sane_eqtype G A1 B1).
    + eapply TySubst.
      * apply SubstZero.
        now apply (sane_eqterm G u1 u2 A1).
      * now apply (sane_eqtype _ A2 B2).
    + eapply TySubst.
      * apply SubstZero.
        apply @TermTyConv with (A := A1).
        { now apply (sane_eqterm G u1 u2 A1). }
        { assumption. }
      * eapply @TyCtxConv.
        { now apply (sane_eqtype (ctxextend G A1) A2 B2). }
        { now apply EqCtxExtend. }

    (* EqTySubstProd *)
    + now apply (sane_issubst G D sbs).
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
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * now apply TyId.
    + apply TyId.
      * now apply @TySubst with (D := D).
      * now apply @TermSubst with (D := D).
      * now apply @TermSubst with (D := D).

    (* EqTySubstEmpty *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * apply TyEmpty. now apply (sane_issubst G D sbs).
    + apply TyEmpty. now apply (sane_issubst G D sbs).

    (* EqTySubstUnit *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * apply TyUnit. now apply (sane_issubst G D sbs).
    + apply TyUnit. now apply (sane_issubst G D sbs).

    (* EqTySubstBool *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * apply TyBool. now apply (sane_issubst G D sbs).
    + apply TyBool. now apply (sane_issubst G D sbs).

    (* EqTyExfalso *)
    + now apply (sane_istype G A).
    + assumption.
    + assumption.

    (* CongProd *)
    + now apply (sane_eqtype G A1 B1).
    + apply TyProd.
      * now apply (sane_eqtype G A1 B1).
      * now apply (sane_eqtype _ A2 B2).
    + apply TyProd.
      * now apply (sane_eqtype G A1 B1).
      * apply @TyCtxConv with (G := ctxextend G A1).
        { now apply (sane_eqtype _ A2 B2). }
        { now apply EqCtxExtend. }


    (* CongId *)
    + now apply (sane_eqtype G A B).
    + apply TyId.
      * now apply (sane_eqtype G A B).
      * now apply (sane_eqterm G u1 v1 A).
      * now apply (sane_eqterm G u2 v2 A).
    + apply TyId.
      * now apply (sane_eqtype G A B).
      * apply @TermTyConv with (A := A).
        { now apply (sane_eqterm G u1 v1 A). }
        { assumption. }
      * apply @TermTyConv with (A := A).
        { now apply (sane_eqterm G u2 v2 A). }
        { assumption. }

    (* CongTySubst *)
    + now apply (sane_issubst G D sbs).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_eqtype D A B).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_eqtype D A B).


  (****** sane_eqterm ******)
  - destruct H ;
    (split ; [(split ; [split | idtac]) | idtac]).


    (* EqTyConv *)
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).
    + eapply TermTyConv.
      * now apply (sane_eqterm G u v A).
      * assumption.
    + eapply TermTyConv.
      * now apply (sane_eqterm G u v A).
      * assumption.

    (* EqCtxConv *)
    + now apply (sane_eqctx G D).
    + eapply TyCtxConv.
      * now apply (sane_eqterm G u v A).
      * assumption.
    + eapply TermCtxConv.
      * now apply (sane_eqterm G u v A).
      * assumption.
    + eapply TermCtxConv.
      * now apply (sane_eqterm G u v A).
      * assumption.

    (* EqRefl *)
    + now apply (sane_isterm G A u).
    + now apply (sane_isterm G A u).
    + assumption.
    + assumption.

    (* EqSym *)
    + now apply (sane_eqterm G v u A).
    + now apply (sane_eqterm G v u A).
    + now apply (sane_eqterm G v u A).
    + now apply (sane_eqterm G v u A).

    (* EqTrans *)
    + now apply (sane_eqterm G u v A).
    + now apply (sane_eqterm G u v A).
    + now apply (sane_eqterm G u v A).
    + now apply (sane_eqterm G v w A).

    (* EqSubstWeak *)
    + now apply CtxExtend.
    + apply @TySubst with (D := G).
      * now apply SubstWeak.
      * now apply (sane_isterm G A (var k)).
    + apply @TermSubst with (D := G).
      * now apply SubstWeak.
      * assumption.
    + now apply @TermVarSucc.

    (* EqSubstZeroZero *)
    + now apply (sane_isterm G A u).
    + now apply (sane_isterm G A u).
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply TermVarZero.
            now apply (sane_isterm G A u). }
      * { apply EqTyWeakZero.
          - now apply (sane_isterm G A u).
          - assumption. }
    + assumption.

    (* EqSubstZeroSucc *)
    + now apply (sane_isterm G A (var k)).
    + now apply (sane_isterm G A (var k)).
    + eapply TermTyConv.
      * { eapply TermSubst.
          - now apply SubstZero.
          - apply @TermVarSucc with (A := A).
            + assumption.
            + now apply (sane_isterm G B u). }
      * { apply EqTyWeakZero.
          - now apply (sane_isterm G A (var k)).
          - assumption. }
    + assumption.

    (* EqSubstShiftZero *)
    + apply CtxExtend.
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
      now apply @TySubst with (D := D).
    + { eapply TySubst.
        - apply SubstWeak.
          now apply @TySubst with (D := D).
        - apply @TySubst with (D := D).
          + assumption.
          + now apply (sane_isterm D B (var k)). }
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
          + now apply (sane_isterm D B (var k)). }
    + { eapply TermSubst.
        - apply SubstWeak.
          now apply @TySubst with (D := D).
        - now apply @TermSubst with (D := D). }

    (* EqSubstAbs *)
    + now apply (sane_issubst G D sbs).
    + { apply TyProd.
        - now apply @TySubst with (D := D).
        - eapply TySubst.
          + now apply @SubstShift with (D := D).
          + now apply (sane_isterm _ B u). }
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermAbs.
        - apply @EqTySubstProd with (D := D).
          + assumption.
          + assumption.
          + now apply (sane_isterm _ B u). }
    + { apply TermAbs.
        - now apply @TySubst with (D := D).
        - eapply TermSubst.
          + eapply SubstShift.
            * eassumption.
            * assumption.
          + assumption. }

    (* EqSubstApp *)
    + now apply (sane_issubst G D sbs).
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
                + now apply (sane_isterm D A v).
              - assumption. }
          + { eapply TermTyConv.
              - apply @TermSubst with (D := D).
                + assumption.
                + eassumption.
              - eapply EqTySubstProd.
                + eassumption.
                + now apply (sane_isterm D A v).
                + assumption. }
          + now apply @TermSubst with (D := D).
        - now apply EqTyShiftZero. }

    (* EqSubstRefl *)
    + now apply (sane_issubst G D sbs).
    + { apply TyId.
        - apply @TySubst with (D := D).
          + assumption.
          + now apply (sane_isterm D A u).
        - now apply @TermSubst with (D := D).
        - now apply @TermSubst with (D := D). }
    + { eapply TermTyConv.
        - apply @TermSubst with (D := D).
          + assumption.
          + now apply TermRefl.
        - apply @EqTySubstId with (D := D).
          + assumption.
          + now apply (sane_isterm D A u).
          + assumption.
          + assumption. }
    + apply TermRefl.
      now apply @TermSubst with (D := D).

    (* EqSubstExfalso *)
    + now apply (sane_issubst G D sbs).
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
    + now apply (sane_issubst G D sbs).
    + apply TyUnit. now apply (sane_issubst G D sbs).
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermUnit. now apply (sane_issubst G D sbs).
        }
      * now apply @EqTySubstUnit with (D := D).
    + apply TermUnit. now apply (sane_issubst G D sbs).

    (* EqSubstTrue *)
    + now apply (sane_issubst G D sbs).
    + apply TyBool. now apply (sane_issubst G D sbs).
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermTrue. now apply (sane_issubst G D sbs).
        }
      * now apply @EqTySubstBool with (D := D).
    + apply TermTrue. now apply (sane_issubst G D sbs).

    (* EqSubstFalse *)
    + now apply (sane_issubst G D sbs).
    + apply TyBool. now apply (sane_issubst G D sbs).
    + eapply TermTyConv.
      * { apply @TermSubst with (D := D).
          - assumption.
          - apply TermFalse. now apply (sane_issubst G D sbs).
        }
      * now apply @EqTySubstBool with (D := D).
    + apply TermFalse. now apply (sane_issubst G D sbs).

    (* EqSubstCond *)
    + now apply (sane_issubst G D sbs).
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
                  * now apply (sane_isterm D Bool u).
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
                  * apply TermTrue. now apply (sane_issubst G D sbs).
                + { apply EqTyCongZero.
                    - now apply @EqTySubstBool with (D := D).
                    - eapply EqTyConv.
                      + now apply @EqSubstTrue with (D := D).
                      + apply EqTySym. now apply @EqTySubstBool with (D := D).
                    - apply EqTyRefl. apply @TySubst with (D := ctxextend D Bool).
                      + apply SubstShift.
                        * assumption.
                        * now apply (sane_isterm D Bool u).
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
                  * apply TermFalse. now apply (sane_issubst G D sbs).
                + { apply EqTyCongZero.
                    - now apply @EqTySubstBool with (D := D).
                    - eapply EqTyConv.
                      + now apply @EqSubstFalse with (D := D).
                      + apply EqTySym. now apply @EqTySubstBool with (D := D).
                    - apply EqTyRefl. apply @TySubst with (D := ctxextend D Bool).
                      + apply SubstShift.
                        * assumption.
                        * now apply (sane_isterm D Bool u).
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
                  * now apply (sane_isterm D Bool u).
                + assumption.
            }
      }

    (* EqTermExfalso *)
     + now apply (sane_istype G A).
    + assumption.
    + assumption.
    + assumption.

    (* UnitEta *)
    + now apply (sane_isterm G Unit u).
    + now apply (sane_isterm G Unit u).
    + assumption.
    + assumption.

    (* EqReflection *)
    + now apply (sane_isterm G (Id A u v) w1).
    + eapply TyIdInversion.
      now apply (sane_isterm G (Id A u v) w1).
    + apply @TyIdInversion with (u := u) (v := v).
      now apply (sane_isterm G (Id A u v) w1).
    + apply @TyIdInversion with (u := u) (v := v).
      now apply (sane_isterm G (Id A u v) w1).

    (* ProdBeta *)
    + now apply (sane_isterm G A v).
    + { eapply TySubst.
        - now apply SubstZero.
        - now apply (sane_isterm _ B u). }
    + apply TermApp.
      * now apply (sane_isterm _ B u).
      * { apply TermAbs.
          - now apply (sane_isterm G A v).
          - assumption. }
      * assumption.
    + { eapply TermSubst.
        - now apply SubstZero.
        - assumption. }

    (* CongTrue *)
    + now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
    + eapply TySubst.
      * apply SubstZero. apply TermTrue.
        now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
      * assumption.
    + apply TermCond ; try assumption.
      apply TermTrue.
      now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
    + assumption.

    (* CongFalse *)
    + now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
    + eapply TySubst.
      * apply SubstZero. apply TermFalse.
        now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
      * assumption.
    + apply TermCond ; try easy.
      apply TermFalse.
      now apply (sane_isterm G (Subst C (sbzero G Bool true)) v).
    + assumption.

    (* ProdEta *)
    + now apply (sane_isterm G (Prod A B) u).
    + now apply (sane_isterm G (Prod A B) u).
    + assumption.
    + assumption.

    (* CongAbs *)
    + now apply (sane_eqtype G A1 B1).
    + apply TyProd.
      * now apply (sane_eqtype G A1 B1).
      * now apply (sane_eqtype _ A2 B2).
    + apply TermAbs.
      * now apply (sane_eqtype G A1 B1).
      * now apply (sane_eqterm _ u1 u2 A2).
    + { eapply TermTyConv.
        - apply TermAbs.
          + now apply (sane_eqtype G A1 B1).
          + { eapply TermCtxConv.
              - eapply TermTyConv.
                + now apply (sane_eqterm (ctxextend G A1) u1 u2 A2).
                + assumption.
              - now apply EqCtxExtend. }
        - apply CongProd.
          + now apply EqTySym.
          + { eapply EqTyCtxConv.
              - now apply @EqTySym with (G := ctxextend G A1).
              - now apply EqCtxExtend. } }

    (* CongApp *)
    + now apply (sane_eqtype G A1 B1).
    + { eapply TySubst.
        - apply SubstZero.
          now apply (sane_eqterm G u2 v2 A1).
        - now apply (sane_eqtype _ A2 B2). }
    + apply TermApp.
      * now apply (sane_eqtype _ A2 B2).
      * now apply (sane_eqterm G u1 v1 _).
      * now apply (sane_eqterm G u2 v2 A1).
    + { eapply TermTyConv.
        - apply TermApp.
          + { eapply TyCtxConv.
              - now apply (sane_eqtype (ctxextend G A1) A2 B2).
              - now apply EqCtxExtend. }
          + { eapply TermTyConv.
              - now apply (sane_eqterm G u1 v1 (Prod A1 A2)).
              - now apply CongProd. }
          + { eapply TermTyConv.
              - now apply (sane_eqterm G u2 v2 A1).
              - assumption. }
        - apply EqTySym.
          now apply EqTyCongZero. }

    (* ConfRefl *)
    + now apply (sane_eqtype G A1 A2).
    + apply TyId.
      * now apply (sane_eqtype G A1 A2).
      * now apply (sane_eqterm G u1 u2 A1).
      * now apply (sane_eqterm G u1 u2 A1).
    + apply TermRefl.
      now apply (sane_eqterm G u1 u2 A1).
    + { eapply TermTyConv.
        - apply TermRefl.
          { eapply TermTyConv.
            - now apply (sane_eqterm G u1 u2 A1).
            - assumption. }
        - apply EqTySym.
          now apply CongId. }

    (* CongCond *)
    + now apply (sane_eqterm G u1 u2 Bool).
    + eapply TySubst.
      * apply SubstZero. now apply (sane_eqterm G u1 u2 Bool).
      * now apply (sane_eqtype (ctxextend G Bool) C1 C2).
    + apply TermCond.
      * now apply (sane_eqterm G u1 u2 Bool).
      * now apply (sane_eqtype (ctxextend G Bool) C1 C2).
      * now apply (sane_eqterm G v1 v2 (Subst C1 (sbzero G Bool true))).
      * now apply (sane_eqterm G w1 w2 (Subst C1 (sbzero G Bool false))).
    + { eapply TermTyConv.
        - { apply TermCond.
            - now apply (sane_eqterm G u1 u2 Bool).
            - now apply (sane_eqtype (ctxextend G Bool) C1 C2).
            - eapply TermTyConv.
              + now apply (sane_eqterm G v1 v2 (Subst C1 (sbzero G Bool true))).
              + apply @CongTySubst with (D := ctxextend G Bool).
                * apply SubstZero. apply TermTrue.
                  now apply (sane_eqterm G u1 u2 Bool).
                * assumption.
            - eapply TermTyConv.
              + now apply (sane_eqterm G w1 w2 (Subst C1 (sbzero G Bool false))).
              + apply @CongTySubst with (D := ctxextend G Bool).
                * apply SubstZero. apply TermFalse.
                  now apply (sane_eqterm G u1 u2 Bool).
                * assumption.
          }
        - apply EqTySym. eapply EqTyTrans.
          + eapply CongTySubst.
            * apply SubstZero. now apply (sane_eqterm G u1 u2 Bool).
            * eassumption.
          + apply EqTyCongZero.
            * apply EqTyRefl. now apply (sane_eqterm G u1 u2 Bool).
            * assumption.
            * apply EqTyRefl. now apply (sane_eqtype (ctxextend G Bool) C1 C2).
      }

    (* CongTermSubst *)
    + now apply (sane_issubst G D sbs).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_eqterm D u1 u2 A).
    + apply @TermSubst with (D := D).
      * assumption.
      * now apply (sane_eqterm D u1 u2 A).
    + apply @TermSubst with (D := D).
      * assumption.
      * now apply (sane_eqterm D u1 u2 A).

Admitted.
(* Defined. *)
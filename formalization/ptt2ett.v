Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require ptt ett.

Section Ptt2Ett.

Context `{configReflection : config.Reflection}.

Fixpoint sane_isctx G (P : ptt.isctx G) : ett.isctx G

with sane_issubst sbs G D (P : ptt.issubst sbs G D) {struct P} : ett.issubst sbs G D

with sane_istype G A (P : ptt.istype G A) {struct P} : ett.istype G A

with sane_isterm G u A (P : ptt.isterm G u A) {struct P} : ett.isterm G u A

with sane_eqctx G D (P : ptt.eqctx G D) {struct P} : ett.eqctx G D

with sane_eqsubst sbs sbt G D (P : ptt.eqsubst sbs sbt G D) {struct P} : ett.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ptt.eqtype G A B) {struct P} : ett.eqtype G A B

with sane_eqterm G u v A (P : ptt.eqterm G u v A) {struct P} : ett.eqterm G u v A.

Proof.
  (* sane_isctx *)
  - { destruct P; doConfig.
    - now apply CtxEmpty.
    - capply CtxExtend. now apply sane_istype.
    }

  (* sane_issubst *)
  - { destruct P; doConfig.

      (* SubstZero *)
      - capply SubstZero ; now apply sane_isterm.

      (* SubstWeak *)
      - capply SubstWeak ; now capply sane_istype.

      (* SubstShift *)
      - { capply SubstShift.
          + now capply sane_issubst.
          + now capply sane_istype.
        }

      (* SubstId *)
      - capply SubstId. now capply sane_isctx.

      (* SubstComp *)
       - { capply (@SubstComp _ _ G D E).
           - now capply sane_issubst.
           - now capply sane_issubst.
         }

      (* SubstCtxConv *)
      - { capply (@SubstCtxConv _ _ G1 G2 D1 D2).
          - now capply sane_issubst.
          - now capply sane_eqctx.
          - now capply sane_eqctx.
        }
  }

  (* sane_istype *)
  - { destruct P; doConfig.

      (* TyCtxConv *)
      - capply (@TyCtxConv _ _ G D) ; auto.

      (* TySubst *)
      - capply (@TySubst _ _ G D) ; auto.

      (* TyProd *)
      - capply TyProd ; auto.

      (* TyId *)
      - capply TyId ; auto.

      (* TyEmpty *)
      - capply TyEmpty ; auto.

      (* TyUnit *)
      - capply TyUnit ; auto.

      (* TyBool *)
      - capply TyBool ; auto.
  }

  (* sane_isterm *)
  - { destruct P; doConfig.

      (* TermTyConv *)
       - apply (@TermTyConv G A B) ; auto.

      (* TermCtxConv *)
      - apply (@TermCtxConv G D) ; auto.

      (* TermSubst *)
      - apply (@TermSubst G D) ; auto.

      (* TermVarZero *)
      - apply TermVarZero ; auto.

      (* TermVarSucc *)
      - apply TermVarSucc ; auto.

      (* TermAbs *)
      - apply TermAbs ; auto.

      (* TermApp *)
      - apply TermApp ; auto.

      (* TermRefl *)
      - apply TermRefl ; auto.

      (* TermJ *)
      - apply TermJ ; auto.

      (* TermExfalso *)
      - apply TermExfalso ; auto.

      (* TermUnit *)
      - apply TermUnit ; auto.

      (* TermTrue *)
      - apply TermTrue ; auto.

      (* TermFalse *)
      - apply TermFalse ; auto.

      (* TermCond *)
      - apply TermCond ; auto.
  }

  (* sane_eqctx *)
  - { destruct P; doConfig.

      (* CtxRefl *)
      - apply CtxRefl ; auto.

      (* CtxSym *)
      - apply CtxSym ; auto.

      (* CtxTrans *)
      - apply (@CtxTrans G D E) ; auto.

      (* EqCtxEmpty *)
      - apply CtxRefl, CtxEmpty.

      (* EqCtxExtend *)
      - apply EqCtxExtend ; auto.
  }

  (* sane_eqsubst *)
  - { destruct P; doConfig.

      (* SubstRefl *)
      - apply SubstRefl ; auto.

      (* SubstSym *)
      - apply SubstSym ; auto.

      (* SubstTrans *)
      - apply (@SubstTrans G D sb1 sb2 sb3) ; auto.

      (* CongSubstZero *)
      - apply (@CongSubstZero G) ; auto.

      (* CongSubstWeak *)
      - apply CongSubstWeak ; auto.

      (* CongSubstShift *)
      - apply CongSubstShift ; auto.

      (* CongSubstComp *)
      - apply (@CongSubstComp G D E) ; auto.

      (* EqSubstCtxConv *)
      - apply (@EqSubstCtxConv G1 G2 D1 D2) ; auto.

      (* CompAssoc *)
      - apply (@CompAssoc G D E F) ; auto.

      (* WeakNat *)
      - apply WeakNat ; auto.

      (* WeakZero *)
      - apply WeakZero ; auto.

      (* ShiftZero *)
      - apply ShiftZero ; auto.

      (* CompShift *)
      - apply (@CompShift G D) ; auto.

      (* CompIdRight *)
      - apply CompIdRight ; auto.

      (* CompIdLeft *)
      - apply CompIdLeft ; auto.
  }

  (* sane_eqtype *)
  - { destruct P; doConfig.

      (* EqTyCtxConv *)
      - apply (@EqTyCtxConv G D); auto.

      (* EqTyRefl*)
      - apply EqTyRefl ; auto.

      (* EqTySym *)
      - apply EqTySym ; auto.

      (* EqTyTrans *)
      - apply (@EqTyTrans G A B C) ; auto.

      (* EqTyIdSubst *)
      - apply EqTyIdSubst ; auto.

      (* EqTySubstComp *)
      - apply (@EqTySubstComp G D E) ; auto.

      (* EqTySubstProd *)
      - apply (@EqTySubstProd G D) ; auto.

      (* EqTySubstId *)
      - apply (@EqTySubstId G D) ; auto.

      (* EqTySubstEmpty *)
      - apply (@EqTySubstEmpty G D) ; auto.

      (* EqTySubstUnit *)
      - apply (@EqTySubstUnit G D) ; auto.

      (* EqTySubstBool *)
      - apply (@EqTySubstBool G D) ; auto.

      (* EqTyExfalso *)
      - apply (@EqTyExfalso G A B u) ; auto.

      (* CongProd *)
      - apply CongProd ; auto.

      (* CongId *)
      - apply CongId ; auto.

      (* CongTySubst *)
      - apply (@CongTySubst G D A B sbs sbt) ; auto.
  }

  (* sane_eqterm *)
  - { destruct P ; doConfig.

      (* EqTyConv *)
      - apply (@EqTyConv G A B) ; auto.

      (* EqCtxConv *)
      - apply (@EqCtxConv G D) ; auto.

      (* EqRefl *)
      - apply EqRefl ; auto.

      (* EqSym *)
      - apply EqSym ; auto.

      (* EqTrans *)
      - apply (@EqTrans G A u v w) ; auto.

      (* EqIdSubst *)
      - apply EqIdSubst ; auto.

      (* EqSubstComp *)
      - apply (@EqSubstComp G D E); auto.

      (* EqSubstWeak *)
      - apply EqSubstWeak ; auto.


      (* EqSubstZeroZero *)
      - apply EqSubstZeroZero ; auto.

      (* EqSubstZeroSucc *)
      - apply EqSubstZeroSucc ; auto.

      (* EqSubstShiftZero *)
      - apply (@EqSubstShiftZero G D) ; auto.

      (* EqSubstShiftSucc *)
      - apply (@EqSubstShiftSucc G D) ; auto.

      (* EqSubstAbs *)
      - apply (@EqSubstAbs G D) ; auto.

      (* EqSubstApp *)
      - apply (@EqSubstApp G D) ; auto.

      (* EqSubstRefl *)
      - apply (@EqSubstRefl G D) ; auto.

      (* EqSubstJ *)
      - apply (@EqSubstJ G D) ; auto.

     (* This rule is subsumed by EqTermExfalso *)
      (* EqSubstExfalso *)
      - apply (@EqSubstExfalso G D) ; auto.

      (* EqSubstUnit *)
      - apply (@EqSubstUnit G D) ; auto.

      (* EqSubstTrue *)
      - apply (@EqSubstTrue G D) ; auto.

      (* EqSubstFalse *)
      - apply (@EqSubstFalse G D) ; auto.

      (* EqSubstCond *)
      - apply (@EqSubstCond G D); auto.

      (* EqTermExfalso *)
      - apply (@EqTermExfalso G A u v w); auto.

      (* UnitEta *)
      - apply UnitEta ; auto.

      (* EqReflection *)
      - (* I told it the argument was implicit... *)
        (* apply (@EqReflection G A u v w1 w2) ; auto. *)
        apply (@EqReflection r G A u v w1 w2) ; auto.

      (* ProdBeta *)
      - apply ProdBeta ; auto.

      (* CondTrue *)
      - apply CondTrue ; auto.

      (* CondFalse *)
      - apply CondFalse ; auto.

      (* ProdEta *)
      - apply ProdEta ; auto.

      (* JRefl *)
      - apply JRefl ; auto.

      (* CongAbs *)
      - apply CongAbs ; auto.

      (* CongApp *)
      - apply CongApp ; auto.

      (* CongRefl *)
      - apply CongRefl ; auto.

      (* CongJ *)
      - apply CongJ ; auto.

      (* CongCond *)
      - apply CongCond ; auto.

      (* CongTermSubst *)
    - apply (@CongTermSubst G D) ; auto.
    }
Defined.

End Ptt2Ett.
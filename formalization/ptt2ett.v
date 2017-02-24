Require Import syntax.
Require config_tactics.
Require ptt ett.

Module Make (ConfigReflection : tt.CONFIG_REFLECTION).

Module Ptt := ptt.Make ConfigReflection.
Module Ett := ett.Make ConfigReflection.

Module my_config_tactics := config_tactics.Make (tt.HasPrecond) (ConfigReflection).
Import my_config_tactics.

Fixpoint sane_isctx G (P : Ptt.isctx G) : Ett.isctx G

with sane_issubst sbs G D (P : Ptt.issubst sbs G D) {struct P} : Ett.issubst sbs G D

with sane_istype G A (P : Ptt.istype G A) {struct P} : Ett.istype G A

with sane_isterm G u A (P : Ptt.isterm G u A) {struct P} : Ett.isterm G u A

with sane_eqctx G D (P : Ptt.eqctx G D) {struct P} : Ett.eqctx G D

with sane_eqsubst sbs sbt G D (P : Ptt.eqsubst sbs sbt G D) {struct P} : Ett.eqsubst sbs sbt G D

with sane_eqtype G A B (P : Ptt.eqtype G A B) {struct P} : Ett.eqtype G A B

with sane_eqterm G u v A (P : Ptt.eqterm G u v A) {struct P} : Ett.eqterm G u v A.

Proof.
  (* sane_isctx *)
  - { destruct P; doConfig.
    - now apply Ett.CtxEmpty.
    - capply Ett.CtxExtend ; auto using sane_isctx, sane_istype.
    }

  (* sane_issubst *)
  - { destruct P; doConfig.

      (* SubstZero *)
      - (config apply Ett.SubstZero) ; auto.

      (* SubstWeak *)
      - apply Ett.SubstWeak ; auto.

      (* SubstShift *)
      - apply Ett.SubstShift ; auto.

      (* SubstId *)
      - apply Ett.SubstId ; auto.

      (* SubstComp *)
       - apply (@Ett.SubstComp G D E) ; auto.

      (* SubstCtxConv *)
      - apply (@Ett.SubstCtxConv G1 G2 D1 D2) ; auto.
  }

  (* sane_istype *)
  - { destruct P; doConfig.

      (* TyCtxConv *)
      - apply (@Ett.TyCtxConv G D) ; auto.

      (* TySubst *)
      - apply (@Ett.TySubst G D) ; auto.

      (* TyProd *)
      - apply Ett.TyProd ; auto.

      (* TyId *)
      - apply Ett.TyId ; auto.

      (* TyEmpty *)
      - apply Ett.TyEmpty ; auto.

      (* TyUnit *)
      - apply Ett.TyUnit ; auto.

      (* TyBool *)
      - apply Ett.TyBool ; auto.
  }

  (* sane_isterm *)
  - { destruct P; doConfig.

      (* TermTyConv *)
       - apply (@Ett.TermTyConv G A B) ; auto.

      (* TermCtxConv *)
      - apply (@Ett.TermCtxConv G D) ; auto.

      (* TermSubst *)
      - apply (@Ett.TermSubst G D) ; auto.

      (* TermVarZero *)
      - apply Ett.TermVarZero ; auto.

      (* TermVarSucc *)
      - apply Ett.TermVarSucc ; auto.

      (* TermAbs *)
      - apply Ett.TermAbs ; auto.

      (* TermApp *)
      - apply Ett.TermApp ; auto.

      (* TermRefl *)
      - apply Ett.TermRefl ; auto.

      (* TermJ *)
      - apply Ett.TermJ ; auto.

      (* TermExfalso *)
      - apply Ett.TermExfalso ; auto.

      (* TermUnit *)
      - apply Ett.TermUnit ; auto.

      (* TermTrue *)
      - apply Ett.TermTrue ; auto.

      (* TermFalse *)
      - apply Ett.TermFalse ; auto.

      (* TermCond *)
      - apply Ett.TermCond ; auto.
  }

  (* sane_eqctx *)
  - { destruct P; doConfig.

      (* CtxRefl *)
      - apply Ett.CtxRefl ; auto.

      (* CtxSym *)
      - apply Ett.CtxSym ; auto.

      (* CtxTrans *)
      - apply (@Ett.CtxTrans G D E) ; auto.

      (* EqCtxEmpty *)
      - apply Ett.CtxRefl, Ett.CtxEmpty.

      (* EqCtxExtend *)
      - apply Ett.EqCtxExtend ; auto.
  }

  (* sane_eqsubst *)
  - { destruct P; doConfig.

      (* SubstRefl *)
      - apply Ett.SubstRefl ; auto.

      (* SubstSym *)
      - apply Ett.SubstSym ; auto.

      (* SubstTrans *)
      - apply (@Ett.SubstTrans G D sb1 sb2 sb3) ; auto.

      (* CongSubstZero *)
      - apply (@Ett.CongSubstZero G) ; auto.

      (* CongSubstWeak *)
      - apply Ett.CongSubstWeak ; auto.

      (* CongSubstShift *)
      - apply Ett.CongSubstShift ; auto.

      (* CongSubstComp *)
      - apply (@Ett.CongSubstComp G D E) ; auto.

      (* EqSubstCtxConv *)
      - apply (@Ett.EqSubstCtxConv G1 G2 D1 D2) ; auto.

      (* CompAssoc *)
      - apply (@Ett.CompAssoc G D E F) ; auto.

      (* WeakNat *)
      - apply Ett.WeakNat ; auto.

      (* WeakZero *)
      - apply Ett.WeakZero ; auto.

      (* ShiftZero *)
      - apply Ett.ShiftZero ; auto.

      (* CompShift *)
      - apply (@Ett.CompShift G D) ; auto.

      (* CompIdRight *)
      - apply Ett.CompIdRight ; auto.

      (* CompIdLeft *)
      - apply Ett.CompIdLeft ; auto.
  }

  (* sane_eqtype *)
  - { destruct P; doConfig.

      (* EqTyCtxConv *)
      - apply (@Ett.EqTyCtxConv G D); auto.

      (* EqTyRefl*)
      - apply Ett.EqTyRefl ; auto.

      (* EqTySym *)
      - apply Ett.EqTySym ; auto.

      (* EqTyTrans *)
      - apply (@Ett.EqTyTrans G A B C) ; auto.

      (* EqTyIdSubst *)
      - apply Ett.EqTyIdSubst ; auto.

      (* EqTySubstComp *)
      - apply (@Ett.EqTySubstComp G D E) ; auto.

      (* EqTySubstProd *)
      - apply (@Ett.EqTySubstProd G D) ; auto.

      (* EqTySubstId *)
      - apply (@Ett.EqTySubstId G D) ; auto.

      (* EqTySubstEmpty *)
      - apply (@Ett.EqTySubstEmpty G D) ; auto.

      (* EqTySubstUnit *)
      - apply (@Ett.EqTySubstUnit G D) ; auto.

      (* EqTySubstBool *)
      - apply (@Ett.EqTySubstBool G D) ; auto.

      (* EqTyExfalso *)
      - apply (@Ett.EqTyExfalso G A B u) ; auto.

      (* CongProd *)
      - apply Ett.CongProd ; auto.

      (* CongId *)
      - apply Ett.CongId ; auto.

      (* CongTySubst *)
      - apply (@Ett.CongTySubst G D A B sbs sbt) ; auto.
  }

  (* sane_eqterm *)
  - { destruct P ; doConfig.

      (* EqTyConv *)
      - apply (@Ett.EqTyConv G A B) ; auto.

      (* EqCtxConv *)
      - apply (@Ett.EqCtxConv G D) ; auto.

      (* EqRefl *)
      - apply Ett.EqRefl ; auto.

      (* EqSym *)
      - apply Ett.EqSym ; auto.

      (* EqTrans *)
      - apply (@Ett.EqTrans G A u v w) ; auto.

      (* EqIdSubst *)
      - apply Ett.EqIdSubst ; auto.

      (* EqSubstComp *)
      - apply (@Ett.EqSubstComp G D E); auto.

      (* EqSubstWeak *)
      - apply Ett.EqSubstWeak ; auto.


      (* EqSubstZeroZero *)
      - apply Ett.EqSubstZeroZero ; auto.

      (* EqSubstZeroSucc *)
      - apply Ett.EqSubstZeroSucc ; auto.

      (* EqSubstShiftZero *)
      - apply (@Ett.EqSubstShiftZero G D) ; auto.

      (* EqSubstShiftSucc *)
      - apply (@Ett.EqSubstShiftSucc G D) ; auto.

      (* EqSubstAbs *)
      - apply (@Ett.EqSubstAbs G D) ; auto.

      (* EqSubstApp *)
      - apply (@Ett.EqSubstApp G D) ; auto.

      (* EqSubstRefl *)
      - apply (@Ett.EqSubstRefl G D) ; auto.

      (* EqSubstJ *)
      - apply (@Ett.EqSubstJ G D) ; auto.

     (* This rule is subsumed by EqTermExfalso *)
      (* EqSubstExfalso *)
      - apply (@Ett.EqSubstExfalso G D) ; auto.

      (* EqSubstUnit *)
      - apply (@Ett.EqSubstUnit G D) ; auto.

      (* EqSubstTrue *)
      - apply (@Ett.EqSubstTrue G D) ; auto.

      (* EqSubstFalse *)
      - apply (@Ett.EqSubstFalse G D) ; auto.

      (* EqSubstCond *)
      - apply (@Ett.EqSubstCond G D); auto.

      (* EqTermExfalso *)
      - apply (@Ett.EqTermExfalso G A u v w); auto.

      (* UnitEta *)
      - apply Ett.UnitEta ; auto.

      (* EqReflection *)
      - (* I told it the argument was implicit... *)
        (* apply (@Ett.EqReflection G A u v w1 w2) ; auto. *)
        apply (@Ett.EqReflection r G A u v w1 w2) ; auto.

      (* ProdBeta *)
      - apply Ett.ProdBeta ; auto.

      (* CondTrue *)
      - apply Ett.CondTrue ; auto.

      (* CondFalse *)
      - apply Ett.CondFalse ; auto.

      (* ProdEta *)
      - apply Ett.ProdEta ; auto.

      (* JRefl *)
      - apply Ett.JRefl ; auto.

      (* CongAbs *)
      - apply Ett.CongAbs ; auto.

      (* CongApp *)
      - apply Ett.CongApp ; auto.

      (* CongRefl *)
      - apply Ett.CongRefl ; auto.

      (* CongJ *)
      - apply Ett.CongJ ; auto.

      (* CongCond *)
      - apply Ett.CongCond ; auto.

      (* CongTermSubst *)
    - apply (@Ett.CongTermSubst G D) ; auto.
    }
Defined.

End Make.
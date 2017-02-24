Require Import syntax config_tactics.

Require ett ptt ptt_sanity ptt_inversion.

(* Renaming ptt_sanity lemmata for readability. *)
Definition ptt_sane_issubst := ptt_sanity.sane_issubst.
Definition ptt_sane_istype  := ptt_sanity.sane_istype.
Definition ptt_sane_isterm  := ptt_sanity.sane_isterm.
Definition ptt_sane_eqctx   := ptt_sanity.sane_eqctx.
Definition ptt_sane_eqtype  := ptt_sanity.sane_eqtype.
Definition ptt_sane_eqsubst := ptt_sanity.sane_eqsubst.
Definition ptt_sane_eqterm  := ptt_sanity.sane_eqterm.

(* Same for inversion *)
Definition ptt_CtxExtendInversion := ptt_inversion.CtxExtendInversion.
Definition ptt_TyProdInversion    := ptt_inversion.TyProdInversion.
Definition ptt_TyIdInversion      := ptt_inversion.TyIdInversion.


Fixpoint sane_isctx G (P : ett.isctx G) {struct P} : ptt.isctx G

with sane_issubst sbs G D (P : ett.issubst sbs G D) {struct P} : ptt.issubst sbs G D

with sane_istype G A (P : ett.istype G A) {struct P} : ptt.istype G A

with sane_isterm G u A (P : ett.isterm G u A) {struct P} : ptt.isterm G u A

with sane_eqctx G D (P : ett.eqctx G D) {struct P} : ptt.eqctx G D

with sane_eqsubst sbs sbt G D (P : ett.eqsubst sbs sbt G D) {struct P} : ptt.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ett.eqtype G A B) {struct P} : ptt.eqtype G A B

with sane_eqterm G u v A (P : ett.eqterm G u v A) {struct P} : ptt.eqterm G u v A.

Proof.

  (****** sane_isctx ******)
  { destruct P ; doConfig.

    (* CtxEmpty *)
    - { capply ptt.CtxEmpty. }

    (* CtxExtend *)
    - {
        intros ; capply ptt.CtxExtend.
        + now apply (ptt_sane_istype G A), sane_istype.
        + now apply sane_istype.
      }
  }

  (****** sane_issubst ******)
  { destruct P ; doConfig.

    (* SubstZero *)
    - { capply ptt.SubstZero.
        + now apply sane_isterm.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
      }

    (* SubstWeak *)
    - {
        capply ptt.SubstWeak.
        + now apply sane_istype.
        + eapply ptt_sane_istype.
          eapply sane_istype ; eassumption.
      }

    (* SubstShift. *)
    - {
        capply ptt.SubstShift.
        + now apply sane_issubst.
        + now apply sane_istype.
        + eapply (ptt_sane_issubst sbs G D).
          now apply sane_issubst.
        + eapply (ptt_sane_istype D A).
          now apply sane_istype.
      }

     (* SubstId *)
     - {
         capply ptt.SubstId.
         - now apply sane_isctx.
       }

     (* SubstComp *)
     - {
         capply (@ptt.SubstComp G D E).
         - now apply sane_issubst.
         - now apply sane_issubst.
         - apply (ptt_sane_issubst sbs G D).
           now apply sane_issubst.
         - apply (ptt_sane_issubst sbt D E).
           now apply sane_issubst.
         - apply (ptt_sane_issubst sbt D E).
           now apply sane_issubst.
       }

     (* SubstCtxConv *)
     - {
         capply (@ptt.SubstCtxConv G1 G2 D1 D2).
         - now apply sane_issubst.
         - now apply sane_eqctx.
         - now apply sane_eqctx.
         - apply (ptt_sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx D1 D2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx D1 D2).
           now apply sane_eqctx.
       }
  }

  (****** sane_istype ******)
  { destruct P.

    (* TyCtxConv *)
    { capply (@ptt.TyCtxConv G D).
      - now apply sane_istype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* TySubst *)
    { capply (@ptt.TySubst G D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
    }

    (* TyProd *)
    { capply ptt.TyProd.
      - now apply sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
    }

    (* TyId *)
    { capply ptt.TyId.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
    }

    (* TyEmpty *)
    { capply ptt.TyEmpty.
      - now apply sane_isctx.
    }

    (* TyUnit *)
    { capply ptt.TyUnit.
      - now apply sane_isctx.
    }

    (* TyBool *)
    { capply ptt.TyBool.
      - now apply sane_isctx.
    }
  }

  (****** sane_isterm ******)
  { destruct P.

    (* TermTyConv *)
    - { capply (@ptt.TermTyConv G A B).
        - now apply sane_isterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      }

    (* TermCtxConv *)
    - { capply (@ptt.TermCtxConv G D).
        - now apply sane_isterm.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
      }

    (* TermSubst *)
    - { capply (@ptt.TermSubst G D A).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* TermVarZero *)
    - { capply ptt.TermVarZero.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
      }

    (* TermVarSucc *)
    - { capply ptt.TermVarSucc.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k)A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* TermAbs *)
    - { capply ptt.TermAbs.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermApp *)
    - { capply ptt.TermApp.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermRefl *)
    - { capply ptt.TermRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermJ *)
    - { capply ptt.TermJ.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermExfalso *)
    - { capply ptt.TermExfalso.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* TermUnit *)
    - { capply ptt.TermUnit.
        - now apply sane_isctx.
      }

    (* TermTrue *)
    - { capply ptt.TermTrue.
        - now apply sane_isctx.
      }

    (* TermFalse *)
    - { capply ptt.TermFalse.
        - now apply sane_isctx.
      }

    (* TermCond *)
    - { capply ptt.TermCond.
        - now apply (@ptt_sane_isterm G u Bool), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }
  }

  (****** sane_eqctx ******)
  { destruct P.

    (* CtxRefl *)
    - { capply ptt.CtxRefl.
        - now apply sane_isctx.
      }

    (* CtxSym *)
    - { capply ptt.CtxSym.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
      }

    (* CtxTrans *)
    - { capply (@ptt.CtxTrans G D E).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx D E), sane_eqctx.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
      }

    (* EqCtxEmpty *)
    - { capply ptt.EqCtxEmpty.
      }

    (* EqCtxExtend *)
    - { capply ptt.EqCtxExtend.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply sane_eqctx.
        - now apply sane_eqtype.
      }
  }

  (****** sane_eqsubst ******)
  { destruct P.

    (* SubstRefl *)
    - { capply ptt.SubstRefl.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* SubstSym *)
    - { capply ptt.SubstSym.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }

    (* SubstTrans *)
    - { capply (@ptt.SubstTrans G D sb1 sb2 sb3).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb2 sb3 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
      }

    (* CongSubstZero *)
    - { capply (@ptt.CongSubstZero G).
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
      }

    (* CongSubstWeak *)
    - { capply ptt.CongSubstWeak.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
      }

    (* CongSubstShift *)
    - { capply ptt.CongSubstShift.
        - now apply sane_eqsubst.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
      }

    (* CongSubstComp *)
    - { capply (@ptt.CongSubstComp G D E).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
      }

    (* EqSubstCtxConv *)
    - { capply (@ptt.EqSubstCtxConv G1 G2 D1 D2).
        - now apply sane_eqsubst.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx D1 D2), sane_eqctx.
        - now apply (@ptt_sane_eqctx D1 D2), sane_eqctx.
        - now apply (@ptt_sane_eqsubst sbs sbt G1 D1), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G1 D1), sane_eqsubst.
      }

    (* CompAssoc *)
    - { capply (@ptt.CompAssoc G D E F).
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
      }

    (* WeakNat *)
    - { capply ptt.WeakNat.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* WeakZero *)
    - { capply ptt.WeakZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* ShiftZero *)
    - { capply ptt.ShiftZero.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
      }

    (* CompShift *)
    - { capply (@ptt.CompShift G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_istype E A), sane_istype.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* CompIdRight *)
    - { capply ptt.CompIdRight.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* CompIdLeft *)
    - { capply ptt.CompIdLeft.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }
  }


  (****** sane_eqtype ******)
  { destruct P.

    (* EqTyCtxConv *)
    { capply (@ptt.EqTyCtxConv G D).
      - now apply sane_eqtype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* EqTyRefl *)
    { capply ptt.EqTyRefl.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySym *)
    { capply ptt.EqTySym.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
    }

    (* EqTyTrans *)
    { capply (@ptt.EqTyTrans G A B C).
      - now apply sane_eqtype.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G B C), sane_eqtype.
    }

    (* EqTyIdSubst *)
    { capply ptt.EqTyIdSubst.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySubstComp *)
    { capply (@ptt.EqTySubstComp G D E).
      - now apply sane_istype.
      - now apply sane_issubst.
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
    }

    (* EqTySubstProd *)
    { capply (@ptt.EqTySubstProd G D).
      - now apply sane_issubst.
      - now apply (ptt_CtxExtendInversion D A),
            (ptt_sane_istype _ B), sane_istype.
      - now apply sane_istype.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstId *)
    { capply (@ptt.EqTySubstId G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_isterm D u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstEmpty *)
    { capply (@ptt.EqTySubstEmpty G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstUnit *)
    { capply (@ptt.EqTySubstUnit G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstBool *)
    { capply (@ptt.EqTySubstBool G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTyExfalso *)
    { capply (@ptt.EqTyExfalso G A B u).
      - now apply (@ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
      - now apply sane_isterm.
    }

    (* CongProd *)
    { capply ptt.CongProd.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply sane_eqtype.
      - now apply sane_eqtype.
    }

    (* CongId *)
    { capply ptt.CongId.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqterm G u1 v1 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u2 v2 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u1 v1 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u2 v2 A), sane_eqterm.
      - now apply sane_eqtype.
      - now apply sane_eqterm.
      - now apply sane_eqterm.
    }

    (* CongTySubst *)
    { capply (@ptt.CongTySubst G D).
      - now apply sane_eqsubst.
      - now apply sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
    }
  }

  (****** sane_eqterm ******)
  { destruct P.

    (* EqTyConv *)
    - { capply (@ptt.EqTyConv G A B).
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
    }

    (* EqCtxConv *)
    - { capply (@ptt.EqCtxConv G D).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqctx.
      }

    (* EqRefl *)
    - { capply ptt.EqRefl.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSym *)
    - { capply ptt.EqSym.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
      }

    (* EqTrans *)
    - { capply (@ptt.EqTrans G A u v w).
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v w A), sane_eqterm.
      }

    (* EqIdSubst *)
    - { capply ptt.EqIdSubst.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstComp *)
    - { capply (@ptt.EqSubstComp G D E A u sbs sbt).
        - now apply sane_isterm.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
        - now apply (@ptt_sane_isterm E u A), sane_isterm.
      }

    (* EqSubstWeak *)
    - { capply ptt.EqSubstWeak.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstZeroZero *)
    - { capply ptt.EqSubstZeroZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstZeroSucc *)
    - { capply ptt.EqSubstZeroSucc.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstShiftZero *)
    - { capply (@ptt.EqSubstShiftZero G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* EqSubstShiftSucc *)
    - { capply (@ptt.EqSubstShiftSucc G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D (var k) B), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstAbs *)
    - { capply (@ptt.EqSubstAbs G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_CtxExtendInversion D A),
                    (ptt_sane_isterm _ u B),
                    sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend D A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstApp *)
    - { capply (@ptt.EqSubstApp G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D v A), sane_isterm.
        - now apply (ptt_TyProdInversion D A B),
                    (ptt_sane_isterm D u _),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstRefl *)
    - { capply (@ptt.EqSubstRefl G D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* EqSubstJ *)
    - { capply (@ptt.EqSubstJ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D v A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstExfalso *)
    - { capply (@ptt.EqSubstExfalso G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstUnit *)
    - { capply (@ptt.EqSubstUnit G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* EqSubstTrue *)
    - { capply (@ptt.EqSubstTrue G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstFalse *)
    - { capply (@ptt.EqSubstFalse G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstCond *)
    - { capply (@ptt.EqSubstCond G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqTermExfalso *)
    - { capply (@ptt.EqTermExfalso G A u v w).
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* UnitEta *)
    - { capply ptt.UnitEta.
        - now apply (@ptt_sane_isterm G u Unit), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqReflection *)
    - { capply (@ptt.EqReflection G A u v w1 w2).
        - now apply (@ptt_sane_isterm G w1 (Id A u v)), sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdBeta *)
    - { capply ptt.ProdBeta.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondTrue *)
    - { capply ptt.CondTrue.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondFalse *)
    - { capply ptt.CondFalse.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdEta *)
    - { capply ptt.ProdEta.
        - now apply (@ptt_sane_isterm G u (Prod A B)), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_eqterm.
      }

    (* JRefl *)
    - { capply ptt.JRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* CongAbs *)
    - { capply ptt.CongAbs.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm (ctxextend G A1) u1 u2 A2), sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G A1) u1 u2 A2), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
      }

    (* CongApp *)
    - { capply ptt.CongApp.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 v1 (Prod A1 A2)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 v1 (Prod A1 A2)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u2 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u2 v2 A1), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongRefl *)
    - { capply ptt.CongRefl.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
      }

    (* CongJ *)
    - { capply ptt.CongJ.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype _ C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqtype _ C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 _), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 _), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (ptt_sane_eqterm G w1 w2 _), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 _), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongCond *)
    - { capply ptt.CongCond.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero Bool false))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero Bool false))), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongTermSubst *)
    - { capply (@ptt.CongTermSubst G D).
        - now apply sane_eqsubst.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }
  }

Defined.

Require Import syntax.
Require config_tactics.

Require ett ptt ptt_sanity ptt_inversion.

Module Make (ConfigReflection : tt.CONFIG_REFLECTION).

Module my_ptt_sanity := ptt_sanity.Make ConfigReflection.
Module Ptt := my_ptt_sanity.my_ptt_admissible.my_ptt_tactics.my_ptt.
(* Problem: How about the my_ptt in ptt_inversion??? *)

Module my_ptt_inversion := ptt_inversion.Make ConfigReflection.

Module Ett := ett.Make ConfigReflection.

Module my_config_tactics := config_tactics.Make (tt.HasPrecond) (ConfigReflection).
Import my_config_tactics.

(* Renaming ptt_sanity lemmata for readability. *)
Definition ptt_sane_issubst := my_ptt_sanity.sane_issubst.
Definition ptt_sane_istype  := my_ptt_sanity.sane_istype.
Definition ptt_sane_isterm  := my_ptt_sanity.sane_isterm.
Definition ptt_sane_eqctx   := my_ptt_sanity.sane_eqctx.
Definition ptt_sane_eqtype  := my_ptt_sanity.sane_eqtype.
Definition ptt_sane_eqsubst := my_ptt_sanity.sane_eqsubst.
Definition ptt_sane_eqterm  := my_ptt_sanity.sane_eqterm.

(* Same for inversion *)
Definition ptt_CtxExtendInversion := my_ptt_inversion.CtxExtendInversion.
Definition ptt_TyProdInversion    := my_ptt_inversion.TyProdInversion.
Definition ptt_TyIdInversion      := my_ptt_inversion.TyIdInversion.


Fixpoint sane_isctx G (P : Ett.isctx G) {struct P} : Ptt.isctx G

with sane_issubst sbs G D (P : Ett.issubst sbs G D) {struct P} : Ptt.issubst sbs G D

with sane_istype G A (P : Ett.istype G A) {struct P} : Ptt.istype G A

with sane_isterm G u A (P : Ett.isterm G u A) {struct P} : Ptt.isterm G u A

with sane_eqctx G D (P : Ett.eqctx G D) {struct P} : Ptt.eqctx G D

with sane_eqsubst sbs sbt G D (P : Ett.eqsubst sbs sbt G D) {struct P} : Ptt.eqsubst sbs sbt G D

with sane_eqtype G A B (P : Ett.eqtype G A B) {struct P} : Ptt.eqtype G A B

with sane_eqterm G u v A (P : Ett.eqterm G u v A) {struct P} : Ptt.eqterm G u v A.

Proof.

  (****** sane_isctx ******)
  { destruct P ; doConfig.

    (* CtxEmpty *)
    - { capply Ptt.CtxEmpty. }

    (* CtxExtend *)
    - {
        intros ; capply Ptt.CtxExtend.
        + now apply (ptt_sane_istype G A), sane_istype.
        + now apply sane_istype.
      }
  }

  (****** sane_issubst ******)
  { destruct P ; doConfig.

    (* SubstZero *)
    - { capply Ptt.SubstZero.
        + now apply sane_isterm.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
      }

    (* SubstWeak *)
    - {
        capply Ptt.SubstWeak.
        + now apply sane_istype.
        + eapply ptt_sane_istype.
          eapply sane_istype ; eassumption.
      }

    (* SubstShift. *)
    - {
        capply Ptt.SubstShift.
        + now apply sane_issubst.
        + now apply sane_istype.
        + eapply (ptt_sane_issubst sbs G D).
          now apply sane_issubst.
        + eapply (ptt_sane_istype D A).
          now apply sane_istype.
      }

     (* SubstId *)
     - {
         capply Ptt.SubstId.
         - now apply sane_isctx.
       }

     (* SubstComp *)
     - {
         capply (@Ptt.SubstComp G D E).
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
         capply (@Ptt.SubstCtxConv G1 G2 D1 D2).
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
    { capply (@Ptt.TyCtxConv G D).
      - now apply sane_istype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* TySubst *)
    { capply (@Ptt.TySubst G D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
    }

    (* TyProd *)
    { capply Ptt.TyProd.
      - now apply sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
    }

    (* TyId *)
    { capply Ptt.TyId.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
    }

    (* TyEmpty *)
    { capply Ptt.TyEmpty.
      - now apply sane_isctx.
    }

    (* TyUnit *)
    { capply Ptt.TyUnit.
      - now apply sane_isctx.
    }

    (* TyBool *)
    { capply Ptt.TyBool.
      - now apply sane_isctx.
    }
  }

  (****** sane_isterm ******)
  { destruct P.

    (* TermTyConv *)
    - { capply (@Ptt.TermTyConv G A B).
        - now apply sane_isterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      }

    (* TermCtxConv *)
    - { capply (@Ptt.TermCtxConv G D).
        - now apply sane_isterm.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
      }

    (* TermSubst *)
    - { capply (@Ptt.TermSubst G D A).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* TermVarZero *)
    - { capply Ptt.TermVarZero.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
      }

    (* TermVarSucc *)
    - { capply Ptt.TermVarSucc.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k)A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* TermAbs *)
    - { capply Ptt.TermAbs.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermApp *)
    - { capply Ptt.TermApp.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermRefl *)
    - { capply Ptt.TermRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermJ *)
    - { capply Ptt.TermJ.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermExfalso *)
    - { capply Ptt.TermExfalso.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* TermUnit *)
    - { capply Ptt.TermUnit.
        - now apply sane_isctx.
      }

    (* TermTrue *)
    - { capply Ptt.TermTrue.
        - now apply sane_isctx.
      }

    (* TermFalse *)
    - { capply Ptt.TermFalse.
        - now apply sane_isctx.
      }

    (* TermCond *)
    - { capply Ptt.TermCond.
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
    - { capply Ptt.CtxRefl.
        - now apply sane_isctx.
      }

    (* CtxSym *)
    - { capply Ptt.CtxSym.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
      }

    (* CtxTrans *)
    - { capply (@Ptt.CtxTrans G D E).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx D E), sane_eqctx.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
      }

    (* EqCtxEmpty *)
    - { capply Ptt.EqCtxEmpty.
      }

    (* EqCtxExtend *)
    - { capply Ptt.EqCtxExtend.
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
    - { capply Ptt.SubstRefl.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* SubstSym *)
    - { capply Ptt.SubstSym.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }

    (* SubstTrans *)
    - { capply (@Ptt.SubstTrans G D sb1 sb2 sb3).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb2 sb3 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
      }

    (* CongSubstZero *)
    - { capply (@Ptt.CongSubstZero G).
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
      }

    (* CongSubstWeak *)
    - { capply Ptt.CongSubstWeak.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
      }

    (* CongSubstShift *)
    - { capply Ptt.CongSubstShift.
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
    - { capply (@Ptt.CongSubstComp G D E).
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
    - { capply (@Ptt.EqSubstCtxConv G1 G2 D1 D2).
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
    - { capply (@Ptt.CompAssoc G D E F).
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
      }

    (* WeakNat *)
    - { capply Ptt.WeakNat.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* WeakZero *)
    - { capply Ptt.WeakZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* ShiftZero *)
    - { capply Ptt.ShiftZero.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
      }

    (* CompShift *)
    - { capply (@Ptt.CompShift G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_istype E A), sane_istype.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* CompIdRight *)
    - { capply Ptt.CompIdRight.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* CompIdLeft *)
    - { capply Ptt.CompIdLeft.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }
  }


  (****** sane_eqtype ******)
  { destruct P.

    (* EqTyCtxConv *)
    { capply (@Ptt.EqTyCtxConv G D).
      - now apply sane_eqtype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* EqTyRefl *)
    { capply Ptt.EqTyRefl.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySym *)
    { capply Ptt.EqTySym.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
    }

    (* EqTyTrans *)
    { capply (@Ptt.EqTyTrans G A B C).
      - now apply sane_eqtype.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G B C), sane_eqtype.
    }

    (* EqTyIdSubst *)
    { capply Ptt.EqTyIdSubst.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySubstComp *)
    { capply (@Ptt.EqTySubstComp G D E).
      - now apply sane_istype.
      - now apply sane_issubst.
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
    }

    (* EqTySubstProd *)
    { capply (@Ptt.EqTySubstProd G D).
      - now apply sane_issubst.
      - now apply (ptt_CtxExtendInversion D A),
            (ptt_sane_istype _ B), sane_istype.
      - now apply sane_istype.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstId *)
    { capply (@Ptt.EqTySubstId G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_isterm D u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstEmpty *)
    { capply (@Ptt.EqTySubstEmpty G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstUnit *)
    { capply (@Ptt.EqTySubstUnit G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstBool *)
    { capply (@Ptt.EqTySubstBool G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTyExfalso *)
    { capply (@Ptt.EqTyExfalso G A B u).
      - now apply (@ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
      - now apply sane_isterm.
    }

    (* CongProd *)
    { capply Ptt.CongProd.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply sane_eqtype.
      - now apply sane_eqtype.
    }

    (* CongId *)
    { capply Ptt.CongId.
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
    { capply (@Ptt.CongTySubst G D).
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
    - { capply (@Ptt.EqTyConv G A B).
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
    }

    (* EqCtxConv *)
    - { capply (@Ptt.EqCtxConv G D).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqctx.
      }

    (* EqRefl *)
    - { capply Ptt.EqRefl.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSym *)
    - { capply Ptt.EqSym.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
      }

    (* EqTrans *)
    - { capply (@Ptt.EqTrans G A u v w).
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v w A), sane_eqterm.
      }

    (* EqIdSubst *)
    - { capply Ptt.EqIdSubst.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstComp *)
    - { capply (@Ptt.EqSubstComp G D E A u sbs sbt).
        - now apply sane_isterm.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
        - now apply (@ptt_sane_isterm E u A), sane_isterm.
      }

    (* EqSubstWeak *)
    - { capply Ptt.EqSubstWeak.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstZeroZero *)
    - { capply Ptt.EqSubstZeroZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstZeroSucc *)
    - { capply Ptt.EqSubstZeroSucc.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstShiftZero *)
    - { capply (@Ptt.EqSubstShiftZero G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* EqSubstShiftSucc *)
    - { capply (@Ptt.EqSubstShiftSucc G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D (var k) B), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstAbs *)
    - { capply (@Ptt.EqSubstAbs G D).
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
    - { capply (@Ptt.EqSubstApp G D).
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
    - { capply (@Ptt.EqSubstRefl G D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* EqSubstJ *)
    - { capply (@Ptt.EqSubstJ G D).
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
    - { capply (@Ptt.EqSubstExfalso G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstUnit *)
    - { capply (@Ptt.EqSubstUnit G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* EqSubstTrue *)
    - { capply (@Ptt.EqSubstTrue G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstFalse *)
    - { capply (@Ptt.EqSubstFalse G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstCond *)
    - { capply (@Ptt.EqSubstCond G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqTermExfalso *)
    - { capply (@Ptt.EqTermExfalso G A u v w).
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* UnitEta *)
    - { capply Ptt.UnitEta.
        - now apply (@ptt_sane_isterm G u Unit), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqReflection *)
    - { capply (@Ptt.EqReflection G A u v w1 w2).
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
    - { capply Ptt.ProdBeta.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondTrue *)
    - { capply Ptt.CondTrue.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondFalse *)
    - { capply Ptt.CondFalse.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdEta *)
    - { capply Ptt.ProdEta.
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
    - { capply Ptt.JRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* CongAbs *)
    - { capply Ptt.CongAbs.
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
    - { capply Ptt.CongApp.
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
    - { capply Ptt.CongRefl.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
      }

    (* CongJ *)
    - { capply Ptt.CongJ.
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
    - { capply Ptt.CongCond.
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
    - { capply (@Ptt.CongTermSubst G D).
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

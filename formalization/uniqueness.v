(* Uniqueness of typing. *)

Require Import syntax.
Require ett ptt.
Require ptt2ett ett2ptt.
Require ptt_admissible.
Require ett_sanity ptt_sanity.
Require ptt_inversion.
Require Import tactics config_tactics.

(* Auxiliary inversion lemmas. *)

Fixpoint eqctx_ctxextend_left G A D
         (H : ett.eqctx (ctxextend G A) D) {struct H} :
  { G' : context &
    { A' : type &
      (D = ctxextend G' A') * ett.eqctx G G' * ett.eqtype G A A'
    }
  }%type

with eqctx_ctxextend_right D G A
                           (H : ett.eqctx D (ctxextend G A)) {struct H} :
  { G' : context &
    { A' : type &
      (D = ctxextend G' A') * ett.eqctx G G' * ett.eqtype G A A'
    }
  }%type.
Proof.
  (**** left ****)
  - { inversion_clear H ; doConfig.

      (* CtxRefl *)
      - exists G, A. repeat split.
        + capply ett.CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + capply ett.EqTyRefl.
          eapply ptt2ett.sane_istype.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.

      (* CtxSym *)
      - destruct (eqctx_ctxextend_right _ _ _ X) as [G' [A' [[eq HG] HA]]].
        exists G', A'. repeat split ; assumption.

      (* CtxTrans *)
      - destruct (eqctx_ctxextend_left _ _ _ X2) as [G' [A' [[eq HG] HA]]].
        subst.
        destruct (eqctx_ctxextend_left _ _ _ X3) as [G'' [A'' [[eq' HG'] HA']]].
        exists G'', A''. repeat split.
        + assumption.
        + ceapply ett.CtxTrans ; eassumption.
        + ceapply ett.EqTyTrans.
          * eassumption.
          * ceapply ett.EqTyCtxConv ; try eassumption.
            capply ett.CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists D0, B. repeat split ; assumption.

    }

  (**** right ****)
  - { inversion_clear H ; doConfig.

      (* CtxRefl *)
      - exists G, A. repeat split.
        + capply ett.CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + capply ett.EqTyRefl.
          eapply ptt2ett.sane_istype.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.

      (* CtxSym *)
      - destruct (eqctx_ctxextend_left _ _ _ X) as [G' [A' [[eq HG] HA]]].
        exists G', A'. repeat split ; assumption.

      (* CtxTrans *)
      - destruct (eqctx_ctxextend_right _ _ _ X3) as [G' [A' [[eq HG] HA]]].
        subst.
        destruct (eqctx_ctxextend_right _ _ _ X2) as [G'' [A'' [[eq' HG'] HA']]].
        exists G'', A''. repeat split.
        + assumption.
        + ceapply ett.CtxTrans ; eassumption.
        + ceapply ett.EqTyTrans.
          * eassumption.
          * ceapply ett.EqTyCtxConv ; try eassumption.
            capply ett.CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists G0, A0. repeat split.
        + now capply ett.CtxSym.
        + capply ett.EqTySym.
          ceapply ett.EqTyCtxConv ; eassumption.

    }

Defined.

Definition eqctx_ctxextend G A G' A'
         (H : ett.eqctx (ctxextend G A) (ctxextend G' A')) :
  (ett.eqctx G G' * ett.eqtype G A A')%type.
Proof.
  destruct (eqctx_ctxextend_left _ _ _ H) as [G'' [A'' [[eq HG] HA]]].
  inversion eq. subst.
  split ; assumption.
Defined.


(* It looks like we need to strengthen some inference
   rules, as follows: *)

Lemma substCtxConv' :
  forall G G' D sbs (E : ett.eqctx G' G),
    ett.issubst sbs G D -> ett.issubst sbs G' D.
Proof.
  intros G G' D sbs E H.
  ceapply ett.SubstCtxConv.
  - eassumption.
  - now capply ett.CtxSym.
  - capply ett.CtxRefl.
    now apply (ett_sanity.sane_issubst sbs G D).
Defined.

(* Tactics for dealing with the conversion cases. *)

Ltac doTyConv unique_term' :=
  ceapply ett.EqTyTrans ;
  [ eapply unique_term' ;
    [ ehyp
    | hyp ]
  | ceapply ett.EqTyCtxConv ;
    [ ehyp
    | hyp ] ].

Ltac doCtxConv D' unique_term' :=
  eapply unique_term' ;
  [ ehyp
  | capply (@ett.CtxTrans _ D') ; hyp ].

Ltac doSubstConv unique_subst' :=
  ceapply ett.CtxTrans ; [
    eapply unique_subst' ; [
      ehyp
    | ceapply ett.CtxTrans ; [
        ehyp
      | capply ett.CtxSym ; hyp
      ]
    ]
  | hyp
  ].

(* The version of the theorem that allows variation of the context. *)

Fixpoint unique_term_ctx G u A (H1 : ptt.isterm G u A) {struct H1}:
  forall B D,
    ptt.isterm D u B ->
    ptt.eqctx D G ->
    ett.eqtype G A B

with unique_subst G D1 sbs (H1 : ptt.issubst sbs G D1) {struct H1}:
  forall G' D2 (H2 : ptt.issubst sbs G' D2) (H3 : ptt.eqctx G G'),
    ett.eqctx D1 D2.

Proof.
  (* unique_term *)
  { destruct H1 ; doConfig ;
    simple refine (fix unique_term'' B' D' H2' H3' {struct H2'} := _) ;
    pose (
      unique_term' B' D' H1 H2 :=
        unique_term'' B' D'
                      H1
                      (ett2ptt.sane_eqctx D' _ H2)
    ) ;
    pose (
      unique_term_ctx' G u A H1 B D H2 H3 :=
        unique_term_ctx G u A
                        H1
                        B D
                        (ett2ptt.sane_isterm D u B H2)
                        (ett2ptt.sane_eqctx D G H3)
    ) ;
    pose (
      unique_subst' G D1 sbs H1 G' D2 H2 H3 :=
        unique_subst G D1 sbs
                     H1
                     G' D2
                     (ett2ptt.sane_issubst sbs G' D2 H2)
                     (ett2ptt.sane_eqctx G G' H3)
    ).

    (* H1: TermTyConv *)
    - {
        capply (@ett.EqTyTrans G _ A B').
        + capply ett.EqTySym. hyp.
        + eapply (unique_term_ctx G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - {
        ceapply ett.EqTyCtxConv.
        - eapply unique_term_ctx'.
          + ehyp.
          + ehyp.
          + capply (@ett.CtxTrans _ D).
            * hyp.
            * capply ett.CtxSym. hyp.
        - hyp.
      }

    (* TermSubst *)
    - { inversion_clear H2' ; doConfig.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - ceapply ett.CongTySubst.
          + ceapply ett.SubstRefl. ehyp.
          + eapply (unique_term_ctx' _ u).
            * hyp.
            * ehyp.
            * { capply ett.CtxSym.
                apply (@unique_subst' G _ sbs) with (G' := G).
                - hyp.
                - eapply substCtxConv'.
                  + ceapply ett.CtxSym.
                    ehyp.
                  + hyp.
                - capply ett.CtxRefl. hyp.
              }
      }

    (* TermVarZero *)
    - { inversion H2' ; doConfig.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - { assert (L : ett.eqctx (ctxextend G0 A0) (ctxextend G A)).
            - rewrite H. hyp.
            - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
              ceapply ett.CongTySubst.
              + ceapply ett.CongSubstWeak.
                capply ett.EqTySym.
                ceapply ett.EqTyCtxConv ; ehyp.
              + capply ett.EqTySym.
                ceapply ett.EqTyCtxConv ; ehyp.
          }
      }


    (* TermVarSucc *)
      - { inversion H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { assert (L : ett.eqctx (ctxextend G0 B0) (ctxextend G B)).
              - rewrite H. hyp.
              - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
                ceapply ett.CongTySubst.
                + ceapply ett.CongSubstWeak.
                  capply ett.EqTySym.
                  ceapply ett.EqTyCtxConv ; ehyp.
                + eapply (unique_term_ctx' _ (var k)).
                  * hyp.
                  * ehyp.
                  * hyp.
            }
        }

      (* TermAbs *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - capply ett.EqTyRefl.
            + capply ett.TyProd. hyp.
        }

      (* TermApp *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply ett.CongTySubst.
              - ceapply ett.CongSubstZero.
                + ceapply ett.EqTyRefl. hyp.
                + ceapply ett.EqRefl. hyp.
              - ceapply ett.EqTyRefl. hyp.
            }
        }

      (* TermRefl *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - config apply ett.EqTyRefl, ett.TyId.
            + hyp.
            + hyp.
        }

      (* TermJ *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply ett.CongTySubst.
              - ceapply ett.CongSubstZero.
                + ceapply ett.EqTyRefl.
                  capply ett.TyId ; hyp.
                + ceapply ett.EqRefl. hyp.
              - ceapply ett.CongTySubst.
                + { ceapply ett.EqSubstCtxConv.
                    - ceapply ett.CongSubstShift.
                      + ceapply ett.CongSubstZero.
                        * ceapply ett.EqTyRefl. ehyp.
                        * ceapply ett.EqRefl. hyp.
                      + ceapply ett.CongId.
                        * { ceapply ett.CongTySubst.
                            - ceapply ett.CongSubstWeak.
                              ceapply ett.EqTyRefl. hyp.
                            - ceapply ett.EqTyRefl. hyp.
                          }
                        * { ceapply ett.CongTermSubst.
                            - ceapply ett.CongSubstWeak.
                              ceapply ett.EqTyRefl. hyp.
                            - ceapply ett.EqRefl. hyp.
                          }
                        * ceapply ett.EqRefl. ceapply ett.TermVarZero. hyp.
                    - ceapply ett.EqCtxExtend.
                      + hyp.
                      + { ceapply ett.EqTyTrans.
                          - ceapply ett.EqTySubstId.
                            + ceapply ett.SubstZero. hyp.
                            + ceapply ett.TermSubst.
                              * ceapply ett.SubstWeak. hyp.
                              * hyp.
                            + ceapply ett.TermVarZero. hyp.
                          - ceapply ett.CongId.
                            + ceapply ett.EqTySym.
                              eapply ptt2ett.sane_eqtype.
                              eapply ptt_admissible.EqTyWeakZero ; hyp.
                            + eapply ptt2ett.sane_eqterm.
                              { eapply ptt_admissible.EqSubstWeakZero ; try hyp.
                                - eapply ett2ptt.sane_istype.
                                  ceapply ett.TySubst.
                                  + ceapply ett.SubstZero. hyp.
                                  + ceapply ett.TySubst.
                                    * ceapply ett.SubstWeak. hyp.
                                    * hyp.
                                - eapply ett2ptt.sane_isterm.
                                  ceapply ett.TermTyConv.
                                  + ehyp.
                                  + eapply ptt2ett.sane_eqtype.
                                    eapply ptt_admissible.EqTyWeakZero ; hyp.
                              }
                            + { ceapply ett.EqTyConv.
                                - ceapply ett.EqSubstZeroZero. hyp.
                                - eapply ptt2ett.sane_eqtype.
                                  eapply ptt_admissible.EqTyWeakZero ; hyp.
                              }
                        }
                    - ceapply ett.CtxRefl.
                      capply ett.CtxExtend.
                      capply ett.TyId.
                      + ceapply ett.TermSubst.
                        * ceapply ett.SubstWeak. hyp.
                        * hyp.
                      + ceapply ett.TermVarZero. hyp.
                  }
                + ceapply ett.EqTyRefl. hyp.
            }
        }

      (* TermExfalso *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply ett.EqTyRefl.
              ceapply ett.TyCtxConv.
              + ehyp.
              + hyp.
            }
        }

      (* TermUnit *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply ett.EqTyRefl, ett.TyUnit) ; hyp.
        }

      (* TermTrue *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply ett.EqTyRefl, ett.TyBool) ; hyp.
        }

      (* TermFalse *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply ett.EqTyRefl, ett.TyBool) ; hyp.
        }

      (* TermCond *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply ett.CongTySubst.
              - ceapply ett.CongSubstZero.
                + ceapply ett.EqTyRefl. constructor. hyp.
                + ceapply ett.EqRefl. hyp.
              - ceapply ett.EqTyRefl. hyp.
            }
        }
  }

 (* unique_subst *)
 { destruct H1 ;
   simple refine (fix unique_subst'' G' D2' H2' H3' {struct H2'} := _) ;
   pose (
     unique_subst' G' D2' H2' H3' :=
       unique_subst'' G' D2' H2'
                      (ett2ptt.sane_eqctx _ G' H3')
   ).

   (* H1: SubstZero *)
   - { inversion_clear H2'.
       - capply ett.EqCtxExtend.
         + hyp.
         + capply ett.EqTyRefl. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstWeak *)
   - { inversion H2'; doConfig.
       - rewrite <- H1 in H3'.
         destruct (eqctx_ctxextend G A G0 A).
         + hyp.
         + subst. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstShift *)
   - { inversion H2'; doConfig.
       - rewrite <- H3 in H3'.
         destruct (eqctx_ctxextend G (Subst A sbs) G0 (Subst A sbs)).
         + hyp.
         + capply ett.EqCtxExtend.
           * apply (@unique_subst G _ sbs) with (G'0 := G).
             -- hyp.
             -- pex. ceapply ett.SubstCtxConv.
                ++ ehyp.
                ++ ceapply ett.CtxSym. hyp.
                ++ capply ett.CtxRefl. hyp.
             -- pex. capply ett.CtxRefl. hyp.
           * capply ett.EqTyRefl. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstId *)
   - { inversion H2'; doConfig.
       - rewrite <- H1. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstComp *)
   - { inversion_clear H2'.
       - eapply (unique_subst _ _ _ H1_0).
         + ehyp.
         + eapply ett2ptt.sane_eqctx.
           eapply (unique_subst _ _ _ H1_).
           * ehyp.
           * hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstCtxConv *)
   - config eapply @ett.CtxTrans with (D := D1).
     + ceapply ett.CtxSym. hyp.
     + eapply unique_subst.
       * ehyp.
       * ehyp.
       * capply ett2ptt.sane_eqctx.
         (config eapply @ett.CtxTrans with (D := G2)) ; hyp.

 }

Defined.

(* The main theorem as it will probably be used. *)
Corollary unique_term {G A B u} :
  ptt.isterm G u A ->
  ptt.isterm G u B ->
  ett.eqtype G A B.

Proof.
  intros H1 H2.
  eapply unique_term_ctx.
  - eassumption.
  - eassumption.
  - apply ptt.CtxRefl. hyps.
Defined.

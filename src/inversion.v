(* Inversion lemmata that come after proving sanity. *)
(* We prove them from PTT to ETT for simplicity. *)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require ptt.
Require ptt_admissible.
Require ett.
Require ptt2ett ett2ptt.
Require ett_sanity.
Require Import tactics.

Require Import Coq.Program.Equality.

Section Inversion.

Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Context `{ConfigUniverses : config.Universes}.
Context `{ConfigWithProp : config.WithProp}.
Context `{ConfigWithJ : config.WithJ}.
Context `{ConfigEmpty : config.WithEmpty}.
Context `{ConfigUnit : config.WithUnit}.
Context `{ConfigBool : config.WithBool}.

Fixpoint TermAbsInversion {G A B u T}
         (H : ptt.isterm G (lam A B u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.istype (ctxextend G A) B *
  ett.isterm (ctxextend G A) u B *
  ett.eqtype G (Prod A B) T.
Proof.
  inversion H ; doConfig.

    (* Type conversion *)
  - { destruct (@TermAbsInversion _ _ _ _ _ X) as [[[[? ?] ?] ?] ?].
      repeat split ; try assumption.
      ceapply EqTyTrans.
      - eassumption.
      - hyp.
    }

    (* Context conversion *)
  - { destruct (@TermAbsInversion _ _ _ _ _ X) as [[[[? ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply EqCtxExtend ; try hyp.
        ceapply EqTyRefl ; assumption.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      capply TyProd ; hyp.
    }

Defined.

Fixpoint TermAppInversion {G A B u v T}
         (H : ptt.isterm G (app u A B v) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.istype (ctxextend G A) B *
  ett.isterm G u (Prod A B) *
  ett.isterm G v A *
  ett.eqtype G (Subst B (sbzero A v)) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermAppInversion _ _ _ _ _ _ X) as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermAppInversion _ _ _ _ _ _ X) as [[[[[? ?] ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply EqCtxExtend ; try hyp.
        ceapply EqTyRefl ; hyp.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst ; try hyp.
      - ceapply SubstZero ; ehyp.
      - hyp.
    }

Defined.

Fixpoint TermReflInversion {G A u T}
         (H : ptt.isterm G (refl A u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u A *
  ett.eqtype G (Id A u u) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermReflInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermReflInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TyId ; hyp.
    }

Defined.

Fixpoint TermJInversion {G A u C w v p T}
         (H : ptt.isterm G (j A u C w v p) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u A *
  ett.istype
    (ctxextend
       (ctxextend G A)
       (Id
          (Subst A (sbweak A))
          (subst u (sbweak A))
          (var 0)
       )
    )
    C *
  ett.isterm G
             w
             (Subst
                (Subst
                   C
                   (sbshift
                      (Id
                         (Subst A (sbweak A))
                         (subst u (sbweak A))
                         (var 0)
                      )
                      (sbzero A u)
                   )
                )
                (sbzero (Id A u u) (refl A u))
             ) *
  ett.isterm G v A *
  ett.isterm G p (Id A u v) *
  ett.eqtype G
             (Subst
                (Subst
                   C
                   (sbshift
                      (Id
                         (Subst A (sbweak A))
                         (subst u (sbweak A))
                         (var 0)
                      )
                      (sbzero A v)
                   )
                )
                (sbzero (Id A u v) p)
             )
             T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ X)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ X)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      assert (
          ett.eqctx
            (ctxextend (ctxextend G0 A)
                       (Id (Subst A (sbweak A))
                           (subst u (sbweak A))
                           (var 0)))
            (ctxextend (ctxextend G A)
                       (Id (Subst A (sbweak A))
                           (subst u (sbweak A))
                           (var 0)))
      ).
      { ceapply EqCtxExtend.
        - ceapply EqCtxExtend ; try hyp.
          ceapply EqTyRefl ; hyp.
        - ceapply CongId.
          + ceapply CongTySubst.
            * ceapply CongSubstWeak ; try hyp.
              ceapply EqTyRefl ; hyp.
            * ceapply EqTyRefl ; hyp.
          + ceapply CongTermSubst.
            * ceapply CongSubstWeak ; try hyp.
              ceapply EqTyRefl ; hyp.
            * ceapply EqRefl ; hyp.
          + ceapply EqRefl.
            ceapply TermVarZero. hyp.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst.
      - ceapply SubstZero. hyp.
      - ceapply TySubst.
        + ceapply SubstCtxConv.
          * { ceapply SubstShift.
              - ceapply SubstZero. ehyp.
              - ceapply TyId.
                + ceapply TermSubst.
                  * ceapply SubstWeak. hyp.
                  * hyp.
                + ceapply TermVarZero. hyp.
            }
          * { capply EqCtxExtend.
              - capply CtxRefl. hyp.
              - ceapply EqTyTrans ; [
                  ceapply EqTySubstId ; try ehyp
                | ..
                ].
                + ceapply SubstZero. hyp.
                + ceapply TermSubst.
                  * ceapply SubstWeak. hyp.
                  * hyp.
                + ceapply TermVarZero. hyp.
                + { ceapply CongId.
                    - capply EqTySym.
                      eapply ptt2ett.sane_eqtype.
                      eapply ptt_admissible.EqTyWeakZero ; hyp.
                    - eapply ptt2ett.sane_eqterm.
                      eapply ptt_admissible.EqSubstWeakZero ;
                        try hyp.
                      + eapply ett2ptt.sane_istype.
                        ceapply TySubst.
                        * ceapply SubstZero. hyp.
                        * ceapply TySubst ; try ehyp.
                          ceapply SubstWeak. hyp.
                      + eapply ett2ptt.sane_isterm.
                        ceapply TermTyConv ; try ehyp.
                        eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; hyp.
                    - ceapply EqTyConv.
                      + ceapply EqSubstZeroZero. hyp.
                      + eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; hyp.
                  }
            }
          * capply CtxRefl.
            apply ptt2ett.sane_isctx.
            apply (ptt_sanity.sane_istype _ C). hyp.
        + hyp.
    }

Defined.

Fixpoint TermExfalsoInversion {G A u T}
         (H : ptt.isterm G (exfalso A u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u Empty *
  ett.eqtype G A T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermExfalsoInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermExfalsoInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; hyp.
    }

Defined.

Fixpoint TermCondInversion {G C u v w T}
         (H : ptt.isterm G (cond C u v w) T) {struct H} :
  ett.isctx G *
  ett.isterm G u Bool *
  ett.istype (ctxextend G Bool) C *
  ett.isterm G v (Subst C (sbzero Bool true)) *
  ett.isterm G w (Subst C (sbzero Bool false)) *
  ett.eqtype G (Subst C (sbzero Bool u)) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermCondInversion _ _ _ _ _ _ X)
        as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermCondInversion _ _ _ _ _ _ X)
        as [[[[[? ?] ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 Bool) (ctxextend G Bool)).
      { capply EqCtxExtend ; try ehyp.
        capply EqTyRefl. tt_sane.
      }
      repeat split.
      - hyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst.
      - ceapply SubstZero. hyp.
      - hyp.
    }

Defined.

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
        + capply CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + capply EqTyRefl.
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
        + ceapply CtxTrans ; eassumption.
        + ceapply EqTyTrans.
          * eassumption.
          * ceapply EqTyCtxConv ; try eassumption.
            capply CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists D0, B. repeat split ; assumption.

    }

  (**** right ****)
  - { inversion_clear H ; doConfig.

      (* CtxRefl *)
      - exists G, A. repeat split.
        + capply CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + capply EqTyRefl.
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
        + ceapply CtxTrans ; eassumption.
        + ceapply EqTyTrans.
          * eassumption.
          * ceapply EqTyCtxConv ; try eassumption.
            capply CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists G0, A0. repeat split.
        + now capply CtxSym.
        + capply EqTySym.
          ceapply EqTyCtxConv ; eassumption.

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

Fixpoint eqctx_ctxempty_right {Γ} (h : ett.eqctx Γ ctxempty) {struct h} :
  Γ = ctxempty

with eqctx_ctxempty_left {Γ} (h : ett.eqctx ctxempty Γ) {struct h} :
  Γ = ctxempty.
Proof.
  (* eqctx_ctxempty_right *)
  - { dependent destruction h ; doConfig.
      - reflexivity.
      - now apply eqctx_ctxempty_left.
      - pose (eqctx_ctxempty_right D h2).
        rewrite e in h1.
        apply (eqctx_ctxempty_right G h1).
      - reflexivity.
    }

  (* eqctx_ctxempty_left *)
  - { dependent destruction h ; doConfig.
      - reflexivity.
      - now apply eqctx_ctxempty_right.
      - pose (eqctx_ctxempty_left D h1).
        rewrite e in h2.
        apply (eqctx_ctxempty_left E h2).
      - reflexivity.
    }
Defined.

Fixpoint eqctx_ctxextend_one_right
  {Γ Δ B} (h : ett.eqctx Γ (ctxextend Δ B)) {struct h} :
  { Γ' : context & { A : type & Γ = ctxextend Γ' A } }

with eqctx_ctxextend_one_left
  {Γ Δ B} (h : ett.eqctx (ctxextend Δ B) Γ) {struct h} :
  { Γ' : context & { A : type & Γ = ctxextend Γ' A } }.
Proof.
  - { dependent destruction h ; doConfig.

      - exists Δ, B. reflexivity.
      - destruct (eqctx_ctxextend_one_left D Δ B h) as [Γ' [A eq]].
        exists Γ', A. assumption.
      - destruct (eqctx_ctxextend_one_right D Δ B h2) as [Γ' [A eq]].
        rewrite eq in h1.
        destruct (eqctx_ctxextend_one_right G Γ' A h1) as [Δ' [A' eq']].
        exists Δ', A'. assumption.
      - exists G, A. reflexivity.
    }

  - { dependent destruction h ; doConfig.

      - exists Δ, B. reflexivity.
      - destruct (eqctx_ctxextend_one_right G Δ B h) as [Γ' [A eq]].
        exists Γ', A. assumption.
      - destruct (eqctx_ctxextend_one_left D Δ B h1) as [Γ' [A eq]].
        rewrite eq in h2.
        destruct (eqctx_ctxextend_one_left E Γ' A h2) as [Δ' [A' eq']].
        exists Δ', A'. assumption.
      - exists D, B0. reflexivity.
    }
Defined.

End Inversion.

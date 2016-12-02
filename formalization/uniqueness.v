(* Uniqueness of typing. *)

Require Import ett.
Require Import sanity.

Lemma eqctx_sym {G D} : eqctx G D -> eqctx D G.
Proof.
  intros [|? ? ? ?].  
  - apply EqCtxEmpty.
  - now apply EqCtxExtend, EqTySym.
Defined.

Lemma eqctx_refl G : isctx G -> eqctx G G.
Proof.
  intros [|? ? ? ?].
  - apply EqCtxEmpty.
  - now apply EqCtxExtend, EqTyRefl.
Defined.

Lemma eqctx_trans G D E :
  eqctx G D -> eqctx D E -> eqctx G E.
Proof.
  intros [|? ? ? ?].
  - intro H ; exact H.
  - intro H.
    inversion H.
    apply EqCtxExtend.
    eapply EqTyTrans.
    + eassumption.
    + assumption.
Defined.

(* We will have to add this as an inference rule. *)
Hypothesis eqctx_ctx :
  forall { G D A },
    eqctx G D ->
    eqctx (ctxextend G A) (ctxextend D A).

Hypothesis temporary :
  forall {G A B}, eqtype G A B.
  
Hypothesis temporary2 :
  forall {G D}, eqctx G D.

Fixpoint unique_term G u A (H1 : isterm G u A) {struct H1}:
  forall B D,
    isterm D u B ->
    eqctx D G ->
    eqtype G A B

with unique_subst G D1 sbs (H1 : issubst sbs G D1) {struct H1}:
  forall D2 (H2 : issubst sbs G D2),
    eqctx D1 D2.

Proof.
  (* unique_term *)
  { destruct H1 ;
    simple refine (fix unique_term' B' D' H2' H3' {struct H2'}:= _).

    (* H1: TermTyConv *)    
    - { 
        apply (@EqTyTrans G _ A B').
        + now apply EqTySym.
        + eapply (unique_term G u A).
          * assumption.
          * eassumption.
          * assumption.
      }

    (* H1: TermCtxConv *)
    - intros; now apply temporary.

    - intros; now apply temporary.

    (* H1: TermVarZero *)
    - { inversion_clear H2'.

        (* H2: TermTyConv *)
        - { 
            apply (@EqTyTrans _ _ A0).
            - eapply unique_term'.
              * eassumption.
              * assumption.
            - eapply EqTyCtxConv.
              * eassumption.
              * assumption.
          }

        (* H2: TermCtxConv *)
        - {
            eapply unique_term'.
            - eassumption.
            - now apply (eqctx_trans _ D').
          }

        (* H2: TermVarZero *)
        - intros; now apply temporary.
      }

    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
    - intros; now apply temporary.
  }

 (* unique_subst *)
 { intros;
   apply temporary2.
 }

Defined.















Proof.
  (* unique_term *)
  { destruct H1 ; try rename H1' into Foo.

    (* TermTyConv *)
    - { apply temporary.
        (* + eassumption. *)
        (* + assumption. *)
        (* +  *)
        (* eapply EqTyTrans. *)
        (* - eapply EqTySym ; eassumption. *)
        (* - now apply (unique_term G u A B). *)
      }

    (* TermCtxConv *)
    - { apply temporary.
        (* eapply EqTyCtxConv. *)
        (* + apply (unique_term G u A B). *)
        (*   * assumption. *)
        (*   * { eapply TermCtxConv. *)
        (*       - eassumption. *)
        (*       - now apply eqctx_sym. } *)
        (* + assumption. *)
      }

    (* TermSubst *)
    - { inversion_clear H2.
        
        - apply temporary.
        (* (* TermTyConv *) *)
        (* - apply (@EqTyTrans G _ A0). *)
        (*   + apply (unique_term G (subst u sbs) _). *)
        (*     * { eapply TermSubst. *)
        (*         - eassumption. *)
        (*         - assumption. } *)
        (*     * eassumption. *)
        (*   + assumption. *)

        - apply temporary.
        (* (* TermCtxConv *) *)
        (* - eapply EqTyCtxConv. *)
        (*   + eapply (unique_term _ (subst u sbs)). *)
        (*     * { eapply TermSubst. *)
        (*         - eassumption. *)
        (*         - assumption. } *)
        (*     * { eapply TermCtxConv. *)
        (*         - eassumption. *)
        (*         - assumption. } *)
        (*   + apply eqctx_refl. *)
        (*     now apply (@sane_issubst G D sbs). *)

        (* TermSubst *)
        (* We need [unique_subst] because of this rule "only". *)
        - apply temporary.
          (* apply (@CongTySubst G D _ _ sbs). *)
          (* + assumption. *)
          (* + apply (unique_term D u A). *)
          (*   * assumption. *)
          (*   * { eapply @TermCtxConv. *)
          (*       - eassumption. *)
          (*       - eapply (unique_subst _ _ _ sbs). *)
          (*         + eassumption. *)
          (*         + assumption. } *)
      }

    (* TermVarZero *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply (unique_TermTyConv _ (var 0)).
          + now apply TermVarZero.
          + eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term _ (var 0)).
            * now eapply TermVarZero.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            eapply sane_eqctx.
            eassumption.

        (* TermVarZero *)
        - apply EqTyRefl.
          eapply TySubst.
          + now apply SubstWeak.
          + assumption.
      }

    (* TermVarSucc *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ (var (S k))).
            * now apply TermVarSucc.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term _ (var (S k))).
            * now eapply TermVarSucc.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            eapply sane_eqctx.
            eassumption.

        (* TermVarSucc *)
        - eapply CongTySubst.
          eapply SubstWeak.
          + assumption.
          + now apply (unique_term _ (var k)).
      }

    (* TermAbs *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term G (lam A _ u)).
            * now eapply TermAbs.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G (lam A _ u)).
            * now apply TermAbs.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            now apply (@sane_istype G A).

        (* TermAbs *)
        - apply CongProd.
          + now apply EqTyRefl.
          + apply EqTyRefl.
            * now apply (@sane_isterm _ _ u).
      }

    (* TermApp *)
    - { inversion_clear H2.
        
        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ (app u A _ v)).
            * now apply TermApp.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G (app u A _ v)).
            * now apply TermApp.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            now apply (@sane_isterm G A v).

        (* TermApp *)
        - eapply CongTySubst.
          + now apply SubstZero.
          + now apply EqTyRefl.
      }

    (* TermRefl *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - apply (@EqTyTrans _ _ A0).
          + apply (unique_term _ (refl A u)).
            * now apply TermRefl.
            * assumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G (refl A u)).
            * now apply TermRefl.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }

          + apply eqctx_refl.
            now apply (@sane_isterm G A u).

        (* TermRefl *)
        - apply CongId.
          + now apply EqTyRefl, (@sane_isterm G A u).
          + now apply EqRefl.
          + now apply EqRefl.
      }

    (* TermExfalso *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ (exfalso A u)).
            * now apply TermExfalso.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G (exfalso A u)).
            * now apply TermExfalso.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }

          + apply eqctx_refl.
            now apply (@sane_istype G A).

        (* TermExfalso *)
        - now apply EqTyRefl.
      }

    (* TermUnit *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ unit).
            * now apply TermUnit.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G unit).
            * now apply TermUnit.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            assumption.

        (* TermUnit *)
        - now apply EqTyRefl, TyUnit.
      }

    (* TermTrue *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ true).
            * now apply TermTrue.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G true).
            * now apply TermTrue.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }

          + apply eqctx_refl.
            assumption.

        (* TermTrue *)
        - now apply EqTyRefl, TyBool.
      }

    (* TermFalse *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ false).
            * now apply TermFalse.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G false).
            * now apply TermFalse.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }

          + apply eqctx_refl.
            assumption.

        (* TermTrue *)
        - now apply EqTyRefl, TyBool.
      }

    (* TermCond *)
    - { inversion_clear H2.

        (* TermTyConv *)
        - eapply EqTyTrans.
          + eapply (unique_term _ (cond C u v w)).
            * now apply TermCond.
            * eassumption.
          + assumption.

        (* TermCtxConv *)
        - eapply EqTyCtxConv.
          + eapply (unique_term G (cond C u v w)).
            * now apply TermCond.
            * { eapply TermCtxConv.
                - eassumption.
                - assumption. }
          + apply eqctx_refl.
            now apply (@sane_isterm G Bool u).
        
        (* TermCond *)
        - eapply CongTySubst.
          + now apply SubstZero.
          + now apply EqTyRefl.        
      }
  }

  (* unique_subst *)
  { destruct H1.

    (* SubstZero *)
    { inversion_clear H2.
      apply EqCtxExtend, EqTyRefl.
      now apply (@sane_isterm G A u).
    }

    (* SubstWeak *)
    { inversion_clear H2.
      apply eqctx_refl.
      now apply (@sane_istype _ A).      
    }

    (* SubstShift *)
    { inversion_clear H2.
      apply eqctx_ctx.
      now apply (unique_subst G _ _ sbs). 
    }    
  }

Defined.
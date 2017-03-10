Require config.
Require Import config_tactics.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ett_sanity.
Require pxtt eitt.
Require ctt.
Require Import eval.
Require Import hml.

Ltac ssplit name :=
  simple refine (existT _ _ _) ; [
    ..
  | match goal with
    | |- _ ?T =>
      pose (name := T) ; replace T with name by reflexivity
    end
  ].

Section Translation.

Axiom cheating : forall A : Type, A.
Ltac todo := apply cheating.

Structure is_ctx_translation G G' : Type := {
  is_ctx_hml : hml_context G G' ;
  is_ctx_der : eitt.isctx (eval_ctx G')
}.

Structure is_type_translation G' A : Type := {
  is_type_ctx : context ;
  is_type_typ' : ctt.type' ;
  is_type_coe : coerce.context_coercion ;
  is_type_isctxcoe : coerce.isctxcoe is_type_coe is_type_ctx (eval_ctx G') ;
  is_type_typ := ctt.Coerce is_type_coe is_type_typ' ;
  is_type_eval := eval_type is_type_typ ;
  is_type_hml : hml_type A is_type_typ ;
  is_type_der : eitt.istype (eval_ctx G') is_type_eval
}.

Arguments is_type_ctx {_ _} _.
Arguments is_type_typ' {_ _} _.
Arguments is_type_coe {_ _} _.
Arguments is_type_isctxcoe {_ _} _.
Arguments is_type_typ {_ _} _.
Arguments is_type_eval {_ _} _.
Arguments is_type_hml {_ _} _.
Arguments is_type_der {_ _} _.

Structure is_term_translation G' A' u u' : Type := {
  is_term_hml : hml_term u u' ;
  is_term_der : eitt.isterm (eval_ctx G') (eval_term u') (eval_type A')
}.

Definition translation_coherence A G' (T' : is_type_translation G' A) :=
  forall (G'' : ctt.context) (crc : coerce.context_coercion),
    coerce.isctxcoe crc (eval_ctx G') (eval_ctx G'') ->
    forall (T'' : is_type_translation G'' A),
    { crt : coerce.type_coercion (coerce.act_type crc (is_type_eval T')) (is_type_eval T'') &
            coerce.istypecoe crt (coerce.act_type crc (is_type_eval T')) (is_type_eval T'') }.

Fixpoint translate_isctx {G} (D : pxtt.isctx G) {struct D} :
  { G' : ctt.context & is_ctx_translation G G' }

with translate_istype {G A} (D : pxtt.istype G A) {struct D} :
  forall G', is_ctx_translation G G' ->
  { T : is_type_translation G' A & translation_coherence A G' T}

with translate_isterm {G A u} (D : pxtt.isterm G u A) {struct D} :
  forall G', is_ctx_translation G G' ->
  forall (T' : is_type_translation G' A),
  { u' : ctt.term & is_term_translation G' (is_type_typ T') u u' }
.

Proof.
  (* translate_isctx *)
  - { destruct D ; doConfig.

      (* CtxEmpty *)
      - { exists ctt.ctxempty.
          split.
          - constructor.
          - capply CtxEmpty.
        }

      (* CtxExtend *)
      - { destruct (translate_isctx G i) as [G'' TGG''].
          destruct (translate_istype G A i0 G'' TGG'') as [T coh].
          exists (ctt.ctxextend G'' (is_type_typ T)).
          destruct TGG'', T.
          split.
          - now constructor.
          - now capply CtxExtend.
        }
  }

  (* translate_istype *)
  - { destruct D ; doConfig.

      (* TyCtxConv *)
      - { (* Need: translate_eqctx *)
          todo.
        }

      (* TySubst *)
      - { (* Need: translate_issubst *)
          todo.
        }

      (* TyProd *)
      - { intros G' TGG'.
          pose (TGG'_hml := is_ctx_hml _ _ TGG').
          destruct (translate_istype G A i G' TGG') as [TA cohA].
          pose (A' := is_type_typ TA).
          assert (TGAG'A' : is_ctx_translation (ctxextend G A) (ctt.ctxextend G' A')).
          { split.
            - apply hml_ctxextend.
              + assumption.
              + apply (is_type_hml TA).
            - capply CtxExtend.
              apply (is_type_der TA).
          }
          destruct (translate_istype (ctxextend G A) B D (ctt.ctxextend G' A') TGAG'A') as [TB cohB].
          pose (B' := is_type_typ TB).

          ssplit T.
          - refine {| is_type_ctx := eval_ctx G';
                      is_type_typ' := ctt.Prod A' B';
                      is_type_coe := coerce.ctx_id
                   |}.
            + constructor. apply TGG'.
            + constructor. constructor.
              * apply (is_type_hml TA).
              * apply (is_type_hml TB).
            + simpl. capply TyProd.
              apply (is_type_der TB).
          - unfold translation_coherence.
            intros G'' crc Isctxcoe_crc T''.
            ssplit crt.
            + todo.
            + todo.
        }

      (* TyId *)
      - { intros G' TGG'.
          destruct (translate_istype G A i0 G' TGG') as [TA cohA].
          (* destruct (translate_isterm G A u i1 G' TGG' A' i3) as [u' [ ?]]. *)
          (* destruct (translate_isterm G A v i2 G' TGG' A' i3) as [v' [? ?]]. *)
          (* destruct i3. destruct TGG'. *)
          (* exists (ctt.Id A' u' v') ; split. *)
          (* + split. *)
          (*   * now apply hml_Id. *)
          (*   * now apply TyId. *)
          (* + todo. *)
          todo.
        }

      (* TyEmpty *)
      - { intros G' TGG'.

          ssplit T.
          - refine {| is_type_ctx  := eval_ctx G' ;
                      is_type_typ' := ctt.Empty ;
                      is_type_coe  := coerce.ctx_id
                   |}.
            + constructor. apply TGG'.
            + constructor. constructor.
            + simpl. capply TyEmpty.
              apply TGG'.
          - unfold translation_coherence.
            intros G'' crc Hcrc T'.

            (* We need to 'discover' that we want a coercion between Empty
               and itself. *)
            replace (is_type_eval T) with Empty by reflexivity.
            pose (hml := is_type_hml T').
            inversion hml. inversion H1. subst. clear hml. clear H1.
            assert (eqT' : eitt.eqtype (eval_ctx G'') (is_type_eval T') Empty).
            { unfold is_type_eval. unfold is_type_typ.
              rewrite <- H2. simpl.
              eapply coerceEmpty.
              apply T'.
            }
            assert (
              eqT : eitt.eqtype (eval_ctx G'') (coerce.act_type crc Empty) Empty
            ).
            { eapply coerceEmpty. eassumption. }

            ssplit crt.
            + apply coerce.type_id.
            + eapply coerce.istype_id.
              ceapply EqTyTrans.
              * eapply eqT.
              * ceapply EqTySym. eapply eqT'.
        }

      (* TyUnit *)
      - { intros G' TGG'.

          ssplit T.
          - refine {| is_type_ctx  := eval_ctx G' ;
                      is_type_typ' := ctt.Unit ;
                      is_type_coe  := coerce.ctx_id
                   |}.
            + constructor. apply TGG'.
            + constructor. constructor.
            + simpl. capply TyUnit.
              apply TGG'.
          - unfold translation_coherence.
            intros G'' crc Hcrc T'.

            replace (is_type_eval T) with Unit by reflexivity.
            pose (hml := is_type_hml T').
            inversion hml. inversion H1. subst. clear hml. clear H1.
            assert (eqT' : eitt.eqtype (eval_ctx G'') (is_type_eval T') Unit).
            { unfold is_type_eval. unfold is_type_typ.
              rewrite <- H2. simpl.
              eapply coerceUnit.
              apply T'.
            }
            assert (
              eqT : eitt.eqtype (eval_ctx G'') (coerce.act_type crc Unit) Unit
            ).
            { eapply coerceUnit. eassumption. }

            ssplit crt.
            + apply coerce.type_id.
            + eapply coerce.istype_id.
              ceapply EqTyTrans.
              * eapply eqT.
              * ceapply EqTySym. eapply eqT'.
        }

      (* TyBool *)
      - { intros G' TGG'.

          ssplit T.
          - refine {| is_type_ctx  := eval_ctx G' ;
                      is_type_typ' := ctt.Bool ;
                      is_type_coe  := coerce.ctx_id
                   |}.
            + constructor. apply TGG'.
            + constructor. constructor.
            + simpl. capply TyBool.
              apply TGG'.
          - unfold translation_coherence.
            intros G'' crc Hcrc T'.

            replace (is_type_eval T) with Bool by reflexivity.
            pose (hml := is_type_hml T').
            inversion hml. inversion H1. subst. clear hml. clear H1.
            assert (eqT' : eitt.eqtype (eval_ctx G'') (is_type_eval T') Bool).
            { unfold is_type_eval. unfold is_type_typ.
              rewrite <- H2. simpl.
              eapply coerceBool.
              apply T'.
            }
            assert (
              eqT : eitt.eqtype (eval_ctx G'') (coerce.act_type crc Bool) Bool
            ).
            { eapply coerceBool. eassumption. }

            ssplit crt.
            + apply coerce.type_id.
            + eapply coerce.istype_id.
              ceapply EqTyTrans.
              * eapply eqT.
              * ceapply EqTySym. eapply eqT'.
        }
    }

  (* translate_isterm *)
  - { destruct D ; doConfig.

      (* TermTyConv *)
      - { (* Need: translate_eqtype *)
          todo.
        }

      (* TermCtxConv *)
      - { (* Need: translate_eqctx *)
          todo.
        }

      (* TermSubst *)
      - { (* Need: translate_issubst *)
          todo.
        }

      (* TermVarZero *)
      - { intros GA' [HGAGA' ?] Aw' TAwAw'.
          (* This is not var 0 in the genral case! *)
          inversion HGAGA'. subst. rename H1 into HGG'. rename H3 into HAA'.
          (* We need to have a coercion between A'[w] and Aw'. *)
          todo.
        }

      (* TermVarSucc *)
      - { intros GB' [HGB D'] Aw' [HAw D''].

          inversion HGB. subst. rename H1 into HG. rename H3 into HB.
          rename A' into B'.

          inversion HAw.

          - subst. rename H1 into HA. rename H3 into Hw.

            inversion Hw. subst. rename A'0 into B''. rename H0 into HB'.
            + (* We still have a coherence problem as we have two translations
                 of B. *)
              todo.
            + todo.

          - todo.
        }

      (* TermAbs *)
      - { intros G' [HG D'] PiAB [HPiAB D''].

          inversion HPiAB.
          (* All those keep branching, that was, one of the reasons, we were
             always having a coercion, may it be the identity. *)
          (* I'm fine with keeping things as they are but we probably should
             have a lemma not to deal with so many cases and only consider
             the coerced case? *)
          - subst. rename H1 into HA. rename H3 into HB.
            todo.
          - todo.
        }

      (* TermApp *)
      - { (* Coherence problem *)
          todo.
        }

      (* TermRefl *)
      - { intros G' TGG' IdAuu' [HIdA' ?].
          inversion HIdA'.
          - subst. todo.
          - todo.


          (* destruct (translate_isterm G A u D G' TGG'). *)
          (* exists G'. exists (ctt.Id A' u' u'). exists (ctt.refl A' u'). *)
          (* repeat split. *)
          (* - assumption. *)
          (* - (* Problem of homology *) *)
          (*   todo. *)
          (* - (* Problem of homology *) *)
          (*   todo. *)
          (* - now capply TermRefl. *)
        }

      (* TermJ *)
      - { (* Likely coherence and homology issues *)
          todo.
        }

      (* TermExfalso *)
      - { (* Coherence problem *)
          todo.
        }

      (* TermUnit *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Unit. exists ctt.unit.
          repeat split.
          - assumption.
          - (* Homology issue *)
            todo.
          - (* Homology issue *)
            todo.
          - now capply TermUnit.
        }

      (* TermTrue *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Bool. exists ctt.true.
          repeat split.
          - assumption.
          - (* Homology issue *)
            todo.
          - (* Homology issue *)
            todo.
          - now capply TermTrue.
        }

      (* TermFalse *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Bool. exists ctt.false.
          repeat split.
          - assumption.
          - (* Homology issue *)
            todo.
          - (* Homology issue *)
            todo.
          - now capply TermFalse.
        }

      (* TermCond *)
      - { (* Coherence problem *)
          todo.
        }
    }

Defined.

End Translation.

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

Structure ctx_translation G : Type := {
  is_ctx_ctx : ctt.context ;
  is_ctx_hml : hml_context G is_ctx_ctx ;
  is_ctx_der : eitt.isctx (eval_ctx is_ctx_ctx)
}.

Arguments is_ctx_ctx {_} _.
Arguments is_ctx_hml {_} _.
Arguments is_ctx_der {_} _.

(* TODO: Take TG instead of G' (the other context will then become useless?) *)
Structure type_translation G' A : Type := {
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

(* We probably have to add the fact that G'' is a translation to
   complete the translation. *)
Definition translation_coherence A G' (T' : type_translation G' A) :=
  forall (G'' : ctt.context) (crc : coerce.context_coercion),
    coerce.isctxcoe crc (eval_ctx G') (eval_ctx G'') ->
    forall (T'' : type_translation G'' A),
    { crt : coerce.type_coercion (coerce.act_type crc (is_type_eval T')) (is_type_eval T'') &
            coerce.istypecoe crt (coerce.act_type crc (is_type_eval T')) (is_type_eval T'') }.

(* First, let's prove some inversions *)
Lemma TransProdInv :
  forall {G' A B} (TP : type_translation G' (Prod A B)),
    { TA : type_translation G' A
    & type_translation (ctt.ctxextend G' (is_type_typ TA)) B }.
Proof.
  intros G' A B TP.

  destruct TP as [G P' crc hcrc P eP hml der].
  inversion hml. inversion H1.
  subst. rename A'0 into A', H4 into hmlA, H6 into hmlB.
  destruct A' as [cA A'].
  destruct B' as [cB B'].

  ssplit TA.
  - refine {| is_type_ctx  := G ;
              is_type_typ' := A' ;
              is_type_coe  := crc |}.
    + assumption.
    + constructor. now inversion hmlA.
    + replace eP with (eval_type P) in der by reflexivity.
      replace P
      with (ctt.Coerce crc
                       (ctt.Prod (ctt.Coerce cA A') (ctt.Coerce cB B')))
      in der by reflexivity.
      simpl in der.
      (* We need to know the coercion goes through! *)
      (* Then we need to apply inversion on der. *)
      todo.
  - (* refine {| is_type_ctx  := ctxextend G A ; *)
    (*           is_type_typ' := B' ; *)
    (*           is_type_coe  := ? |}. *)
    (* We need to be able to extend a context coercion! *)
    todo.
Defined.






(* Now, proceed with the translation *)

Fixpoint translate_isctx {G} (D : pxtt.isctx G) {struct D} :
  ctx_translation G

with translate_istype {G A} (D : pxtt.istype G A) {struct D} :
  forall (TG : ctx_translation G),
  { T : type_translation (is_ctx_ctx TG) A
  & translation_coherence A (is_ctx_ctx TG) T }

with translate_isterm {G A u} (D : pxtt.isterm G u A) {struct D} :
  forall (TG : ctx_translation G),
  forall (TA : type_translation (is_ctx_ctx TG) A),
  { u' : ctt.term & is_term_translation (is_ctx_ctx TG) (is_type_typ TA) u u' }
.

Proof.
  (* translate_isctx *)
  - { destruct D ; doConfig.

      (* CtxEmpty *)
      - { exists ctt.ctxempty.
          - constructor.
          - capply CtxEmpty.
        }

      (* CtxExtend *)
      - { pose (TG := translate_isctx G i).
          destruct (translate_istype G A i0 TG) as [TA cohA].
          (* We should have a constructor to extend a translation by another *)
          destruct TG as [G' ?].
          destruct TA as [? A' cA ?].
          exists (ctt.ctxextend G' (ctt.Coerce cA A')).
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
      - { intros TG.

          pose (hmlG := is_ctx_hml TG).
          destruct (translate_istype G A i TG) as [TA cohA].
          pose (G' := is_ctx_ctx TG).
          pose (A' := is_type_typ TA).
          (* This should be transparent! *)
          assert (TGA : ctx_translation (ctxextend G A)).
          { exists (ctt.ctxextend G' A').
            - constructor.
              + assumption.
              + apply (is_type_hml TA).
            - capply CtxExtend.
              apply (is_type_der TA).
          }
          destruct (translate_istype (ctxextend G A) B D TGA) as [TB cohB].
          pose (B' := is_type_typ TB).

          ssplit T.
          - refine {| is_type_ctx  := eval_ctx G' ;
                      is_type_typ' := ctt.Prod A' B' ;
                      is_type_coe  := coerce.ctx_id
                   |}.
            + constructor. apply TG.
            + constructor. constructor.
              * apply (is_type_hml TA).
              * apply (is_type_hml TB).
            + simpl. capply TyProd.
              apply (is_type_der TB).
          - unfold translation_coherence.
            intros G'' crc Hcrc T''.

            (* Maybe some lemma that does the following? *)
            (* Let's find out that we have a product in T''. *)
            pose (hml := is_type_hml T'').
            inversion hml. inversion H1. subst. clear hml. clear H1.
            rename A'1 into A'', B'0 into B''.
            destruct A'' as [cA'' A''].

            (* Let's build coercions between As and Bs *)
            assert (TA' : type_translation G'' A).
            { refine {| is_type_ctx  := is_type_ctx T'' ;
                        is_type_typ' := A'' ;
                        is_type_coe  := cA''
                     |}.
              - todo.
              - assumption.
              - todo.
            }
            destruct (cohA G'' crc Hcrc TA') as [crtA iscrtA].

            assert (TGA'' :
              ctx_translation (ctxextend G A)
                                 (ctt.ctxextend G'' (ctt.Coerce cA'' A''))
            ).
            { split.
              - constructor.
                + (* Are we missing information? *)
                  todo.
                + assumption.
              - (* Probably follows from some inversion, again... *)
                todo.
            }

            destruct B'' as [cB'' B''].
            assert (TB' :
              type_translation (ctt.ctxextend G'' (ctt.Coerce cA'' A''))
                                  B
            ).
            { refine {| is_type_ctx  := ctxextend (is_type_ctx T'') A ;
                        is_type_typ' := B'' ;
                        is_type_coe  := cB'' |}.
              - todo.
              - assumption.
              - todo.
            }
            (* We need to extend crc by cA''? Or something else? *)
            (* destruct (cohB (ctt.ctxextend G'' (ctt.Coerce cA'' A'')) *)
            (*                ()) *)

            (* Into what does it 'reduce'? *)
            (* assert (eqT'' : eitt.eqtype (eval_ctx G'') (is_type_eval T'') (Prod )) *)

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

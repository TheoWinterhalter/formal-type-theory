Require config.
Require Import config_tactics.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ett_sanity.
Require pxtt eitt.
Require ctt.
Require Import eval.
Require Import hml.

Section Translation.

Axiom cheating : forall A : Type, A.
Ltac todo := apply cheating.

Fixpoint translate_isctx {G} (D : pxtt.isctx G) {struct D} :
  { G' : ctt.context & hml_context G G' * eitt.isctx (eval_ctx G') }%type

with translate_istype {G A} (D : pxtt.istype G A) {struct D} :
  forall G', hml_context G G' -> eitt.isctx (eval_ctx G') ->
  { A' : ctt.type &
    hml_type A A' *
    eitt.istype (eval_ctx G') (eval_type A')
  }%type

with translate_isterm {G A u} (D : pxtt.isterm G u A) {struct D} :
  forall G', hml_context G G' -> eitt.isctx (eval_ctx G') ->
  forall A', hml_type A A' -> eitt.istype (eval_ctx G') (eval_type A') ->
  { u' : ctt.term &
    hml_term u u' *
    eitt.isterm (eval_ctx G') (eval_term u') (eval_type A')
  }%type
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
      - { destruct (translate_isctx G i) as [G'' [? ?]].
          destruct (translate_istype G A i0 G'' h i1) as [A'' [? ?]].
          exists (ctt.ctxextend G'' A'').
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
      - { intros G' HGG' D'.
          destruct (translate_istype G A i G' HGG' D') as [A' [? ?]].
          assert (K : eitt.isctx (ctxextend (eval_ctx G') (eval_type A'))).
          - now capply CtxExtend.
          - assert (L : hml.hml_context (ctxextend G A) (ctt.ctxextend G' A')).
            + now apply hml_ctxextend.
            + destruct (translate_istype (ctxextend G A) B D (ctt.ctxextend G' A') L K) as [B' [? ?]].
              exists (ctt.Prod A' B') ; split.
              * now apply hml_Prod.
              * now apply TyProd.
        }

      (* TyId *)
      - { intros G' HGG' D'.
          destruct (translate_istype G A i0 G' HGG' D') as [A' [? ?]].
          destruct (translate_isterm G A u i1 G' HGG' D' A' h i3) as [u' [? ?]].
          destruct (translate_isterm G A v i2 G' HGG' D' A' h i3) as [v' [? ?]].
          exists (ctt.Id A' u' v') ; split.
          + now apply hml_Id.
          + now apply TyId.
        }

      (* TyEmpty *)
      - { intros G' ? ?.
          exists ctt.Empty ; split.
          - constructor.
          - now apply TyEmpty.
        }

      (* TyUnit *)
      - { intros G' ? ?.
          exists ctt.Unit ; split.
          - constructor.
          - now apply TyUnit.
        }

      (* TyBool *)
      - { intros G' ? ?.
          exists ctt.Bool ; split.
          - constructor.
          - now apply TyBool.
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
      - { intros G' HGG' D' A' HAA' D''.
          exists (ctt.var 0) ; split.
          - constructor.
          - inversion HGG'.
            inversion HAA'.
            + todo.
            + todo.
        }

      (* TermVarSucc *)
      - { destruct (translate_isterm _ _ _ D) as [G' [A' [vk' [[[? ?] ?] ?]]]].
          (* Coherence problem here, if we translate B, we get another G'. *)
          todo.
        }

      (* TermAbs *)
      - { (* Coherence problem *)
          todo.
        }

      (* TermApp *)
      - { (* Coherence problem *)
          todo.
        }

      (* TermRefl *)
      - { destruct (translate_isterm G A u D) as [G' [A' [u' [[[? ?] ?] ?]]]].
          exists G'. exists (ctt.Id A' u' u'). exists (ctt.refl A' u').
          repeat split.
          - assumption.
          - (* Problem of homology *)
            todo.
          - (* Problem of homology *)
            todo.
          - now capply TermRefl.
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

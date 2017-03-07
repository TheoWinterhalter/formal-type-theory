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
  { G' : ctt.context &
  { A' : ctt.type &
    hml_context G G' *
    hml_type A A' *
    eitt.istype (eval_ctx G') (eval_type A')
  } }%type

with translate_isterm {G A u} (D : pxtt.isterm G u A) {struct D} :
  { G' : ctt.context &
  { A' : ctt.type &
  { u' : ctt.term &
    hml_context G G' *
    hml_type A A' *
    hml_term u u' *
    eitt.isterm (eval_ctx G') (eval_term u') (eval_type A')
  } } }%type
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
      - { destruct (translate_istype G A i0) as [G' [A' [[? ?] ?]]].
          exists (ctt.ctxextend G' A').
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
      - { destruct (translate_istype _ _ D) as [GA' [B' [[? ?] ?]]].
          (* No way to get A' from it, and if we translate istype G A,
             we won't be able to relate ctxextend G' A' and GA'. *)
          todo.
        }

      (* TyId *)
      - { (* Same problem of coherence between the different translations of
             A. *)
          todo.
        }

      (* TyEmpty *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Empty.
          repeat split.
          - assumption.
          - (* This is the reason we had a strict notion of coercion that
               needed to always be here. In that case, I cannot relate
               Empty and itself because there is no coercion involved.
             *)
            todo.
          - now capply TyEmpty.
        }

      (* TyUnit *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Unit.
          repeat split.
          - assumption.
          - (* Same here *)
            todo.
          - now capply TyUnit.
        }

      (* TyBool *)
      - { destruct (translate_isctx G i) as [G' [? ?]].
          exists G'. exists ctt.Bool.
          repeat split.
          - assumption.
          - (* Same here *)
            todo.
          - now capply TyBool.
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
      - { destruct (translate_istype G A i0) as [G' [A' [[? ?] ?]]].
          exists (ctt.ctxextend G' A'). exists (ctt.Subst A' (ctt.sbweak A')).
          exists (ctt.var 0).
          repeat split.
          - now constructor.
          - (* Same problem here, homology is ill-defined with respect to
               current definition of ctt. *)
            todo.
          - (* Again. *)
            todo.
          - now capply TermVarZero.
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

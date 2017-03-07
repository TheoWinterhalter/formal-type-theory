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
  - {
      destruct D.
      
      (* CtxEmpty *)
      - { exists ctt.ctxempty.
          split.
          + constructor.
          + apply CtxEmpty.
        }

      (* CtxExtend *)
      - { todo. }
  }

  (* translate_istype *)
  - {
   todo.
  }

  (* translate_isterm *)
  - {
   todo.
  }

Defined.  

End Translation.

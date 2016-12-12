(* Translating CTT to ITT *)
Require ctt.
Require itt.

Module C := ctt.
Module I := itt.

Definition todo : False.
Admitted.

Fixpoint eval_ctx (G : C.context) : I.context

with eval_substitution' (sbs : C.substitution') : I.substitution

with eval_substitution (sbs : C.substitution) : I.substitution

with eval_type' (A : C.type') : I.type

with eval_type (A : C.type) : I.type

with eval_term' (t : C.term') : I.term

with eval_term (t : C.term) : I.term.

Proof.

  (****** eval_ctx ******)
  - destruct G.

    (* ctxempty *)
    + exact I.ctxempty.

    (* ctxextend *)
    + simple refine (I.ctxextend _ _).
      * now apply eval_ctx.
      * now apply eval_type.

  (****** Eval_substitution' ******)
  - destruct sbs.

    (* sbzero *)
    + simple refine (I.sbzero _ _ _).
      * now apply eval_ctx.
      * now apply eval_type.
      * now apply eval_term.

    (* sbweak *)
    + simple refine (I.sbweak _ _).
      * now apply eval_ctx.
      * now apply eval_type.

    + destruct todo.

    + destruct todo.

    + destruct todo.

  (****** eval_substitution ******)
  - destruct todo.

  (****** eval_type' ******)
  - destruct todo.

  (****** eval_type ******)
  - destruct todo.

  (****** eval_term' ******)
  - destruct todo.

  (****** eval_term ******)
  - destruct todo.

Defined.
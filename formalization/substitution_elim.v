Require Import syntax.
Require ett ptt.

Hypothesis subst_free_term : term -> Prop.

Hypothesis temporary : forall {A}, A.
Ltac todo := exact temporary.

Fixpoint elim_term u :
  { v : term &
    subst_free_term v *
    (forall G A, ptt.isterm G u A -> ett.eqterm G u v A)
  }%type.

Proof.
  destruct u.

  (* var *)
  - exists (var n).
    todo.

  (* lam *)
  - (* destruct (elim_term ) *)
    (* We need to have elim_type as well *)
    todo.

  (* app *)
  - todo.

  (* refl *)
  - todo.

  (* j *)
  - todo.

  (* subst *)
  - (* What would we do here? Go though another destruction of u?
       When does it end? *)
    todo.

  (* exfalso *)
  - todo.

  (* unit *)
  - exists unit. todo.

  (* true *)
  - exists true. todo.

  (* false *)
  - exists false. todo.

  (* cond *)
  - todo.

Defined.

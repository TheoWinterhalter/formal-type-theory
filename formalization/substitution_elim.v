Require Import syntax.
Require ett ptt.

Inductive subst_free_term : term -> Type :=
  | subst_free_var : forall n, subst_free_term (var n)

  | subst_free_lam :
      forall A B u,
        subst_free_type A ->
        subst_free_type B ->
        subst_free_term u ->
        subst_free_term (lam A B u)

  | subst_free_app :
      forall u A B v,
        subst_free_term u ->
        subst_free_type A ->
        subst_free_type B ->
        subst_free_term v ->
        subst_free_term (app u A B v)
(*
  | subst_free_refl : type -> term -> term
  | subst_free_j : type -> term -> type -> term -> term -> term -> term
  (* NB: subst is not subst free! *)
  | subst_free_exfalso : type -> term -> term
  | subst_free_unit : term
  | subst_free_true : term
  | subst_free_false : term
  | subst_free_cond : type -> term -> term -> term -> term
*)
with subst_free_type : type -> Type :=
(*   | subst_free_Prod : type -> type -> type
     | subst_free_Id : type -> term -> term -> type
     | subst_free_Subst : type -> substitution -> type
     | subst_free_Empty : type
     | subst_free_Unit : type
*)
     | subst_free_Bool : subst_free_type Bool.

Hypothesis temporary : forall {A}, A.
Ltac todo := exact temporary.

Fixpoint elim_term u :
  { v : term &
    subst_free_term v *
    (forall G A, ptt.isterm G u A -> ett.eqterm G u v A)
  }%type

with elim_type A :
  { B : type &
    subst_free_type B *
    (forall G, ptt.istype G A -> ett.eqtype G A B) }%type.

Proof.
  (* elim_term *)
  - {
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
  }

  (* elim_type *)
  - { todo. }

Defined.

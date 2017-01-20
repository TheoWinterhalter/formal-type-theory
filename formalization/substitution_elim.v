Require Import syntax.
Require ett ptt.
Require Import ptt_inversion.
Require ptt_sanity.
Require Import tactics.

Inductive subst_free_term : term -> Type :=
  | subst_free_var :
      forall n,
        subst_free_term (var n)

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

  | subst_free_refl :
      forall A u,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term (refl A u)

  | subst_free_j :
      forall A u C w v p,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_type C ->
        subst_free_term w ->
        subst_free_term v ->
        subst_free_term p ->
        subst_free_term (j A u C w v p)

  (* NB: subst is not subst free! *)

  | subst_free_exfalso :
      forall A u,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term (exfalso A u)

  | subst_free_unit :
      subst_free_term unit

  | subst_free_true :
      subst_free_term true

  | subst_free_false :
      subst_free_term false

  | subst_free_cond :
      forall A u v w,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term v ->
        subst_free_term w ->
        subst_free_term (cond A u v w)

with subst_free_type : type -> Type :=

  | subst_free_Prod :
      forall A B,
        subst_free_type A ->
        subst_free_type B ->
        subst_free_type (Prod A B)

  | subst_free_Id :
      forall A u v,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term v ->
        subst_free_type (Id A u v)

  (* NB: Subst is not subst free! *)

  | subst_free_Empty :
      subst_free_type Empty

  | subst_free_Unit :
      subst_free_type Unit

  | subst_free_Bool :
      subst_free_type Bool
.

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
    (forall G, ptt.istype G A -> ett.eqtype G A B)
  }%type.

Proof.
  (* elim_term *)
  - { destruct u.

      (* var *)
      - exists (var n). split.
        + constructor.
        + intros G A H.
          apply ett.EqRefl.
          hyp.

      (* lam *)
      - { destruct (elim_type t) as [A [sA fA]].
          destruct (elim_type t0) as [B [sB fB]].
          destruct (elim_term u) as [v [sv fv]].
          exists (lam A B v). split.
          - now constructor.
          - intros G T h.
            destruct (ptt_sanity.sane_isterm G (lam t t0 u) T h).
            eapply ett.EqTyConv.
            + eapply ett.CongAbs.
              * apply fA. todo. (* We need another inversion lemma. *)
              * apply fB. todo.
              * apply fv. todo.
            + todo. (* Also part of the inversion lemma. *)
        }

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

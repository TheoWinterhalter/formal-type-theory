Require Import syntax.
Require Import ett.
Require ptt.
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

(* When dealing with substitutions we need to shift them when they go through
   types and terms, and this requires information about contexts.
 *)
Fixpoint elim_term {G A u} (H : ptt.isterm G u A) {struct H} :
  { v : term & subst_free_term v * eqterm G u v A }%type

with elim_type {G A} (H : ptt.istype G A) {struct H} :
  { B : type & subst_free_type B * eqtype G A B }%type.
Proof.
  (* elim_term *)
  - { destruct H.

      (* TermTyConv *)
      - { destruct (elim_term _ _ _ H) as [v [sv ev]].
          exists v.  split.
          - assumption.
          - eapply EqTyConv ; ehyp.
        }

      (* TermCtxConv *)
      - { destruct (elim_term _ _ _ H) as [v [sv ev]].
          exists v.  split.
          - assumption.
          - eapply EqCtxConv ; ehyp.
        }

      (* TermSubst *)
      - { (* Here we need to 'apply' the substitution. *)
          todo.
        }

      (* TermVarZero *)
      - { exists (var 0). split.
          - now constructor.
          - apply EqRefl. apply TermVarZero. hyp.
        }

      (* TermVarSucc *)
      - { exists (var (S k)). split.
          - now constructor.
          - apply EqRefl. apply TermVarSucc ; hyp.
        }

      (* TermAbs *)
      - { destruct (elim_type _ _ i0) as [A' [sA eA]].
          destruct (elim_type _ _ i1) as [B' [sB eB]].
          destruct (elim_term _ _ _ H) as [u' [su eu]].
          exists (lam A' B' u'). split.
          - now constructor.
          - eapply CongAbs ; hyp.
        }

      (* TermApp *)
      - { destruct (elim_term _ _ _ H) as [u' [su eu]].
          destruct (elim_type _ _ i0) as [A' [sA eA]].
          destruct (elim_type _ _ i1) as [B' [sB eB]].
          destruct (elim_term _ _ _ H0) as [v' [sv ev]].
          exists (app u' A' B' v'). split.
          - now constructor.
          - eapply CongApp ; hyp.
        }

      (* TermRefl *)
      - { destruct (elim_type _ _ i0) as [A' [sA eA]].
          destruct (elim_term _ _ _ H) as [u' [su eu]].
          exists (refl A' u'). split.
          - now constructor.
          - eapply CongRefl ; hyp.
        }

      (* TermJ *)
      - { destruct (elim_type _ _ i0) as [A' [sA eA]].
          destruct (elim_term _ _ _ H) as [u' [su eu]].
          destruct (elim_type _ _ i1) as [C' [sC eC]].
          destruct (elim_term _ _ _ H0) as [w' [sw ew]].
          destruct (elim_term _ _ _ H1) as [v' [sv ev]].
          destruct (elim_term _ _ _ H2) as [p' [sp ep]].
          exists (j A' u' C' w' v' p'). split.
          - now constructor.
          - eapply CongJ ; hyp.
        }

      (* TermExfalso *)
      - { destruct (elim_type _ _ i0) as [A' [sA eA]].
          destruct (elim_term _ _ _ H) as [u' [su eu]].
          exists (exfalso A' u'). split.
          - now constructor.
          - eapply EqTermExfalso.
            + eapply TermExfalso ; hyp.
            + eapply TermTyConv.
              * eapply TermExfalso ; ett_sane.
              * now apply EqTySym.
            + ehyp.
        }

      (* TermUnit *)
      - { exists unit. split.
          - now constructor.
          - apply EqRefl. apply TermUnit. hyp.
        }

      (* TermTrue *)
      - { exists true. split.
          - now constructor.
          - apply EqRefl. apply TermTrue. hyp.
        }

      (* TermTrue *)
      - { exists false. split.
          - now constructor.
          - apply EqRefl. apply TermFalse. hyp.
        }

      (* TermCond *)
      - { destruct (elim_type _ _ i0) as [C' [sC eC]].
          destruct (elim_term _ _ _ H) as [u' [su eu]].
          destruct (elim_term _ _ _ H0) as [v' [sv ev]].
          destruct (elim_term _ _ _ H1) as [w' [sw ew]].
          exists (cond C' u' v' w'). split.
          - now constructor.
          - apply CongCond ; hyp.
        }

    }

  (* elim_type *)
  - { destruct H.

      (* TyCtxConv *)
      - { destruct (elim_type _ _ H) as [A' [sA eA]].
          exists A'. split.
          - assumption.
          - eapply EqTyCtxConv ; ehyp.
        }

      (* TySubst *)
      - { todo. (* Same here we need to apply. *) }

      (* TyProd *)
      - { destruct (elim_type _ _ H0) as [A' [sA eA]].
          destruct (elim_type _ _ H) as [B' [sB eB]].
          exists (Prod A' B'). split.
          - now constructor.
          - eapply CongProd ; hyp.
        }

      (* TyId *)
      - { destruct (elim_type _ _ H) as [A' [sA eA]].
          destruct (elim_term _ _ _ i0) as [u' [su eu]].
          destruct (elim_term _ _ _ i1) as [v' [sv ev]].
          exists (Id A' u' v'). split.
          - now constructor.
          - eapply CongId ; hyp.
        }

      (* TyEmpty *)
      - { exists Empty. split.
          - now constructor.
          - apply EqTyRefl. apply TyEmpty. hyp.
        }

      (* TyUnit *)
      - { exists Unit. split.
          - now constructor.
          - apply EqTyRefl. apply TyUnit. hyp.
        }

      (* TyBool *)
      - { exists Bool. split.
          - now constructor.
          - apply EqTyRefl. apply TyBool. hyp.
        }

    }

Defined.

Require config.
Require Import config_tactics.

Local Open Scope type_scope.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ett_sanity.
Require pxtt.

Axiom cheating : forall (A : Type), A.
Ltac todo := apply cheating.

Definition Family (G : Set) := G -> Set.

Definition section {G : Set} (A : Family G) :=
  forall x, A x.

Definition Pi {G} (A : Family G) (B : Family (sigT A)) :=
  fun xs => forall (x : A xs), B (existT _ xs x).

Inductive istran_ctx : context -> Set -> Type :=
  | istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit
  | istran_ctx_ctxextend :
      forall G G' A A',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_ctx (ctxextend G A) (sigT A')

with istran_type :
  (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=
 | istran_type_Empty :
     forall G G', istran_type G G' Empty (fun _ => Empty_set)
 | istran_type_Unit :
     forall G G', istran_type G G' Unit (fun _ => Datatypes.unit)
 | istran_type_Prod :
     forall G G' A A' B B',
       istran_type G G' A A' ->
       istran_type (ctxextend G A) (sigT A') B B' ->
       istran_type G G' (Prod A B) (Pi A' B')

 | istran_type_todo :
     forall (G : context) (G' : Set) (A : type) (A' : Family G'),
       istran_type G G' A A'.

Fixpoint eval_ctx G (Der : pxtt.isctx G) {struct Der} :
  { G' : Set & istran_ctx G G' }

with eval_subst {G D G' sbs} (Der : pxtt.issubst sbs G D) {struct Der} :
     istran_ctx G G' ->
     { D' : Set
     & istran_ctx D D'
     * (Family D' -> Family G') }

with eval_ty {G G' A} (Der : pxtt.istype G A) {struct Der} :
   istran_ctx G G' ->
   { A' : Family G' & istran_type G G' A A' }

with eval_term {G G' A A' u} (Der : pxtt.isterm G u A) {struct Der} :
    istran_ctx G G' ->
    istran_type G G' A A' ->
    section A'

with eval_eqctx_lr {G G' D} (Der : pxtt.eqctx G D) {struct Der} :
    istran_ctx G G' ->
    { D' : Set & istran_ctx D D' * (D' = G') }

with eval_eqctx_rl {G D D'} (Der : pxtt.eqctx G D) {struct Der} :
    istran_ctx D D' ->
    { G' : Set & istran_ctx G G' * (G' = D') }.


Proof.
  (* eval_ctx *)
  - {
      destruct Der ; doConfig.

      (* CtxEmpty *)
      - exists Datatypes.unit.
        constructor.

      (* CtxExtend *)
      - { destruct (eval_ctx G i) as [G' ist_GG'].
          destruct (eval_ty G G' A i0 ist_GG') as [A' ist_AA'].
          exists (sigT A').
          now constructor.
        }
    }

  (* eval_subst *)
  - { destruct Der ; doConfig.

      (* SubstZero *)
      - { todo. }

      (* SubstWeak *)
      - { todo. }

      (* SubstShift *)
      - { todo. }

      (* SubstId *)
      - { todo. }

      (* SubstComp *)
      - { todo. }

      (* SubstCtxConv *)
      - { todo. }
  }

  (* eval_ty *)
  - { destruct Der ; doConfig.

      (* TyCtxConv *)
      - { intros ist_DG'.
          rename G' into D'.
          destruct (eval_eqctx_rl G D D' e ist_DG') as [G' [ist_GG' eq_G'D']].
          destruct eq_G'D'.
          destruct (eval_ty G G' A Der ist_GG') as [A' ist_AA'].
          exists A'.
          constructor.
        }

      (* TySubst *)
      - { intros ist_GG'.
          destruct (eval_subst G D G' sbs i ist_GG') as [D' [ist_DD' sbs']].
          destruct (eval_ty D D' A Der ist_DD') as [A' ist_AA'].
          pose (A'' := sbs' A').
          exists A''.
          constructor.
        }

      (* TyProd *)
      - { intros ist_GG'.
          destruct (eval_ty G G' A i ist_GG') as [A' ist_AA'].
          pose (G'A' := sigT A').
          destruct (eval_ty (ctxextend G A) G'A' B Der) as [B' ist_BB'].
          { now constructor. }
          exists (Pi A' B').
          now constructor.
        }

      (* TyId *)
      - { intros ist_GG'.
          destruct (eval_ty G G' A i0 ist_GG') as [A' ist_AA'].
          pose (u' := eval_term G G' A A' u i1 ist_GG' ist_AA').
          pose (v' := eval_term G G' A A' v i2 ist_GG' ist_AA').
          exists (fun xs => u' xs = v' xs).
          now constructor.
        }

      (* TyEmpty *)
      - { intros _.
          exists (fun _ => Datatypes.Empty_set).
          now constructor.
        }

      (* TyUnit *)
      - { intros _.
          exists (fun _ => Datatypes.unit).
          now constructor.
        }

      (* TyBool *)
      - { intros _.
          exists (fun _ => Datatypes.bool).
          now constructor.
        }
    }

    (* eval_term *)
    - { todo. }

    (* eval_eqctx_lr *)
    - { todo. }

    (* eval_eqctx_rl *)
    - { todo. }
Defined.

Lemma empty_to_empty :
  let Der := (TyEmpty CtxEmpty : pxtt.istype ctxempty Empty) in
  let ist_GG' := istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit in
  forall xs, projT1 (eval_ty Der ist_GG') xs = Empty_set.
Proof.
  reflexivity.
Qed.

Lemma consistency : forall u, pxtt.isterm ctxempty u Empty -> Empty_set.
Proof.
  intros u Der.
  pose (ist_GG' := istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit).
  pose (tr := eval_ty (TyEmpty CtxEmpty) ist_GG').
  pose (u' := eval_term Der ist_GG' (projT2 tr)).
  pose (p := u' tt). apply p.
Qed.

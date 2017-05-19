(* We attempt a formalisation that goes from reflection for dSet to
   definitional UIP dSet.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

Require Import Coq.Program.Equality.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.
  Context `{isdset : config.DSetCriterion}.
  Local Instance hasDSetReflection : config.DSetReflection
    := {| config.dsetreflectionFlag := config.Yes ;
         config.dsetreflectionCriterion := config.dsetcriterion |}.
  Local Instance hasDSetUIP : config.DSetUIP
    := {| config.dsetuipFlag := config.No ;
         config.dsetuipCriterion G A := config.ko |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.No |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.
  Context `{isdset : config.DSetCriterion}.
  Local Instance hasDSetReflection : config.DSetReflection
    := {| config.dsetreflectionFlag := config.No ;
         config.dsetreflectionCriterion G A := config.ko |}.
  Local Instance hasDSetUIP : config.DSetUIP
    := {| config.dsetuipFlag := config.No ;
         config.dsetuipCriterion := config.dsetcriterion |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Ttt.

End Ttt.

Section Translation.

Open Scope type_scope.

Context `{isdset : config.DSetCriterion}.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

(* We explain beforhand what it means to be a translation *)
(* Inductive istran_ctx : context -> context -> Type := *)
(* | istran_ctxempty : *)
(*     istran_ctx ctxempty ctxempty *)

(* | istran_ctxextend : *)
(*     forall Γ A Γᵗ Aᵗ, *)
(*       istran_ctx Γ Γᵗ -> *)
(*       (* istran_type Γ A Γᵗ Aᵗ -> *) *)
(*       istran_ctx (ctxextend Γ A) (ctxextend Γᵗ Aᵗ). *)

Definition istran_ctx : context -> context -> Type :=
  fun Γ Γᵗ => Ttt.isctx Γᵗ.

Fixpoint trans_isctx {Γ} (H : Stt.isctx Γ) {struct H} :
  { Γᵗ : context & istran_ctx Γ Γᵗ }.

Proof.
  (**** trans_ctx ****)
  - { dependent destruction H.

      (* CtxEmpty *)
      - { exists ctxempty. capply CtxEmpty. }

      (* CtxExtend *)
      - admit.
    }
Qed.

End Translation.

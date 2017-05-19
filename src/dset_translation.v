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

(* The main idea is that we translate types as types with holes for the
   dSets inhabitants together with the inhabitants that fill them.
   This way, two translations of the same type only diverge in what fills the
   holes.
   Terms are translated in a similar way.
   However, the definitional equalities are translated into propositional
   equalities between the Σ-types inhabitants that are produced.

   Note: The main idea is that being a dSet is a syntactic criterion,
   which allows us to place the holes without fail and thus make sure
   the rest of the strucuture doesn't have reflection, while eveything
   filling the holes verifies some definitional UIP in the target.

   This probably means that beside istran_*, the trans_* theorem is also
   wrongly stated.
   Question: Do we need to internalise Σ-types in order to do that? Or is there
   hope we can actually have the telescopes on the meta-level.
   This would also allow us to avoid all sorts of proofs of equality to
w  write (and type check!) about them.
 *)

Record contextᵗ (Γ : context) := mkctxᵗ {
  context : context ;
  isctx   : Ttt.isctx context
}.

Arguments context {_} _.
Arguments isctx {_} _.

Record substitutionᵗ
  {Γ} (Γᵗ : contextᵗ Γ) {Δ} (Δᵗ : contextᵗ Δ) (σ : substitution) := mksubstᵗ {
  substitution : substitution ;
  issubst      : Ttt.issubst substitution (context Γᵗ) (context Δᵗ)
}.

Arguments substitution {_ _ _ _ _} _.
Arguments issubst {_ _ _ _ _} _.

Record typeᵗ {Γ} (Γᵗ : contextᵗ Γ) (A : type) := mktypeᵗ {
  type   : type ;
  istype : Ttt.istype (context Γᵗ) type
}.

Arguments type {_ _ _} _.
Arguments istype {_ _ _} _.

Record termᵗ {Γ} {Γᵗ : contextᵗ Γ} {A} (Aᵗ : typeᵗ Γᵗ A) (u : term) := mktermᵗ {
  term   : term ;
  isterm : Ttt.isterm (context Γᵗ) term (type Aᵗ)
}.

Arguments term {_ _ _ _ _} _.
Arguments isterm {_ _ _ _ _} _.

(* Note this is still not ok, we want to have telescopes and also
   constraints on the translation itself, like homology to the original
   perhaps. *)

Fixpoint trans_isctx {Γ} (H : Stt.isctx Γ) {struct H} :
  contextᵗ Γ

with trans_issubst {Γ Δ σ} (H : Stt.issubst σ Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
    substitutionᵗ Γᵗ Δᵗ σ
  } }

with trans_istype {Γ A} (H : Stt.istype Γ A) {struct H} :
  { Γᵗ : contextᵗ Γ & typeᵗ Γᵗ A }

with trans_term {Γ A u} (H : Stt.isterm Γ u A) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
    termᵗ Aᵗ u
  } }
.
Proof.
  (**** trans_isctx ****)
  - { dependent destruction H ; doConfig.

      (* CtxEmpty *)
      - { exists ctxempty. capply CtxEmpty. }

      (* CtxExtend *)
      - { (* pose (Gᵗ := trans_isctx _ i). *)
          destruct (trans_istype _ _ i0) as [Gᵗ Aᵗ].
          unshelve (eapply mkctxᵗ).
          - exact (ctxextend (context Gᵗ) (type Aᵗ)).
          - capply CtxExtend. apply (istype Aᵗ).
        }
    }

  (**** trans_issubst ****)
  - { dependent destruction H ; doConfig.

      (* SubstZero *)
      - admit.

      (* SubstWeak *)
      - admit.

      (* SubstShift *)
      - admit.

      (* SubstId *)
      - admit.

      (* SubstComp *)
      - admit.

      (* SubstCtxConv *)
      - admit.
    }

  (**** trans_istype ****)
  - { dependent destruction H ; doConfig.

      (* TyCtxConv *)
      - admit.

      (* TySubst *)
      - admit.

      (* TyProd *)
      - admit.

      (* TyId *)
      - admit.
    }

  (**** trans_isterm ****)
  - { dependent destruction H ; doConfig.

      (* TermTyConv *)
      - admit.

      (* TermCtxConv *)
      - admit.

      (* TermSubst *)
      - admit.

      (* TermVarZero *)
      - admit.

      (* TermVarSucc *)
      - admit.

      (* TermAbs *)
      - admit.

      (* TermApp *)
      - admit.

      (* TermRefl *)
      - admit.
    }
Qed.

End Translation.

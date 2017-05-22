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
   write (and type check!) about them.
 *)

(* Let's experiment with those telescopes. *)
Inductive telescope :=
| simple_term (u : term) : telescope
| hole_term (n : term) (D : type) (f : term -> telescope) : telescope.

Check (hole_term true Bool (fun x => simple_term (refl Bool x))).

Fixpoint telescope_equality
  (Γ : context) (t1 t2 : telescope) (A : type) : Type :=
  match t1, t2 with
  | simple_term u1, simple_term u2 =>
    { p : term & Ttt.isterm Γ p (Id A u1 u2) }
  | hole_term d1 D1 f1, hole_term d2 D2 f2 =>
    Ttt.eqtype Γ D1 D2 *
    { p : term &
      Ttt.isterm Γ p (Id D1 d1 d2) *
      telescope_equality Γ (f1 d1) (f2 d1) A
    }
  | _, _ => False
  end.

Record contextᵗ (Γ : context) := mkctxᵗ {
  context : context ;
  isctx   : Ttt.isctx context
}.

Arguments context {_} _.
Arguments isctx {_} _.
Coercion context : contextᵗ >-> syntax.context.

Record substitutionᵗ
  {Γ} (Γᵗ : contextᵗ Γ) {Δ} (Δᵗ : contextᵗ Δ) (σ : substitution) := mksubstᵗ {
  substitution : substitution ;
  issubst      : Ttt.issubst substitution Γᵗ Δᵗ
}.

Arguments substitution {_ _ _ _ _} _.
Arguments issubst {_ _ _ _ _} _.
Coercion substitution : substitutionᵗ >-> syntax.substitution.

Record typeᵗ {Γ} (Γᵗ : contextᵗ Γ) (A : type) := mktypeᵗ {
  type   : type ;
  istype : Ttt.istype Γᵗ type
}.

Arguments type {_ _ _} _.
Arguments istype {_ _ _} _.
Coercion type : typeᵗ >-> syntax.type.

Record termᵗ {Γ} {Γᵗ : contextᵗ Γ} {A} (Aᵗ : typeᵗ Γᵗ A) (u : term) := mktermᵗ {
  term   : term ;
  isterm : Ttt.isterm Γᵗ term Aᵗ
}.

Arguments term {_ _ _ _ _} _.
Arguments isterm {_ _ _ _ _} _.
Coercion term : termᵗ >-> syntax.term.

Record eqctxᵗ {Γ} (Γᵗ : contextᵗ Γ) {Δ} (Δᵗ : contextᵗ Δ) := {
  (* TODO *)
}.

Record eqsubstᵗ
  {Γ} {Γᵗ : contextᵗ Γ} {Δ} {Δᵗ : contextᵗ Δ}
  {σ} (σᵗ : substitutionᵗ Γᵗ Δᵗ σ)
  {ρ} (ρᵗ : substitutionᵗ Γᵗ Δᵗ ρ)
  := {
  (* TODO *)
}.

Record eqtypeᵗ
  {Γ} {Γᵗ : contextᵗ Γ}
  {A} (Aᵗ : typeᵗ Γᵗ A)
  {B} (Bᵗ : typeᵗ Γᵗ B)
  := {
  (* TODO *)
}.

Record eqtermᵗ
  {Γ} {Γᵗ : contextᵗ Γ}
  {A} {Aᵗ : typeᵗ Γᵗ A}
  {u} (uᵗ : termᵗ Aᵗ u)
  {v} (vᵗ : termᵗ Aᵗ v)
  := {
  (* TODO *)
}.

(* Note this is still not ok, we want to have telescopes and also
   constraints on the translation itself, like homology to the original
   perhaps. *)

(* One essential lemma that we want to have on translations is that
   two translations of the same term that live at the same type are
   definitionally equal. This relies on the definitional UIP present
   in the target type theory.

   We cannot prove it in the current state, but this should be around to
   guide the definition of termᵗ and typeᵗ.
*)
Lemma termᵗ_coh :
  forall {Γ} {Γᵗ : contextᵗ Γ}
    {A} {Aᵗ : typeᵗ Γᵗ A}
    {u} (uᵗ uᵗ' : termᵗ Aᵗ u),
    Ttt.eqterm Γᵗ uᵗ uᵗ' Aᵗ.
Admitted.

Fixpoint trans_isctx {Γ} (H : Stt.isctx Γ) {struct H} :
  contextᵗ Γ

with trans_issubst {Γ Δ σ} (H : Stt.issubst σ Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
    substitutionᵗ Γᵗ Δᵗ σ
  } }

with trans_istype {Γ A} (H : Stt.istype Γ A) {struct H} :
  { Γᵗ : contextᵗ Γ &
    typeᵗ Γᵗ A
  }

with trans_isterm {Γ A u} (H : Stt.isterm Γ u A) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
    termᵗ Aᵗ u
  } }

with trans_eqctx {Γ Δ} (H : Stt.eqctx Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
    eqctxᵗ Γᵗ Δᵗ
  } }

with trans_eqsubst {Γ Δ σ ρ} (H : Stt.eqsubst σ ρ Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
  { σᵗ : substitutionᵗ Γᵗ Δᵗ σ &
  { ρᵗ : substitutionᵗ Γᵗ Δᵗ ρ &
    eqsubstᵗ σᵗ ρᵗ
  } } } }

with trans_eqtype {Γ A B} (H : Stt.eqtype Γ A B) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
  { Bᵗ : typeᵗ Γᵗ B &
    eqtypeᵗ Aᵗ Bᵗ
  } } }

with trans_eqterm {Γ A u v} (H : Stt.eqterm Γ u v A) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
  { uᵗ : termᵗ Aᵗ u &
  { vᵗ : termᵗ Aᵗ v &
    eqtermᵗ uᵗ vᵗ
  } } } }
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
          - exact (ctxextend Gᵗ Aᵗ).
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

  (**** trans_eqctx ****)
  - { dependent destruction H ; doConfig.

      (* CtxRefl *)
      - admit.

      (* CtxSym *)
      - admit.

      (* CtxTrans *)
      - admit.

      (* EqCtxEmpty *)
      - admit.

      (* EqCtxExtend *)
      - admit.
    }

  (**** trans_eqsubst ****)
  - { dependent destruction H ; doConfig.

      (* SubstRefl *)
      - admit.

      (* SubstSym *)
      - admit.

      (* SubstTrans *)
      - admit.

      (* CongSubstZero *)
      - admit.

      (* CongSubstWeak *)
      - admit.

      (* CongSubstShift *)
      - admit.

      (* CongSubstComp *)
      - admit.

      (* EqSubstCtxConv *)
      - admit.

      (* CompAssoc *)
      - admit.

      (* WeakNat *)
      - admit.

      (* WeakZero *)
      - admit.

      (* ShiftZero *)
      - admit.

      (* CompShift *)
      - admit.

      (* CompIdRight *)
      - admit.

      (* CompIdLeft *)
      - admit.
    }

  (**** trans_eqtype ****)
  - { dependent destruction H ; doConfig.

      (* EqTyCtxConv *)
      - admit.

      (* EqTyRefl *)
      - admit.

      (* EqTySym *)
      - admit.

      (* EqTyTrans *)
      - admit.

      (* EqTyIdSubst *)
      - admit.

      (* EqTySubstComp *)
      - admit.

      (* EqTySubstProd *)
      - admit.

      (* EqTySubstId *)
      - admit.

      (* CongProd *)
      - admit.

      (* CongId *)
      - admit.

      (* CongTySubst *)
      - admit.
    }

  (**** trans_eqterm ****)
  - { dependent destruction H ; doConfig.

      (* EqTyConv *)
      - admit.

      (* EqCtxConv *)
      - admit.

      (* EqRefl *)
      - admit.

      (* EqSym *)
      - admit.

      (* EqTrans *)
      - admit.

      (* EqIdSubst *)
      - admit.

      (* EqSubstComp *)
      - admit.

      (* EqSubstWeak *)
      - admit.

      (* EqSubstZeroZero *)
      - admit.

      (* EqSubstZeroSucc *)
      - admit.

      (* EqSubstShiftZero *)
      - admit.

      (* EqSubstShiftSucc *)
      - admit.

      (* EqSubstAbs *)
      - admit.

      (* EqSubstApp *)
      - admit.

      (* EqSubstRefl *)
      - admit.

      (* DSetReflection *)
      - { destruct (trans_isterm _ _ _ i3) as [Gᵗ [Eqᵗ pᵗ]].
          exists Gᵗ.
          (* Now we'd like some inversion on Eqᵗ to get some Aᵗ, uᵗ and vᵗ. *)
          (* I was hoping this case would help me see how to build the ᵗ
             types... *)
          (* In a way, the Aᵗ, uᵗ and vᵗ we would get would be what would
             fill the only hole for each. *)
          admit.
        }

      (* ProdBeta *)
      - admit.

      (* CongAbs *)
      - admit.

      (* CongApp *)
      - admit.

      (* CongRefl *)
      - admit.

      (* CongTermSubst *)
      - admit.
    }
Qed.

End Translation.

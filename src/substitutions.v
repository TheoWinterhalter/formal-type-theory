(* Handling meta-level substitutions. *)

Require Import Classes.CRelationClasses.

Require config.
Require Import config_tactics.
Require Import tt.
Require Import syntax.

(* Tactics to apply rules of substitutions *)

Ltac rewrite_Subst_action :=
  first [
    rewrite SubstProd
  | rewrite SubstId
  | rewrite SubstEmpty
  | rewrite SubstUnit
  | rewrite SubstBool
  | rewrite SubstBinaryProd
  | rewrite SubstUni
  | rewrite SubstEl
  | rewrite sbidtype
  ].

Ltac rewrite_subst_action :=
  first [
    rewrite substLam
  | rewrite substApp
  | rewrite substRefl
  | rewrite substJ
  | rewrite substExfalso
  | rewrite substUnit
  | rewrite substTrue
  | rewrite substFalse
  | rewrite substCond
  | rewrite substPair
  | rewrite substProjOne
  | rewrite substProjTwo
  | rewrite substUniProd
  | rewrite substUniId
  | rewrite substUniEmpty
  | rewrite substUniUnit
  | rewrite substUniBool
  | rewrite substUniBinaryProd
  | rewrite substUniUni
  | rewrite sbidterm
  ].

Ltac rewrite_subst_var :=
  first [
    rewrite sbconszero
  | rewrite sbconssucc
  | rewrite sbweakvar
  | rewrite sbdropvar
  ].

Ltac rewrite_subst :=
  first [
    rewrite_Subst_action
  | rewrite_subst_action
  | rewrite_subst_var
  ].

Ltac rewrite_substs :=
  repeat rewrite_subst.

Section Substitutions.

  Open Scope type_scope.

Context `{configPrecondition : config.Precondition}.
(* Local Instance havePrecondition : config.Precondition := *)
(*   {| config.flagPrecondition := config.Yes |}. *)
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBoolType : config.BoolType}.
Context `{configProdType : config.ProdType}.
Context `{configSyntax : syntax.Syntax}.

(* A substitution is well-formed if it is well-formed on variables.
   The action on types and terms is derived from it.
 *)
Inductive issubst : forall (σ : substitution) (Γ : context), context -> Type :=
| SubstNil :
    forall {σ Γ},
      isctx Γ ->
      issubst σ Γ ctxempty

| SubstCons :
    forall {σ Γ Δ A},
      isctx Γ ->
      isctx Δ ->
      istype Δ A ->
      issubst (σ↑) Γ Δ ->
      isterm Γ (var 0)[σ] A[σ↑] ->
      issubst σ Γ (ctxextend Δ A)

| SubstCtxConv :
    forall {σ Γ Δ Δ'},
      eqctx Δ' Δ ->
      issubst σ Γ Δ ->
      issubst σ Γ Δ'
.

Class SubstitutionProperties := {
  SubstId   : forall {Γ}, isctx Γ -> issubst sbid Γ Γ;
  SubstWeak : forall {Γ A}, isctx Γ -> istype Γ A -> issubst sbweak (Γ,A) Γ;
  issubst_ext :
    forall {Γ Δ},
      isctx Γ ->
      isctx Δ ->
      forall {σ ρ},
        σ ~ ρ ->
        issubst σ Γ Δ ->
        issubst ρ Γ Δ
}.

Context {substProp : SubstitutionProperties}.

Lemma SubstTypeExt :
  config.flagPrecondition ->
  forall {Δ A},
    istype Δ A ->
    forall {σ ρ},
      σ ~ ρ ->
      A[σ] = A[ρ].
Proof.
  intros fp Δ A hA.
  config induction hA ; intros σ ρ h.
  - now apply IHhA.
  - rewrite_substs. f_equal.
    + now apply H.
    + apply IHhA. intros [|n].
      * now rewrite_substs.
      * rewrite_substs. apply h.
  - rewrite_substs. f_equal.
    + now apply H.
    + (* Need to be mutual with terms. *)
Admitted.

Axiom cheating : forall {A}, A.
Tactic Notation "cheat" := (exact cheating).

Fixpoint TySubst {Γ Δ σ A} (hσ : issubst σ Γ Δ) (hA : istype Δ A)
  (hΓ : config.flagPrecondition -> isctx Γ) {struct hA} :
  istype Γ A[σ]

with TermSubst {Γ Δ σ u A} (hσ : issubst σ Γ Δ) (hu : isterm Δ u A)
  (hΓ : config.flagPrecondition -> isctx Γ) {struct hu} :
  isterm Γ u[σ] A[σ]

with CongTySubst {Γ Δ σ A B} (hσ : issubst σ Γ Δ) (h : eqtype Δ A B)
  (hΓ : config.flagPrecondition -> isctx Γ) {struct h} :
  eqtype Γ A[σ] B[σ]
.
Proof.
  (* TySubst *)
  - cheat.

  (* TermSubst *)
  - { config destruct hu.

      (* TermTyConv *)
      - config apply @TermTyConv with (A := A[σ]).
        + config apply TermSubst with (Δ := G) ; assumption.
        + config apply CongTySubst with (Δ := G) ; assumption.
        + assumption.
        + (config apply TySubst with (Δ := G)) ; assumption.
        + (config apply TySubst with (Δ := G)) ; assumption.

      (* TermCtxConv *)
      - { config apply TermSubst with (Δ := G).
          - eapply SubstCtxConv ; eassumption.
          - assumption.
          - assumption.
        }

      (* TermVarZero *)
      - { inversion hσ.
          - exfalso. eapply ctxextend_notempty. symmetry. eassumption.
          - destruct (ctxextend_inj H2) as [e1 e2]. subst. clear H2.
            cheat. (* A[σ ↑] = A[sbweak][σ] but it seems annoying to show. *)
          - subst.
            cheat. (* Maybe induction on hσ instead? *)
        }

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.

      - cheat.
    }

  (* CongTySubst *)
  - cheat.
Defined.

End Substitutions.

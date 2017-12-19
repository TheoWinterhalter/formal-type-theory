(* Handling meta-level substitutions. *)

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

Context `{configPrecondition : config.Precondition}.
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

(* First we need to define the notion of well-formed substitution. *)
Inductive issubst : substitution -> context -> context -> Type :=
| SubstEmpty :
    forall {σ Γ},
      isctx Γ ->
      issubst σ Γ ctxempty

| SubstCons :
    forall {σ u Γ Δ A},
      istype Δ A ->
      issubst σ Γ Δ ->
      isterm Γ u A[σ] ->
      issubst (u ⋅ σ) Γ (ctxextend Δ A)

| SubstId :
    forall {Γ},
      isctx Γ ->
      issubst sbid Γ Γ

| SubstWeak :
    forall {Γ A},
      istype Γ A ->
      issubst sbweak (ctxextend Γ A) Γ
.

(* We show applying substitutions preserves typing. *)
Lemma TySubst :
  forall {Δ A},
    istype Δ A ->
    forall {Γ σ},
      issubst σ Γ Δ ->
      istype Γ A[σ].
Proof.
  intros Δ A hA.
  induction hA ; intros Γ σ hσ.

  (* TyCtxConv *)
  - admit.

  (* TyProd *)
  - { rewrite_substs.
      capply TyProd.
      - apply IHhA. apply SubstCons.
        + admit. (* ok *)
        + admit. (* not ok *)
        + (* capply TermVarZero. *) (* not ok? :( *)
          admit.
      - apply X. assumption.
      - admit. (* ok *)
    }

  (* TyId *)
  - admit.

  (* TyEmpty *)
  - admit.

  (* TyUnit *)
  - admit.

  (* TyBool *)
  - admit.

  (* TyBinaryProd *)
  - admit.

  (* TyUni *)
  - admit.

  (* TyEl *)
  - admit.
Admitted.



End Substitutions.

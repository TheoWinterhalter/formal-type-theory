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

(* Let's do it with preconditions for now *)
(* Context `{configPrecondition : config.Precondition}. *)
Local Instance havePrecondition : config.Precondition :=
  {| config.flagPrecondition := config.Yes |}.
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

Fixpoint issubst_rec (σ : substitution) (Γ Δ : context) (hΔ : isctx Δ) : Type.
  destruct hΔ as [| Δ A hΔ hA].
  - exact Datatypes.unit.
  - doConfig.
    simple refine (_ * _).
    + exact (issubst_rec σ↑ Γ Δ hΔ).
    + exact (isterm Γ (var 0)[σ] A[σ↑]).
Defined.

Definition issubst σ Γ Δ := { h : isctx Δ & issubst_rec σ Γ Δ h }.

Lemma SubstNil :
  forall {σ Γ},
    isctx Γ ->
    issubst σ Γ ctxempty.
Proof.
  intros σ Γ hΓ.
  exists CtxEmpty. exact tt.
Defined.

Lemma SubstCons :
  forall {σ Γ Δ A},
    isctx Γ ->
    isctx Δ ->
    istype Δ A ->
    issubst (σ↑) Γ Δ ->
    isterm Γ (var 0)[σ] A[σ↑] ->
    issubst σ Γ (ctxextend Δ A).
Proof.
  intros σ Γ Δ A hΓ _ hA [hΔ hσ] hv.
  unshelve eexists.
  - now capply CtxExtend.
  - cbn. split.
    + assumption.
    + assumption.
Defined.

Lemma issubst_ext :
  forall {Γ Δ},
    isctx Γ ->
    isctx Δ ->
    forall {σ ρ},
      σ ~ ρ ->
      issubst σ Γ Δ ->
      issubst ρ Γ Δ.
Proof.
  intros Γ Δ hΓ hΔ.
  induction hΔ as [| Δ B hΔ ih hB] ; intros σ ρ h [hΔB hσ].
  - now exists CtxEmpty.
  - doConfig.
    specialize (ih (σ↑) (ρ↑)).
    assert (hh : σ ↑ ~ ρ ↑).
    { intro n. rewrite_substs. apply h. }
    specialize (ih hh).
    assert (hσ' : issubst σ↑ Γ Δ).
    {

 (* exists hΔB. inversion hΔB as [| Δ' B' hΔ' hB']. *)
 (*    + (* Impossible case but true. *) *)
 (*      subst. easy. *)
 (*    + cbn. destruct hσ as [hσ hv]. *)
 (*      split. *)
 (*      * specialize (ih (σ↑) (ρ↑)). *)
 (*        assert (hh : σ ↑ ~ ρ ↑). *)
 (*        { intro n. rewrite_substs. apply h. } *)
 (*        specialize (ih hh). *)
 (*        assert (hσ' : issubst σ↑ Γ Δ). *)
 (*        { *)
Abort.
(* Working by induction on the derivation is really annoying when what
   we really want is to work by induction on contexts.
 *)


Lemma SubstWeak :
  forall {Γ A},
    isctx Γ ->
    istype Γ A ->
    issubst sbweak (ctxextend Γ A) Γ.
Proof.
  intros Γ A hΓ hA.
  exists hΓ. induction hΓ as [| Δ B hΔ ih hB].
  - exact tt.
  - split.
    +
Abort.


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

| SubstWeak :
    forall {Γ A},
      isctx Γ ->
      istype Γ A ->
      issubst sbweak (ctxextend Γ A) Γ
.

Lemma issubst_ext :
  forall {Γ Δ},
    isctx Γ ->
    isctx Δ ->
    forall {σ ρ},
      σ ~ ρ ->
      issubst σ Γ Δ ->
      issubst ρ Γ Δ.
Proof.
  intros Γ Δ hΓ hΔ.
  induction hΔ ; intros σ ρ h hσ.
  - apply SubstNil. assumption.
  - rename G into Δ.
    inversion hσ.
    + apply SubstNil. assumption.
    + doConfig.
      assert (Δ0 = Δ).
      { eapply ctxextend_inj. apply H2. }
      assert (A0 = A).
      { eapply ctxextend_inj. apply H2. }
      subst.
      apply SubstCons.
      * assumption.
      * assumption.
      * assumption.
      * apply X with (σ := σ ↑).
        -- intro n. rewrite_substs. apply h.
        -- assumption.
      * (* Some setoid rewrite might help me? *)
        (* It is true, but I'm lazy for now. *)
        admit.
    + subst. rename A0 into B.
Abort. (* Maybe no longer necessary. *)

Fact eqDropCons : forall {u σ}, (u ⋅ σ) ↑ ~ σ.
Proof.
  intros u σ n.
  now rewrite_substs.
Defined.

Lemma SubstCons' :
  forall {Γ Δ A u σ},
    isctx Γ ->
    isctx Δ ->
    issubst σ Γ Δ ->
    istype Δ A ->
    isterm Γ u A[σ] ->
    issubst (u ⋅ σ) Γ (ctxextend Δ A).
Proof.
  intros Γ Δ A u σ hΓ hΔ hσ hA hu.
  apply SubstCons.
  - assumption.
  - (* apply issubst_ext with (σ0 := σ). *)
(*     + assumption. *)
(*     + assumption. *)
(*     + (* symmetry. *) *)
(*       intro n. symmetry. *)
(*       apply eqDropCons. *)
(*     + assumption. *)
(*   - rewrite_substs. *)
(*     (* Some setoid rewrite would help us. *)
(*        We'll only deal with those once we are convinced we're on the right *)
(*        tracks. *)
(*      *) *)
(*     admit. *)
(* Admitted. *)
Abort.

Lemma SubstCtxConv :
  forall {σ Γ Δ Δ'},
    eqctx Δ' Δ ->
    issubst σ Γ Δ ->
    issubst σ Γ Δ'.
Proof.
  intros σ Γ Δ Δ' h1 h2.
  induction h2.
  -

  ceapply TermCtxConv.
  - apply h2.
    ceapply TermCtxConv.
    + eassumption.
    + assumption.
    + admit. (* Need precondition *)
    + admit. (* Need precondition *)
    + admit. (* Need precondition *)
  - capply CtxRefl. admit. (* Need precondition *)
  - admit. (* Need precondition *)
  - admit. (* Need precondition *)
  - admit. (* Precondition in the definition of issubst? *)
Admitted.

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
  - { apply IHhA. ceapply SubstCtxConv.
      - eassumption.
      - assumption.
    }

  (* TyProd *)
  - { rewrite_substs.
      capply TyProd.
      - apply IHhA. (* apply SubstCons. *)
        (* We do it by hand, hopefully understanding who is SubstCons *)
        intros [| n] C h.
        + rewrite_substs.
          (* Here we would need some kind of inversion AND induction
             hypothesis. *)
          admit.
        + rewrite_substs. admit.
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

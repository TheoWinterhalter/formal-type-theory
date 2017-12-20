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

(* A substitution is well-formed if it is well-formed on variables.
   The action on types and terms is derived from it.
 *)
Inductive issubst (σ : substitution) (Γ : context) : context -> Type :=
| SubstNil :
    issubst σ Γ ctxempty

| SubstCons :
    forall {Δ A},
      istype Δ A ->
      issubst (σ↑) Γ Δ ->
      isterm Γ (var 0)[← σ] A[σ] ->
      issubst σ Γ (ctxextend Δ A)
.

Lemma issubst_ext :
  forall {Γ Δ},
    isctx Γ ->
    isctx Δ ->
    forall {σ ρ},
      (forall n, (var n)[← σ] = (var n)[← ρ]) ->
      issubst σ Γ Δ ->
      issubst ρ Γ Δ.
Proof.
  intros Γ Δ hΓ hΔ.
  induction hΔ ; intros σ ρ h hσ.
  - apply SubstNil.
  - rename G into Δ.
    inversion hσ.
    + apply SubstNil.
    + doConfig. apply SubstCons.
      * assumption.
      * (* apply X with (σ := σ ↑). *)
        (* -- intro n. rewrite_substs. apply h. *)
        (* -- *)
        (* Missing injectivity of ctxextend... *)
Abort.


Lemma SubstId :
  forall {Γ},
    isctx Γ ->
    issubst sbid Γ Γ.
Proof.
  intros Γ hΓ. induction hΓ.
  - apply SubstNil.
  - apply SubstCons.
    + assumption.
    +
  (* rewrite_substs. assumption. *)
(* Defined. *)
Abort.

Fixpoint dropCtx Δ (h : isctx Δ) (n : nat) : context.
  destruct n.
  - exact Δ.
  - destruct h.
    + exact ctxempty.
    + doConfig. exact (dropCtx G i n).
Defined.

Fact dropCtx0 : forall Δ h, dropCtx Δ h 0 = Δ.
Proof.
  intros Δ h. destruct h ; reflexivity.
Defined.

Fixpoint SubstConsDrop {Γ Δ σ}
         (hΓ : isctx Γ) (hΔ : isctx Δ) (hσ : issubst (σ↑) Γ (dropCtx Δ hΔ 1)) :
  issubst σ Γ Δ.
Proof.
  destruct hΔ.
  - apply SubstNil.
  - rename G into Δ.
    apply SubstCons.
    + assumption.
    + simpl in hσ. rewrite dropCtx0 in hσ. assumption.
    + (* How should we take this into account? *)
Abort.

Fixpoint SubstDrop {Γ Δ σ n} (hΓ : isctx Γ) (hΔ : isctx Δ) :
  issubst σ Γ Δ ->
  issubst (σ ↑ n) Γ (dropCtx Δ hΔ n).
Proof.
  intro hσ.
  destruct hΔ.
  - simpl. apply SubstNil.
  - rename G into Δ.
    destruct n.
    + simpl. admit. (* This should be assumed I guess. *)
    + simpl.


    + assumption.
    +
Abort.

Lemma SubstWeak :
  forall {Γ A},
    (config.flagPrecondition -> isctx Γ) ->
    istype Γ A ->
    issubst sbweak (ctxextend Γ A) Γ.
Proof.
  intros Γ A hΓ hA n B h.
  rewrite_substs.
  capply TermVarSucc.
  - assumption.
  - admit. (* Missing hyp *)
  - assumption.
Admitted.

Lemma SubstCons :
  forall {σ u Γ Δ A},
    istype Δ A ->
    issubst σ Γ Δ ->
    isterm Γ u A[σ] ->
    issubst (u ⋅ σ) Γ (ctxextend Δ A).
Proof.
  intros σ u Γ Δ A hA hσ hu n B h.
  induction n.
  - rewrite_substs.
    admit. (* Wrong?? *)
  - rewrite_substs.
    admit. (* This rule is probably wrong! *)
Abort.

Lemma SubstCtxConv :
  forall {σ Γ Δ Δ'},
    eqctx Δ' Δ ->
    issubst σ Γ Δ ->
    issubst σ Γ Δ'.
Proof.
  intros σ Γ Δ Δ' h1 h2 n B h.
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

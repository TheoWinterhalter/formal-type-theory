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
      isterm Γ (var 0)[← σ] A[σ↑] ->
      issubst σ Γ (ctxextend Δ A)
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
  - apply SubstNil.
  - rename G into Δ.
    inversion hσ.
    + apply SubstNil.
    + doConfig.
      (* Missing injectivity of ctxextend... *)
      assert (Δ0 = Δ) by admit.
      assert (A0 = A) by admit.
      subst.
      apply SubstCons.
      * assumption.
      * apply X with (σ := σ ↑).
        -- intro n. rewrite_substs. apply h.
        -- assumption.
      * (* Some setoid rewrite might help me? *)
        (* It is true, but I'm lazy for now. *)
        admit.
Admitted.

Fact eqDropCons : forall {u σ}, (u ⋅ σ) ↑ ~ σ.
Proof.
  intros u σ n.
  now rewrite_substs.
Defined.

Instance sbextSymmetric `{Syntax} : Symmetric sbextR.
Proof.
  intros σ ρ h n.
  symmetry. apply h.
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
  - apply issubst_ext with (σ0 := σ).
    + assumption.
    + assumption.
    + (* symmetry. *)
      intro n. symmetry.
      apply eqDropCons.
    + assumption.
  - rewrite_substs.
    (* Some setoid rewrite would help us.
       We'll only deal with those once we are convinced we're on the right
       tracks.
     *)
    admit.
Admitted.

Fixpoint shiftby Δ (h : isctx Δ) (n : nat) : substitution.
  destruct h.
  - exact sbid.
  - doConfig. rename G into Δ.
    exact (var n ⋅ shiftby Δ i (S n)).
Defined.

Require Import Coq.Vectors.Vector.

Fixpoint ctxextension (Γ : context) {n : nat} (An : Vector.t type n) : context :=
  match An with
  | nil _ => Γ
  | cons _ A n An => ctxextend (ctxextension Γ An) A
  end.

Fixpoint isctxextension (Γ : context) {n : nat} (An : Vector.t type n) :=
  (isctx (ctxextension Γ An) *
  match An with
  | nil _ => isctx Γ
  | cons _ A n An =>
    isctx Γ * isctxextension Γ An
  end)%type.

Fixpoint SubstShiftby Γ (h : isctx Γ) (n : nat) (An : Vector.t type n) :
  isctxextension Γ An ->
  issubst (shiftby Γ h n) (ctxextension Γ An) Γ.
Proof.
  intro h'.
  config destruct h.
  - apply SubstNil.
  - simpl. apply SubstCons'.
    + destruct An ; apply h'.
    + config assumption.
    + assert (ctxextension (ctxextend G A) An = ctxextension G (shiftin A An)).
      { induction An.
        - cbn. reflexivity.
        - cbn. f_equal. apply IHAn. cbn in h'.
          apply h'. (* Ugly because not a lemma. *)
      }
      rewrite H. apply SubstShiftby.
      induction An.
      * cbn in *. repeat split.
        -- apply h'.
        -- config assumption.
        -- config assumption.
        -- config assumption.
      * cbn in *. repeat split.
        -- rewrite <- H. apply h'.
        -- config assumption.
        -- apply IHAn.
           ++ apply h'.
           ++ admit. (* Injectivity of ctxextend again *)
    + assumption.
    + induction n.
      * (* How did I end up here? Aw isn't the right type... *)
Abort.


(* Fixpoint exsbid Γ (h : isctx Γ) : substitution *)

(* with exsbweak Γ (A : type) (h : isctx Γ) : substitution. *)

(*   - { destruct h. *)
(*       - exact sbid. (* Anything would fit really. *) *)
(*       - rename G into Γ. doConfig. *)
(*         exact (var 0 ⋅ exsbweak Γ A i). *)
(*     } *)

(*   - { destruct h. *)
(*       - exact sbweak. *)
(*       - rename G into Γ, A0 into B. doConfig. *)

(* Defined. *)

(* Lemma SubstExId : *)
(*   forall {Γ} (h : isctx Γ), *)
(*     issubst (exsbid Γ h) Γ Γ. *)
(* Proof. *)
(*   intros Γ h. *)
(*   induction h. *)
(*   - apply SubstNil. *)
(*   - rename G into Γ. doConfig. cbn. *)
(*     apply SubstCons'. *)
(*     + capply CtxExtend. *)
(*       * capply i. (* Why didn't doConfig work here? *) *)
(*       * assumption. *)
(*     + capply i. *)
(*     + specialize (X config.yes). *)


Lemma SubstWeak :
  forall {Γ A},
    isctx Γ ->
    istype Γ A ->
    issubst sbweak (ctxextend Γ A) Γ.
Proof.
  intros Γ A hΓ.
  induction hΓ ; intro hA.
  - apply SubstNil.
  - doConfig. rename A0 into B, G into Δ.
    apply SubstCons.
    + assumption.
    + admit.
    + (* rewrite_substs. ceapply TermVarSucc. *)
      (* * capply CtxExtend ; assumption. *)
      (* * *)
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
    + doConfig. admit.
    + doConfig. rewrite_substs. admit.
Admitted. (* It holds as long as we can type weakening. *)

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

(* Forcing Translation

   Based on The Definitional Side of the Forcing
   by Jaber et al.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

Require ett_sanity.
Require Import inversion.

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
    := {| config.universesFlag := config.Yes |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.Yes |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.

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
    := {| config.universesFlag := config.Yes |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.Yes |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.

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

(* We give ourselves a category in the source *)
(* Note: This should also hold in the target by equivalence ett/ptt. *)
Context `{ℙ : term}.
Context `{
  hℙ :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ ℙ (Uni (uni 0))
}.

Definition Tℙ := El (uni 0) ℙ.

Context `{_Hom : term}.
Context `{
  hHom :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ
                 _Hom
                 (Arrow Tℙ (Arrow Tℙ (Uni (uni 0))))
}.

Definition Hom p q :=
  El (uni 0)
     (app (app _Hom Tℙ (Arrow Tℙ (Uni (uni 0))) p)
          Tℙ
          (Uni (uni 0))
          q).

Context `{_idℙ : term}.
Context `{
  hidℙ :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ _idℙ (Prod Tℙ (Hom (var 0) (var 0)))
}.

Definition idℙ p :=
  app _idℙ Tℙ (Hom (var 0) (var 0)) p.

Context `{_comp : term}.
Context `{
  hcomp :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ
                 _comp
                 (Prod Tℙ
                       (Prod Tℙ
                             (Prod Tℙ
                                   (Arrow (Hom (var 2) (var 1))
                                          (Arrow (Hom (var 1) (var 0))
                                                 (Hom (var 2) (var 0)))))))
}.

Definition comp p q r f g :=
  app (app (app (app (app _comp
                          Tℙ
                          (Prod Tℙ
                                (Arrow (Hom (var 2) (var 1))
                                       (Arrow (Hom (var 1) (var 0))
                                              (Hom (var 2) (var 0)))))
                          p)
                     Tℙ
                     (Prod Tℙ
                           (Arrow (Hom p (var 1))
                                  (Arrow (Hom (var 1) (var 0))
                                         (Hom p (var 0)))))
                     q)
                Tℙ
                (Arrow (Hom p q)
                       (Arrow (Hom q (var 0)) (Hom p (var 0)))) r)
           (Hom p q)
           (Arrow (Hom q r) (Hom p r))
           f)
      (Hom q r)
      (Hom p r)
      g.

(* This is really illegible so we need to complete the alternative syntax. *)

(* We require extra definitional equalities *)
Context `{
  CompIdℙLeft :
    forall {Γ p q f},
      Ttt.isterm Γ f (Hom p q) ->
      Ttt.eqterm Γ (comp p p q (idℙ p) f) f (Hom p q)
}.
Context `{
  CompIdℙRight :
    forall {Γ p q f},
      Ttt.isterm Γ f (Hom p q) ->
      Ttt.eqterm Γ (comp p q q f (idℙ q)) f (Hom p q)
}.
Context `{
  CompℙAssoc :
    forall {Γ p q r s f g h},
      Ttt.isterm Γ f (Hom p q) ->
      Ttt.isterm Γ g (Hom q r) ->
      Ttt.isterm Γ h (Hom r s) ->
      Ttt.eqterm Γ
                 (comp p q s f (comp q r s g h))
                 (comp p r s (comp p q r f g) h)
                 (Hom p s)
}.

(* As well as those due to the presence of explicit substitutions and
   de Bruijn indices. *)
Context `{
  EqSubstℙ :
    forall {Γ Δ ρ},
      Ttt.issubst ρ Γ Δ ->
      Ttt.eqterm Γ (subst ℙ ρ) ℙ (Uni (uni 0))
}.

(* I'm not sure about this *)
Context `{
  EqSubstHom :
    forall {Γ Δ ρ},
      Ttt.issubst ρ Γ Δ ->
      Ttt.eqterm Γ
                 (subst _Hom ρ)
                 _Hom
                 (Arrow Tℙ (Arrow Tℙ (Uni (uni 0))))
}.

Axiom todo : forall {A}, A.
Ltac todo := apply todo.

Lemma EqTySubstℙ :
  forall {Γ Δ ρ},
    Ttt.issubst ρ Γ Δ ->
    Ttt.eqtype Γ (Subst Tℙ ρ) Tℙ.
Proof.
  intros Γ Δ ρ h.
  ceapply EqTyTrans.
  - ceapply EqTySym.
    ceapply ElSubst.
    + eassumption.
    + apply hℙ.
      apply (ett_sanity.sane_issubst _ _ _ h).
  - ceapply CongEl.
    eapply EqSubstℙ.
    eassumption.
Defined.

Lemma EqTySubstHom :
  forall {Γ Δ ρ u v},
    Ttt.issubst ρ Γ Δ ->
    Ttt.isterm Δ u Tℙ ->
    Ttt.isterm Δ v Tℙ ->
    Ttt.eqtype Γ
               (Subst (Hom u v) ρ)
               (Hom (subst u ρ) (subst v ρ)).
Proof.
  intros Γ Δ ρ u v hρ hu hv.
  unfold Hom.
  (* unfold Ttt.eqtype. pushsubst. *)
  (* This shouldn't be necessary! *)
  ceapply EqTyTrans ; [
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [
        ceapply ElSubst
      | ceapply EqTyRefl
      | ..
      ]
    | ..
    ]
  | ..
  ].
  - eassumption.
  - ceapply TermTyConv ; [ ceapply TermApp | .. ].
    + ceapply TermTyConv ; [ ceapply TermApp | .. ].
      * ceapply TermTyConv ; [ apply hHom | .. ].
        -- apply (ett_sanity.sane_issubst _ _ _ hρ).
        -- todo. (* It's true and tiresome *)
      * assumption.
      * todo.
    + assumption.
    + pushsubst.
      * capply SubstZero. assumption.
      * capply EqTyRefl. capply TyUni.
        apply (ett_sanity.sane_issubst _ _ _ hρ).
  - ceapply TySubst.
    + eassumption.
    + ceapply TyEl.
      * ceapply TermTyConv ; [ ceapply TermApp | .. ].
        -- ceapply TermTyConv ; [ ceapply TermApp | .. ].
           ++ ceapply TermTyConv ; [ apply hHom | .. ].
              ** apply (ett_sanity.sane_issubst _ _ _ hρ).
              ** todo.
           ++ assumption.
           ++ todo.
        -- assumption.
        -- pushsubst.
           ++ capply SubstZero. assumption.
           ++ capply EqTyRefl. capply TyUni.
              apply (ett_sanity.sane_issubst _ _ _ hρ).
  - ceapply CongEl.
    pushsubst ; [ instantiate (1 := Δ) | .. ].
    + ceapply TermTyConv ; [ ceapply TermApp | .. ].
      * ceapply TermTyConv ; [ apply hHom | .. ].
        -- apply (ett_sanity.sane_issubst _ _ _ hρ).
        -- todo.
      * assumption.
      * todo.
    + assumption.
    + assumption.
    + ceapply EqTyConv ; [ ceapply CongApp | .. ].
      * todo.
      * todo.
      * pushsubst ; [ instantiate (1 := Δ) | .. ].
        -- ceapply TermTyConv ; [ apply hHom | .. ].
           ++ apply (ett_sanity.sane_issubst _ _ _ hρ).
           ++ todo.
        -- assumption.
        -- assumption.
        -- ceapply EqTyConv ; [ ceapply CongApp | .. ].
           ++ todo.
           ++ todo.
           ++ ceapply EqTyConv ; [ eapply EqSubstHom | .. ].
              ** eassumption.
              ** todo.
           ++ capply EqRefl. ceapply TermSubst ; eassumption.
           ++ todo.
        -- todo.
      * capply EqRefl. ceapply TermSubst ; eassumption.
      * todo.
    + pushsubst.
      * eassumption.
      * capply SubstZero. assumption.
      * capply EqTyRefl. capply TyUni.
        apply (ett_sanity.sane_issubst _ _ _ hρ).
      * pushsubst.
        -- eassumption.
        -- capply EqTyRefl. capply TyUni.
           apply (ett_sanity.sane_issubst _ _ _ hρ).
Defined.

Lemma Tyℙ :
  forall {Γ},
    Ttt.isctx Γ ->
    Ttt.istype Γ Tℙ.
Proof.
  intros Γ h.
  ceapply TyEl. apply hℙ. assumption.
Defined.


Lemma TyHom :
  forall {Γ u v},
    Ttt.isterm Γ u Tℙ ->
    Ttt.isterm Γ v Tℙ ->
    Ttt.istype Γ (Hom u v).
Proof.
  intros Γ u v hu hv.
  ceapply TyEl.
  ceapply TermTyConv ; [ ceapply TermApp | .. ].
  - ceapply TermTyConv ; [ ceapply TermApp | .. ].
    + ceapply TermTyConv ; [ apply hHom | .. ].
      * apply (ett_sanity.sane_isterm _ _ _ hu).
      * todo.
    + assumption.
    + todo.
  - assumption.
  - pushsubst.
    + capply SubstZero. assumption.
    + capply EqTyRefl. capply TyUni.
      apply (ett_sanity.sane_isterm _ _ _ hu).
Defined.


Lemma CongHom :
  forall {Γ u1 u2 v1 v2},
    Ttt.eqterm Γ u1 u2 Tℙ ->
    Ttt.eqterm Γ v1 v2 Tℙ ->
    Ttt.eqtype Γ (Hom u1 v1) (Hom u2 v2).
Proof.
  intros.
  unfold Hom.
  ceapply CongEl.
  ceapply EqTyConv ; [ ceapply CongApp | .. ].
  - capply EqTyRefl.
    apply (ett_sanity.sane_eqterm _ _ _ _ X).
  - capply EqTyRefl.
    capply TyUni. capply CtxExtend.
    apply (ett_sanity.sane_eqterm _ _ _ _ X).
  - ceapply EqTyConv ; [ ceapply CongApp | .. ].
    + capply EqTyRefl.
      apply (ett_sanity.sane_eqterm _ _ _ _ X).
    + capply EqTyRefl. capply TyProd.
      ceapply TySubst.
      * capply SubstWeak. ceapply TyEl. apply hℙ.
        capply CtxExtend.
        apply (ett_sanity.sane_eqterm _ _ _ _ X).
      * capply TyUni. capply CtxExtend.
        apply (ett_sanity.sane_eqterm _ _ _ _ X).
    + capply EqRefl.
      ceapply TermTyConv ; [ eapply hHom | .. ].
      * apply (ett_sanity.sane_eqterm _ _ _ _ X).
      * todo.
    + assumption.
    + todo.
  - assumption.
  - pushsubst.
    + capply SubstZero.
      apply (ett_sanity.sane_eqterm _ _ _ _ X0).
    + capply EqTyRefl. capply TyUni.
      apply (ett_sanity.sane_eqterm _ _ _ _ X).
Defined.

Lemma hidℙ' :
  forall {Γ x},
    Ttt.isterm Γ x Tℙ ->
    Ttt.isterm Γ (idℙ x) (Hom x x).
Proof.
  intros Γ x h.
  unfold idℙ.
  ceapply TermTyConv ; [ ceapply TermApp | .. ].
  - apply hidℙ.
    apply (ett_sanity.sane_isterm _ _ _ h).
  - assumption.
  - ceapply EqTyTrans ; [ eapply EqTySubstHom | .. ].
    + capply SubstZero. assumption.
    + ceapply TermTyConv ; [ capply TermVarZero | .. ].
      * apply (ett_sanity.sane_isterm _ _ _ h).
      * todo.
    + ceapply TermTyConv ; [ capply TermVarZero | .. ].
      * apply (ett_sanity.sane_isterm _ _ _ h).
      * todo.
    + capply CongHom.
      * unfold Ttt.eqterm. pushsubst.
        -- assumption.
        -- capply EqRefl. assumption.
      * unfold Ttt.eqterm. pushsubst.
        -- assumption.
        -- capply EqRefl. assumption.
Defined.



(* We also introduce the notion of forcing context *)
Inductive fctx :=
| cond : fctx
| fxvar : fctx -> fctx
| fxpath : fctx -> fctx.

(* As well as a validity judgment for them *)
Inductive isfctx : context -> fctx -> Type :=
| valid_cond : isfctx ctxempty cond
| valid_fxvar : forall Γ σ A, isfctx Γ σ -> isfctx (ctxextend Γ A) (fxvar σ)
| valid_fxpath : forall Γ σ, isfctx Γ σ -> isfctx Γ (fxpath σ).

(* Last condition of a forcing context *)
Fixpoint _last_cond (o : nat) (σ : fctx) : nat :=
  match σ with
  | cond => o
  | fxvar σ => _last_cond (S o) σ
  | fxpath σ => S o
  end.

Definition last_cond σ := _last_cond 0 σ.

(* Also known as length *)
Fixpoint _first_cond o σ :=
  match σ with
  | cond => o
  | fxvar σ => _first_cond (S o) σ
  | fxpath σ => _first_cond (S (S o)) σ
  end.

Definition first_cond σ := _first_cond 0 σ.

(* Morphism of a variable *)
Fixpoint _morph (o : nat) (σ : fctx) (x : nat) : term :=
  match σ, x with
  | cond, _ => idℙ (var o) (* Should never happen should it? *)
  | fxvar σ, 0 => idℙ (var (_last_cond o σ))
  | fxvar σ, S x => _morph (S o) σ x
  | fxpath σ, S (S x) =>
    comp todo todo todo
         (_morph (S (S o)) σ x)
         (var o)
  | fxpath σ, _ => idℙ (var (_first_cond o σ))
  end.

Definition morph σ x := _morph 0 σ x.

Fixpoint lift_var (σ : fctx) (x : nat) : nat :=
  match σ, x with
  | cond, _ => 0 (* This case doesn't happend with well-typed things *)
  | fxvar σ, 0 => 0
  | fxvar σ, S x => S (lift_var σ x)
  | fxpath σ, x => S (S (lift_var σ x))
  end.

(* Translation *)

Reserved Notation "[[ A ]] σ" (at level 5).
Reserved Notation "[ u | A ]! σ" (at level 5).
Reserved Notation "[[ A ]]! σ" (at level 5).

Definition fProd' (σ : fctx) (A : type) : type :=
  Prod (Hom (var (S (last_cond σ))) (var 0)) A.

Definition flam (σ : fctx) (A : type) (u : term) : term :=
  lam Tℙ (fProd' σ A) (lam (Hom (var (S (last_cond σ))) (var 0)) A u).

Definition fProd (σ : fctx) (A : type) : type :=
  Prod Tℙ (fProd' σ A).

Fixpoint trans_type (σ : fctx) (A : type) {struct A} : type :=
  match A with
  | Prod A B => Prod ([[ A ]]! (fxpath σ)) ([[ B ]] (fxvar (fxpath σ)))

  | Id A u v => Id ([[ A ]] (fxpath σ))
                  (trans_term (fxpath σ) u)
                  (trans_term (fxpath σ) v)
                  (* ([ u | A ]! (fxpath σ)) *)
                  (* ([ v | A ]! (fxpath σ)) *)

  | Subst A ρ => Subst ([[ A ]] (fxpath σ)) (trans_subst (fxpath σ) ρ)

  | Uni l => fProd (fxpath σ) (Uni l)

  | El l a => El l (trans_term (fxpath σ) a)

  (* Cases that don't happen given our config *)
  | _ => Empty

  end

with trans_term (σ : fctx) (u : term) {struct u} : term :=
  match u with
  | var n =>
    app (app (var (lift_var σ n))
             todo
             todo
             (var (last_cond σ)))
        todo
        todo
        (morph σ n)

  | lam A B t =>
    lam ([[A]]! σ)
        ([[B]] (fxvar σ))
        (trans_term (fxvar σ) t)

  | app u A B v =>
    app (trans_term σ u)
        ([[A]]! σ)
        ([[B]] (fxvar σ))
        ([ v | A ]! σ)

  | refl A u =>
    refl ([[A]] σ)
         (trans_term σ u)

  (* TODO *)

  (* Cases that don't happen given our config *)
  | _ => unit
  end

with trans_subst (σ : fctx) (ρ : substitution) {struct ρ} : substitution :=
  match ρ with
  | sbid => sbid

  (* TODO *)

  (* Cases that don't happen given our config *)
  | _ => todo
  end

(* Intuition: [[ A ]]σ := [ A ]σ {1 := σe} {0 := id σe} *)
where "[[ A ]] σ" :=
  (Subst (Subst (trans_type σ A)
                (sbshift (Hom (var (S (last_cond σ)))
                              (var 0))
                         (sbzero Tℙ
                                 (var (last_cond σ)))))
         (sbzero (Hom (var (last_cond σ)) (var (last_cond σ)))
                 (idℙ (var (last_cond σ)))))

and "[ u | A ]! σ" :=
    (flam σ
          (Subst (Subst A (sbweak Tℙ))
                 (sbweak (Hom (var (S (last_cond σ))) (var 0))))
          (subst (subst (trans_term σ u)
                        (sbweak Tℙ))
                 (sbweak (Hom (var (S (last_cond σ))) (var 0)))))

and "[[ A ]]! σ" :=
  (fProd σ
         (Subst (Subst ([[A]] σ) (sbweak Tℙ))
                (sbweak (Hom (var (S (last_cond σ))) (var 0))))).

Fixpoint trans_ctx (σ : fctx) (Γ : context) : context :=
  match Γ, σ with
  | ctxempty, cond =>
    ctxextend ctxempty Tℙ

  | Γ, fxpath σ =>
    ctxextend (ctxextend (trans_ctx σ Γ) Tℙ)
              (Hom (var (S (last_cond σ))) (var 0))

  | ctxextend Γ A, fxvar σ =>
    ctxextend (trans_ctx σ Γ) ([[A]]! σ)

  (* Case that can't happen when considering valid forcing contexts *)
  | _, _ => ctxempty

  end.

Lemma last_cond_S :
  forall {σ Γ},
    isfctx Γ σ ->
    forall n, _last_cond (S n) σ = S (_last_cond n σ).
Proof.
  intros σ Γ h n.
  dependent induction h.

  - simpl. easy.
  - simpl. apply IHh.
  - simpl. easy.
Defined.


Lemma last_cond_var :
  forall {σ Γ},
    isfctx Γ σ ->
    last_cond (fxvar σ) = S (last_cond σ).
Proof.
  intros σ Γ h.
  dependent induction h.

  - unfold last_cond. simpl. easy.

  - unfold last_cond. simpl.
    now rewrite @last_cond_S with (Γ := Γ).

  - unfold last_cond. simpl. easy.
Defined.

Lemma trans_ctx_fxpath :
  forall {Γ σ},
    trans_ctx (fxpath σ) Γ =
    ctxextend (ctxextend (trans_ctx σ Γ) Tℙ)
              (Hom (var (S (last_cond σ))) (var 0)).
Proof.
  intros Γ σ.
  destruct Γ.
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

Lemma trans_ctx_fxvar :
  forall {Γ A σ},
    trans_ctx (fxvar σ) (ctxextend Γ A) =
    ctxextend (trans_ctx σ Γ) ([[A]]! σ).
Proof.
  intros Γ A σ.
  simpl. reflexivity.
Defined.


Lemma isfctx_conv :
  forall {Γ σ},
    isfctx Γ σ ->
    forall Δ,
      Stt.eqctx Δ Γ ->
      isfctx Δ σ.
Proof.
  intros Γ σ hσ.
  dependent induction hσ ; intros Δ eq.

  - (* pose (eqctx_ctxempty_right eq). *)
    (* Problem: inversion has been proven on economic tt and I want this
       in paranoid tt! *)
    assert (eq' : Δ = ctxempty) by todo.
    rewrite eq'. apply valid_cond.
  - (* Here again we have a result on ett where we need it on ptt,
       we could always invoke the translation between them. *)
    assert (eq' : {Δ' : context & {A' : type & Δ = ctxextend Δ' A'}}) by todo.
    destruct eq' as [Δ' [A' eq'] ].
    rewrite eq' in *.
    apply valid_fxvar.
    apply IHhσ.
    (* This also holds by inversion. *)
    todo.
  - apply valid_fxpath. now apply IHhσ.
Qed.

Lemma sound_trans_type' {σ Γ A} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A) ->
  Ttt.istype (trans_ctx σ Γ) ([[A]] σ).
Proof.
  intro h.
  ceapply TySubst.
  - ceapply SubstZero. apply hidℙ'.
    todo. (* We need to find how to properly prove it. *)
  - ceapply TySubst.
    + ceapply SubstCtxConv ; [
        ceapply SubstShift
      | ceapply EqCtxExtend ; [ capply CtxRefl | .. ]
      | capply CtxRefl
      ].
      * ceapply SubstZero. todo. (* Same here *)
      * apply TyHom.
        -- todo. (* Similar *)
        -- todo. (* Similar' *)
      * rewrite trans_ctx_fxpath in h.
        todo. (* Some sanity and inversion *)
      * ceapply EqTyTrans ; [ eapply EqTySubstHom | .. ].
        -- ceapply SubstZero. todo. (* Same again *)
        -- todo. (* Repeat *)
        -- todo. (* ... *)
        -- capply CongHom.
           ++ unfold Ttt.eqterm. pushsubst.
              all:todo. (* ... *)
           ++ unfold Ttt.eqterm. pushsubst.
              all:todo. (* ... *)
      * capply CtxExtend.
        apply TyHom.
        -- todo. (* ... *)
        -- todo. (* ... *)
    + rewrite trans_ctx_fxpath in h. apply h.
Qed.

Lemma sound_trans_type'' {σ Γ A} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A) ->
  Ttt.istype (trans_ctx σ Γ) ([[A]]! σ).
Proof.
  intro h.
  ceapply TyProd. ceapply TyProd. ceapply TySubst.
  - capply SubstWeak. apply TyHom.
    + todo.
    + todo.
  - ceapply TySubst.
    + capply SubstWeak. apply Tyℙ.
      todo. (* Something like sanity and inversion. *)
    + now apply sound_trans_type'.
Qed.

Lemma sound_trans_term' {σ Γ A u} :
  Ttt.isterm (trans_ctx σ Γ) (trans_term σ u) ([[A]] σ) ->
  Ttt.isterm (trans_ctx σ Γ) ([u | [[A]] σ]! σ) ([[A]]! σ).
Proof.
  intro h.
  ceapply TermAbs. ceapply TermAbs.
  ceapply TermSubst.
  - capply SubstWeak. apply TyHom.
    + todo.
    + todo.
  - ceapply TermSubst.
    + capply SubstWeak. apply Tyℙ.
      todo. (* Sanity *)
    + exact h.
Qed.

Lemma sound_trans_eqtype' {σ Γ A B} :
  Ttt.eqtype (trans_ctx (fxpath σ) Γ) (trans_type σ A) (trans_type σ B) ->
  Ttt.eqtype (trans_ctx σ Γ) ([[A]] σ) ([[B]] σ).
Proof.
  intro h.
  ceapply CongTySubst.
  - ceapply SubstRefl. capply SubstZero.
    apply hidℙ'. todo.
  - ceapply CongTySubst.
    + ceapply SubstRefl.
      ceapply SubstCtxConv ; [
        ceapply SubstShift
      | ceapply EqCtxExtend ; [ capply CtxRefl | .. ]
      | capply CtxRefl
      ].
      * capply SubstZero. todo.
      * apply TyHom.
        -- todo. (* Similar *)
        -- todo. (* Similar' *)
      * rewrite trans_ctx_fxpath in h.
        todo. (* Some sanity and inversion *)
      * ceapply EqTyTrans ; [ eapply EqTySubstHom | .. ].
        -- ceapply SubstZero. todo. (* Same again *)
        -- todo. (* Repeat *)
        -- todo. (* ... *)
        -- capply CongHom.
           ++ unfold Ttt.eqterm. pushsubst.
              all:todo. (* ... *)
           ++ unfold Ttt.eqterm. pushsubst.
              all:todo. (* ... *)
      * capply CtxExtend.
        apply TyHom.
        -- todo. (* ... *)
        -- todo. (* ... *)
    + rewrite trans_ctx_fxpath in h. assumption.
Qed.

Fixpoint sound_trans_ctx σ Γ (hσ : isfctx Γ σ) (H : Stt.isctx Γ) {struct H} :
  Ttt.isctx (trans_ctx σ Γ)

with sound_trans_subst σ ρ Γ Δ
  (hσ : isfctx Γ σ) (H : Stt.issubst ρ Γ Δ) {struct H} :
  { δ : fctx &
    isfctx Δ δ *
    Ttt.issubst (trans_subst σ ρ) (trans_ctx σ Γ) (trans_ctx δ Δ)
  }%type

with sound_trans_type σ Γ A (hσ : isfctx Γ σ) (H : Stt.istype Γ A) {struct H} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A)

with sound_trans_term σ Γ A u
  (hσ : isfctx Γ σ) (H : Stt.isterm Γ u A) {struct H} :
  Ttt.isterm (trans_ctx σ Γ) (trans_term σ u) ([[A]] σ)

with sound_trans_eqctx σ Γ Δ (hσ : isfctx Γ σ) (H : Stt.eqctx Γ Δ) {struct H} :
  Ttt.eqctx (trans_ctx σ Γ) (trans_ctx σ Δ)

with sound_trans_eqsubst σ ρ θ Γ Δ
  (hσ : isfctx Γ σ) (H : Stt.eqsubst ρ θ Γ Δ) {struct H} :
  { δ : fctx &
    isfctx Δ δ *
    Ttt.eqsubst (trans_subst σ ρ)
                (trans_subst σ θ)
                (trans_ctx σ Γ)
                (trans_ctx δ Δ)
  }%type

with sound_trans_eqtype σ Γ A B
  (hσ : isfctx Γ σ) (H : Stt.eqtype Γ A B) {struct H} :
  Ttt.eqtype (trans_ctx (fxpath σ) Γ) (trans_type σ A) (trans_type σ B)

with sound_trans_eqterm σ Γ A u v
  (hσ : isfctx Γ σ) (H : Stt.eqterm Γ u v A) {struct H} :
  Ttt.eqterm (trans_ctx σ Γ) (trans_term σ u) (trans_term σ u) (trans_type σ A).
Proof.
  (* sound_trans_ctx *)
  - { dependent destruction H ; doConfig.

      (* CtxEmpty *)
      - dependent induction hσ.

        + simpl. capply CtxExtend.
          ceapply Tyℙ.
          capply CtxEmpty.

        + simpl. capply CtxExtend.
          apply TyHom.
          * todo.
          * ceapply TermTyConv ; [ capply TermVarZero | .. ].
            -- todo.
            -- todo.

      (* CtxExtend *)
      - dependent induction hσ.

        + simpl. capply CtxExtend.
          apply sound_trans_type''.
          apply sound_trans_type ; assumption.

        + simpl. capply CtxExtend.
          apply TyHom.
          * todo.
          * ceapply TermTyConv ; [ capply TermVarZero | .. ].
            -- todo.
            -- todo.
    }

  (* sound_trans_subst *)
  - { dependent destruction H ; doConfig.

      (* SubstZero *)
      - todo.

      (* SubstWeak *)
      - todo.

      (* SubstShift *)
      - todo.

      (* SubstId *)
      - todo.

      (* SubstComp *)
      - todo.

      (* SubstCtxConv *)
      - todo.
    }

  (* sound_trans_type *)
  - { dependent destruction H ; doConfig ; rewrite trans_ctx_fxpath.

      (* TyCtxConv *)
      - ceapply TyCtxConv.
        + apply @sound_trans_type with (Γ := G).
          * eapply isfctx_conv ; eassumption.
          * assumption.
        + rewrite trans_ctx_fxpath.
          capply EqCtxExtend.
          * capply EqCtxExtend.
            -- apply sound_trans_eqctx.
               ++ eapply isfctx_conv ; eassumption.
               ++ assumption.
            -- capply EqTyRefl.
               ceapply Tyℙ.
               apply sound_trans_ctx.
               ++ eapply isfctx_conv ; eassumption.
               ++ assumption.
          * capply EqTyRefl.
            apply TyHom.
            -- todo.
            -- todo.

      (* TySubst *)
      - simpl.
        assert (hxσ : isfctx G (fxpath σ)).
        { apply valid_fxpath. assumption. }
        destruct (sound_trans_subst (fxpath σ) sbs G D hxσ i) as [δ [hδ ?] ].
        ceapply TySubst.
        + ceapply SubstCtxConv ; [ eapply i2 | .. ].
          * rewrite trans_ctx_fxpath.
            capply CtxRefl. todo.
          * ceapply CtxRefl.
            apply (ett_sanity.sane_issubst _ _ _ i2).
        + (* apply sound_trans_type'. *)
          (* Mismatch between δ and (fxpath σ), maybe the translation is
             wrong in this case, maybe we need to have δ as the result of
             a function. *)
          todo.

      (* TyProd *)
      - simpl. capply TyProd.
        ceapply TyCtxConv ; [ eapply sound_trans_type' | .. ].
        + apply sound_trans_type.
          * apply valid_fxvar. apply valid_fxpath. exact hσ.
          * exact H.
        + rewrite trans_ctx_fxvar.
          rewrite trans_ctx_fxpath.
          capply CtxRefl. capply CtxExtend.
          ceapply TyCtxConv ; [ eapply sound_trans_type'' | .. ].
          * eapply sound_trans_type.
            -- eapply valid_fxpath. eassumption.
            -- assumption.
          * rewrite trans_ctx_fxpath. capply CtxRefl.
            capply CtxExtend. apply TyHom.
            -- todo.
            -- todo.

      (* TyId *)
      - simpl. capply TyId.
        + assert (hσ' : isfctx G (fxpath σ)).
          { apply valid_fxpath. assumption. }
          pose (sound_trans_term _ _ _ _ hσ' i1).
          (* pose (sound_trans_term' i3). *)
          (* rewrite trans_ctx_fxpath in i4. *)
          (* todo. (* Mismatch again... *) *)
          rewrite trans_ctx_fxpath in i3.
          assumption.
        + assert (hσ' : isfctx G (fxpath σ)).
          { apply valid_fxpath. assumption. }
          pose (sound_trans_term _ _ _ _ hσ' i2).
          rewrite trans_ctx_fxpath in i3.
          assumption.

      (* TyUni *)
      - simpl. (* Maybe we should deduce something for fProd? *)
        unfold fProd.
        capply TyProd. capply TyProd. capply TyUni.
        capply CtxExtend.
        apply TyHom.
        + todo.
        + todo.

      (* TyEL *)
      - simpl.
        ceapply TyEl.
        assert (hσ' : isfctx G (fxpath σ)).
        { apply valid_fxpath. assumption. }
        pose (h' := sound_trans_term _ _ _ _ hσ' i).
        rewrite trans_ctx_fxpath in h'.
        ceapply TermTyConv ; [ exact h' | .. ].
        simpl. (* compsubst. *)
        (* + capply SubstZero. apply hidℙ'. todo. *)
        (* + todo. *)
        (* +  *)
        todo. (* I believe in it. *)
    }

  (* sound_trans_term *)
  - { dependent destruction H ; doConfig.

      (* TermTyConv *)
      - pose (ih := sound_trans_term _ _ _ _ hσ H).
        ceapply TermTyConv.
        + apply ih.
        + apply sound_trans_eqtype'.
          apply sound_trans_eqtype ; assumption.

      (* TermCtxConv *)
      - pose (hσ' := isfctx_conv hσ _ e).
        pose (ih := sound_trans_term _ _ _ _ hσ' H).
        ceapply TermCtxConv.
        + apply ih.
        + apply sound_trans_eqctx ; assumption.

      (* TermSubst *)
      - todo. (* Need the corresponding translation *)

      (* TermVarZero *)
      - simpl. (* ceapply TermApp. *)
        (* Won't we have trouble with the lack of typing information
           when translating variables? *)
        todo.

      (* TermVarSucc *)
      - todo.

      (* TermAbs *)
      - simpl. ceapply TermTyConv.
        + ceapply TermAbs.
          assert (hσ' : isfctx (ctxextend G A) (fxvar σ)).
          { apply valid_fxvar. assumption. }
          pose (sound_trans_term _ _ _ _ hσ' H).
          rewrite trans_ctx_fxvar in i2. assumption.
        + todo. (* Not sure it holds... *)

      (* TermApp *)
      - simpl. ceapply TermTyConv.
        + ceapply TermApp.
          * pose (ih := sound_trans_term _ _ _ _ hσ H).
            simpl in ih.
            (* Same conversion problem! *)
            todo.
          * todo.
        + todo.

      - todo.

      - todo.

      - todo.

      - todo.

      - todo.

      - todo.
    }

  (* sound_trans_eqctx *)
  - { dependent destruction H ; doConfig.

      (* CtxRefl *)
      - capply CtxRefl. now apply sound_trans_ctx.

      (* CtxSym *)
      - capply CtxSym. apply sound_trans_eqctx.
        + eapply isfctx_conv ; eassumption.
        + assumption.

      (* CtxTrans *)
      - ceapply CtxTrans.
        + eapply sound_trans_eqctx ; eassumption.
        + apply sound_trans_eqctx.
          * eapply isfctx_conv.
            -- eassumption.
            -- (* Sanity and then symmetry *)
               todo.
          * assumption.

      (* EqCtxEmpty *)
      - capply CtxRefl. apply sound_trans_ctx.
        + assumption.
        + capply CtxEmpty.

      (* EqCtxExtend *)
      - dependent induction hσ.
        + simpl. capply EqCtxExtend.
          * apply sound_trans_eqctx ; assumption.
          * todo. (* Need sound_trans_eq[[]] *)
        + simpl. capply EqCtxExtend.
          * capply EqCtxExtend.
            -- (* This feels dangerous! *)
               apply IHhσ ; try assumption.
               reflexivity.
            -- todo.
          * capply EqTyRefl. todo.
    }

  (* sound_trans_eqsubst *)
  - todo.

  (* sound_trans_eqtype *)
  - todo.

  (* sound_trans_eqterm *)
  - todo.
Defined.

End Translation.

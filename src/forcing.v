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
Context `{_Hom : term}.
Context `{
  hHom :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ _Hom (Arrow (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))
}.

Definition Hom p q :=
  El (app (app _Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) p)
          (El ℙ)
          (Uni (uni 0))
          q).

Context `{_idℙ : term}.
Context `{
  hidℙ :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ _idℙ (Prod (El ℙ) (Hom (var 0) (var 0)))
}.

Definition idℙ p :=
  app _idℙ (El ℙ) (Hom (var 0) (var 0)) p.

Context `{_comp : term}.
Context `{
  hcomp :
    forall {Γ},
      Ttt.isctx Γ ->
      Ttt.isterm Γ
                 _comp
                 (Prod (El ℙ)
                       (Prod (El ℙ)
                             (Prod (El ℙ)
                                   (Arrow (Hom (var 2) (var 1))
                                          (Arrow (Hom (var 1) (var 0))
                                                 (Hom (var 2) (var 0)))))))
}.

Definition comp p q r f g :=
  app (app (app (app (app _comp
                          (El ℙ)
                          (Prod (El ℙ)
                                (Arrow (Hom (var 2) (var 1))
                                       (Arrow (Hom (var 1) (var 0))
                                              (Hom (var 2) (var 0)))))
                          p)
                     (El ℙ)
                     (Prod (El ℙ)
                           (Arrow (Hom p (var 1))
                                  (Arrow (Hom (var 1) (var 0))
                                         (Hom p (var 0)))))
                     q)
                (El ℙ)
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
                 (Arrow (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))
}.

Axiom todo : forall {A}, A.
Ltac todo := apply todo.

Lemma EqTySubstℙ :
  forall {Γ Δ ρ},
    Ttt.issubst ρ Γ Δ ->
    Ttt.eqtype Γ (Subst (El ℙ) ρ) (El ℙ).
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
    Ttt.isterm Δ u (El ℙ) ->
    Ttt.isterm Δ v (El ℙ) ->
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

Lemma TyHom :
  forall {Γ u v},
    Ttt.isterm Γ u (El ℙ) ->
    Ttt.isterm Γ v (El ℙ) ->
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
    Ttt.eqterm Γ u1 u2 (El ℙ) ->
    Ttt.eqterm Γ v1 v2 (El ℙ) ->
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
    Ttt.isterm Γ x (El ℙ) ->
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

(* Morphism of a variable *)
(* Fixpoint morph (σ : fctx) (x : nat) : term := *)
(*   match σ, x with *)
(*   | cond, _ => (idℙ (var o)) *)
(*   | fxvar σ, 0 => (idℙ (last_cond σ)) *)
(*   | fxvar σ, (S x) => morph σ x *)
(*   | fxpath σ, x => comp ? ? ? (morph σ x (* ?? x-1 we'd like, no? *)) (var 0). *)
(*                       (* maybe not var 0, but rather an offset? *) *)

Fixpoint lift_var (σ : fctx) (x : nat) : nat :=
  match σ, x with
  | cond, _ => 0 (* This case doesn't happend with well-typed things *)
  | fxvar σ, 0 => 0
  | fxvar σ, S x => S (lift_var σ x)
  | fxpath σ, x => S (S (lift_var σ x))
  end.

(* Translation *)

Reserved Notation "[[ A ]] σ" (at level 5).
Reserved Notation "[ u ]! σ" (at level 5).
Reserved Notation "[[ A ]]! σ" (at level 5).

Definition flam (σ : fctx) (u : term) : term :=
  lam (El ℙ) todo (lam (Hom (var (S (last_cond σ))) (var 0)) todo u).

Definition fProd (σ : fctx) (A : type) : type :=
  Prod (El ℙ) (Prod (Hom (var (S (last_cond σ))) (var 0)) A).

Fixpoint trans_type (σ : fctx) (A : type) {struct A} : type :=
  match A with
  | Prod A B => Prod ([[ A ]]! (fxpath σ)) ([[ B ]] (fxvar (fxpath σ)))

  | Id A u v => Id ([[ A ]] (fxpath σ)) ([ u ]! (fxpath σ)) ([ v ]! (fxpath σ))

  | Subst A ρ => Subst ([[ A ]] (fxpath σ)) (trans_subst (fxpath σ) ρ)

  | Uni l => fProd (fxpath σ) (Uni l)

  | El a => El (trans_term σ a)

  (* Cases that don't happen given our config *)
  | _ => Empty

  end

with trans_term (σ : fctx) (u : term) {struct u} : term :=
  match u with
  | var n => var (lift_var σ n)

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
                         (sbzero (El ℙ)
                                 (var (last_cond σ)))))
         (sbzero (Hom (var (last_cond σ)) (var (last_cond σ)))
                 (idℙ (var (last_cond σ)))))

and "[ u ]! σ" := (flam σ (trans_term (fxpath σ) u))

and "[[ A ]]! σ" := (fProd σ (trans_type (fxpath σ) A)).

Fixpoint trans_ctx (σ : fctx) (Γ : context) : context :=
  match Γ, σ with
  | ctxempty, cond =>
    ctxextend ctxempty (El ℙ)

  | Γ, fxpath σ =>
    ctxextend (ctxextend (trans_ctx σ Γ) (El ℙ))
              (Hom (var (S (last_cond σ))) (var 0))

  | ctxextend Γ A, fxvar σ =>
    ctxextend (trans_ctx σ Γ) ([[A]] σ)

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
    ctxextend (ctxextend (trans_ctx σ Γ) (El ℙ))
              (Hom (var (S (last_cond σ))) (var 0)).
Proof.
  intros Γ σ.
  destruct Γ.
  - simpl. reflexivity.
  - simpl. reflexivity.
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


Fixpoint sound_trans_ctx σ Γ (hσ : isfctx Γ σ) (H : Stt.isctx Γ) {struct H} :
  Ttt.isctx (trans_ctx σ Γ)

with sound_trans_subst σ δ ρ Γ Δ
  (hσ : isfctx Γ σ) (hδ : isfctx Δ δ) (H : Stt.issubst ρ Γ Δ) {struct H} :
  Ttt.issubst (trans_subst σ ρ) (trans_ctx σ Γ) (trans_ctx δ Δ)

with sound_trans_type σ Γ A (hσ : isfctx Γ σ) (H : Stt.istype Γ A) {struct H} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A)

with sound_trans_term σ Γ A u
  (hσ : isfctx Γ σ) (H : Stt.isterm Γ u A) {struct H} :
  Ttt.isterm (trans_ctx σ Γ) (trans_term σ u) (trans_type σ A)

with sound_trans_eqctx σ Γ Δ (hσ : isfctx Γ σ) (H : Stt.eqctx Γ Δ) {struct H} :
  Ttt.eqctx (trans_ctx σ Γ) (trans_ctx σ Δ)

with sound_trans_eqsubst σ δ ρ θ Γ Δ
  (hσ : isfctx Γ σ) (hδ : isfctx Δ δ) (H : Stt.eqsubst ρ θ Γ Δ) {struct H} :
  Ttt.eqsubst (trans_subst σ ρ) (trans_subst σ θ) (trans_ctx σ Γ) (trans_ctx δ Δ)

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
          ceapply TyEl. apply hℙ.
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
          todo. (* Need something for [[A]] σ typing. *)

        + simpl. capply CtxExtend.
          apply TyHom.
          * todo.
          * ceapply TermTyConv ; [ capply TermVarZero | .. ].
            -- todo.
            -- todo.
    }

  (* sound_trans_subst *)
  - todo.

  (* sound_trans_type *)
  - { dependent destruction H ; doConfig ; rewrite trans_ctx_fxpath.

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
               ceapply TyEl. apply hℙ.
               apply sound_trans_ctx.
               ++ eapply isfctx_conv ; eassumption.
               ++ assumption.
          * capply EqTyRefl.
            apply TyHom.
            -- todo.
            -- todo.

      (* - simpl. ceapply TySubst. *)
      (*   + ceapply SubstCtxConv ; [ eapply sound_trans_subst | .. ]. *)
      (*     * apply valid_fxpath. exact hσ. *)
      (*     * todo. (* We shouldn't habe to provide it. *) *)
      (*     * eassumption. *)
      (*     * rewrite trans_ctx_fxpath. *)
      (*       capply CtxRefl. todo. *)
      (*     * capply CtxRefl. todo. *)
      (*   + todo. (* Need something to deduce sound_trans_type scales to [[]] *) *)
      - todo.

      - simpl. capply TyProd.
        todo. (* Same need *)

      - simpl. capply TyId.
        + todo. (* Need sound_trans_term *)
        + todo. (* Same *)

      - simpl. (* Maybe we should deduce something for fProd? *)
        unfold fProd.
        capply TyProd. capply TyProd. capply TyUni.
        capply CtxExtend.
        apply TyHom.
        + todo.
        + todo.

      - simpl.
        (* ceapply TyEl. *)
        todo. (* We need sound_trans_term before we can fix the translation of
                 El. *)
    }

  (* sound_trans_term *)
  - { dependent destruction H ; doConfig.

      (* TermTyConv *)
      - pose (ih := sound_trans_term _ _ _ _ hσ H).
        ceapply TermTyConv.
        + apply ih.
        + todo. (* Need sound_trans_eqtype *)

      (* TermCtxConv *)
      - pose (hσ' := isfctx_conv hσ _ e).
        pose (ih := sound_trans_term _ _ _ _ hσ' H).
        ceapply TermCtxConv.
        + apply ih.
        + todo. (* Need sound_trans_eqctx *)

      (* TermSubst *)
      - todo. (* Need the corresponding translation *)

      (* TermVarZero *)
      - todo. (* Incomplete translation. *)

      (* TermVarSucc *)
      - todo.

      - todo.

      - todo.

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

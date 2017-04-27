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

  (* Case that don't happen given our config *)
  | _ => Empty

  end

with trans_term (σ : fctx) (u : term) {struct u} : term :=
  match u with
  | _ => todo
  end

with trans_subst (σ : fctx) (ρ : substitution) {struct ρ} : substitution :=
  match ρ with
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

Fixpoint sound_trans_type σ Γ A (hσ : isfctx Γ σ) (H : Stt.istype Γ A) {struct H} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A).
Proof.
  (* sound_trans_type *)
  - { dependent destruction H ; doConfig ; rewrite trans_ctx_fxpath.

      - ceapply TyCtxConv.
        + apply @sound_trans_type with (Γ := G).
          * todo. (* Need lemma *)
          * assumption.
        + rewrite trans_ctx_fxpath.
          capply EqCtxExtend.
          * capply EqCtxExtend.
            -- todo. (* Need sound_trans_eqctx *)
            -- capply EqTyRefl.
               ceapply TyEl. apply hℙ.
               todo. (* Need sound_trans_ctx *)
          * capply EqTyRefl. todo.

      - simpl. config eapply @TySubst with (D := D).
        + todo. (* Need sound_trans_subst *)
        + todo. (* Need something to deduce sound_trans_type scales to [[]] *)

      - simpl. capply TyProd.
        todo. (* Same need *)

      - simpl. capply TyId.
        + todo. (* Need sound_trans_term *)
        + todo. (* Same *)

      - simpl. todo. (* Something for fProd? *)

      - todo.

      - todo.

      - todo.

      - todo.

      - todo.
    }
Defined.

(** OLD BELOW **)

Fixpoint isctx_trans_empty {σ} (h : isfctx ctxempty σ) {struct h} :
  Ttt.isctx (trans_ctx σ ctxempty)

with isterm_last_cond {σ Γ} (h : isfctx Γ σ) {struct h} :
  Ttt.isctx Γ ->
  Ttt.isterm (trans_ctx σ Γ) (var (last_cond σ)) (El ℙ).
Proof.
  (* isctx_trans_empty *)
  - { dependent destruction h.

      - simpl. capply CtxExtend.
        ceapply TyEl. apply hℙ.
        capply CtxEmpty.

      - pose (IHh := isctx_trans_empty σ h).
        simpl. capply CtxExtend.
        ceapply TyEl.
        ceapply TermTyConv ; [ ceapply TermApp | .. ].
        + ceapply TermTyConv ; [ ceapply TermApp | .. ].
          * ceapply TermTyConv ; [ apply hHom | .. ].
            -- capply CtxExtend.
               ceapply TyEl. apply hℙ.
               now apply IHh.
            -- assert (
                   Ttt.isterm (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                              ℙ
                              (Uni (uni 0))
                 ).
               { apply hℙ. capply CtxExtend.
                 ceapply TyEl. apply hℙ.
                 now apply IHh.
               }
               unfold Arrow.
               capply CongProd.
               ++ capply EqTyRefl.
                  ceapply TyEl. apply hℙ.
                  capply CtxExtend.
                  ceapply TyEl. apply hℙ.
                  now apply IHh.
               ++ pushsubst.
                  ** magic.
                  ** ceapply TySubst.
                     --- capply SubstWeak.
                         ceapply TyEl. apply hℙ.
                         capply CtxExtend.
                         ceapply TyEl. apply hℙ.
                         now apply IHh.
                     --- capply TyUni.
                         capply CtxExtend.
                         ceapply TyEl. apply hℙ.
                         now apply IHh.
                  ** capply CongProd.
                     --- eapply EqTySubstℙ.
                         capply SubstWeak.
                         ceapply TyEl. apply hℙ.
                         capply CtxExtend.
                         ceapply TyEl. apply hℙ.
                         now apply IHh.
                     --- pushsubst.
                         +++ magic.
                         +++ magic.
                         +++ capply EqTyRefl. magic.
                         +++ pushsubst.
                             *** magic.
                             *** pushsubst.
                                 ---- ceapply SubstCtxConv ; [
                                        ceapply SubstWeak
                                      | ..
                                      ].
                                      ++++ ceapply TyEl. apply hℙ.
                                           shelve.
                                      ++++ ceapply EqCtxExtend.
                                           **** capply CtxRefl.
                                                capply CtxExtend.
                                                ceapply TyEl. apply hℙ.
                                                capply CtxExtend.
                                                ceapply TyEl. apply hℙ.
                                                now apply IHh.
                                           **** capply EqTySym.
                                                eapply EqTySubstℙ.
                                                capply SubstWeak.
                                                ceapply TyEl. apply hℙ.
                                                capply CtxExtend.
                                                ceapply TyEl. apply hℙ.
                                                now apply IHh.
                                      ++++ capply CtxRefl.
                                           capply CtxExtend.
                                           ceapply TyEl. apply hℙ.
                                           capply CtxExtend.
                                           ceapply TyEl. apply hℙ.
                                           now apply IHh.
                                 ---- capply EqTyRefl.
                                      magic.
          * ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
            -- apply isterm_last_cond.
               ++ assumption.
               ++ capply CtxEmpty.
            -- ceapply TyEl. apply hℙ.
               now apply IHh.
            -- eapply EqTySubstℙ.
               capply SubstWeak.
               ceapply TyEl. apply hℙ.
               now apply IHh.
          * pushsubst.
            -- capply SubstZero.
               ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
               ++ apply isterm_last_cond.
                  ** assumption.
                  ** capply CtxEmpty.
               ++ ceapply TyEl. apply hℙ.
                  now apply IHh.
               ++ eapply EqTySubstℙ.
                  capply SubstWeak.
                  ceapply TyEl. apply hℙ.
                  now apply IHh.
            -- ceapply TySubst.
               ++ capply SubstWeak.
                  ceapply TyEl. apply hℙ.
                  capply CtxExtend.
                  ceapply TyEl. apply hℙ.
                  capply CtxExtend.
                  ceapply TyEl. apply hℙ.
                  now apply IHh.
               ++ capply TyUni.
                  capply CtxExtend.
                  ceapply TyEl. apply hℙ.
                  capply CtxExtend.
                  ceapply TyEl. apply hℙ.
                  now apply IHh.
            -- capply CongProd.
               ++ eapply EqTySubstℙ.
                  capply SubstZero.
                  ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
                  ** apply isterm_last_cond.
                     --- assumption.
                     --- capply CtxEmpty.
                  ** ceapply TyEl. apply hℙ.
                     now apply IHh.
                  ** eapply EqTySubstℙ.
                     capply SubstWeak.
                     ceapply TyEl. apply hℙ.
                     now apply IHh.
               ++ pushsubst.
                  ** ceapply SubstShift.
                     --- capply SubstZero.
                         ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
                         +++ apply isterm_last_cond ; [ assumption | .. ].
                             capply CtxEmpty.
                         +++ ceapply TyEl. apply hℙ.
                             now apply IHh.
                         +++ eapply EqTySubstℙ.
                             capply SubstWeak.
                             ceapply TyEl. apply hℙ.
                             now apply IHh.
                     --- ceapply TyEl. apply hℙ.
                         capply CtxExtend.
                         ceapply TyEl. apply hℙ.
                         capply CtxExtend.
                         ceapply TyEl. apply hℙ.
                         now apply IHh.
                  ** capply SubstWeak.
                     ceapply TyEl. apply hℙ.
                     capply CtxExtend.
                     ceapply TyEl. apply hℙ.
                     capply CtxExtend.
                     ceapply TyEl. apply hℙ.
                     now apply IHh.
                  ** capply EqTyRefl.
                     capply TyUni.
                     capply CtxExtend.
                     ceapply TyEl. apply hℙ.
                     capply CtxExtend.
                     ceapply TyEl. apply hℙ.
                     capply CtxExtend.
                     ceapply TyEl. apply hℙ.
                     now apply IHh.
                  ** pushsubst.
                     --- ceapply SubstShift.
                         +++ capply SubstZero.
                             ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
                             *** apply isterm_last_cond ; [ assumption | .. ].
                                 capply CtxEmpty.
                             *** ceapply TyEl. apply hℙ.
                                 now apply IHh.
                             *** eapply EqTySubstℙ.
                                 capply SubstWeak.
                                 ceapply TyEl. apply hℙ.
                                 now apply IHh.
                         +++ ceapply TyEl. apply hℙ.
                             capply CtxExtend.
                             ceapply TyEl. apply hℙ.
                             capply CtxExtend.
                             ceapply TyEl. apply hℙ.
                             now apply IHh.
                     --- capply EqTyRefl.
                         capply TyUni.
                         capply CtxExtend.
                         ceapply TySubst.
                         +++ ceapply SubstZero.
                             ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
                             *** apply isterm_last_cond ; [ assumption | .. ].
                                 capply CtxEmpty.
                             *** ceapply TyEl. apply hℙ.
                                 now apply IHh.
                             *** eapply EqTySubstℙ.
                                 capply SubstWeak.
                                 ceapply TyEl. apply hℙ.
                                 now apply IHh.
                         +++ ceapply TyEl. apply hℙ.
                             capply CtxExtend.
                             ceapply TyEl. apply hℙ.
                             capply CtxExtend.
                             ceapply TyEl. apply hℙ.
                             now apply IHh.
        + ceapply TermTyConv ; [ ceapply TermVarZero | .. ].
          * ceapply TyEl. apply hℙ.
            now apply IHh.
          * ceapply EqTySubstℙ.
            capply SubstWeak.
            ceapply TyEl. apply hℙ.
            now apply IHh.
        + pushsubst.
          * capply SubstZero.
            ceapply TermTyConv ; [ ceapply TermVarZero | .. ].
            -- ceapply TyEl. apply hℙ.
               now apply IHh.
            -- ceapply EqTySubstℙ.
               capply SubstWeak.
               ceapply TyEl. apply hℙ.
               now apply IHh.
          * capply EqTyRefl.
            ceapply TyUni.
            capply CtxExtend.
            ceapply TyEl. apply hℙ.
            now apply IHh.
            Unshelve.
            capply CtxExtend.
            ceapply TyEl. apply hℙ.
            capply CtxExtend.
            ceapply TyEl. apply hℙ.
            now apply IHh.
    }

  (* isterm_last_cond *)
  - { dependent destruction h ; intro hΓ.

      - unfold last_cond. simpl.
        ceapply TermTyConv ; [ ceapply TermVarZero | .. ].
        + ceapply TyEl. apply hℙ.
          capply CtxEmpty.
        + eapply EqTySubstℙ.
          capply SubstWeak.
          ceapply TyEl. apply hℙ.
          capply CtxEmpty.

      - rewrite @last_cond_var with (Γ := Γ) ; [ .. | exact h ].
        unfold last_cond. simpl.
        ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
        + apply isterm_last_cond.
          * assumption.
          * todo. (* Inversion *)
        + ceapply TySubst.
          * ceapply SubstZero. apply hidℙ'.
            apply isterm_last_cond.
            -- assumption.
            -- todo. (* Inversion *)
          * ceapply TySubst.
            -- todo. (*TODO*)
            -- todo.
        + todo.

      - rewrite trans_ctx_fxpath.
        unfold last_cond. simpl.
        ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
        + ceapply TermVarZero.
          ceapply TyEl. apply hℙ.
          (* now apply isctx_trans_empty. *)
          todo. (* Maybe we should prove all these statements
                   silmutaneuously. *)
        (* + ceapply TyEl. *)
(*           ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*           * ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*             -- ceapply TermTyConv ; [ apply hHom | .. ]. *)
(*                ++ capply CtxExtend. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*                ++ unfold Arrow. *)
(*                   capply CongProd. *)
(*                   ** capply EqTyRefl. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** pushsubst. *)
(*                      --- capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- ceapply TySubst. *)
(*                          +++ capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ capply TyUni. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                      --- capply CongProd. *)
(*                          +++ eapply EqTySubstℙ. *)
(*                              capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ pushsubst. *)
(*                              *** ceapply SubstShift. *)
(*                                  ---- capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** capply EqTyRefl. *)
(*                                  capply TyUni. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** pushsubst. *)
(*                                  ---- ceapply SubstShift. *)
(*                                       ++++ capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- pushsubst. *)
(*                                       ++++ ceapply SubstCtxConv ; [ *)
(*                                              ceapply SubstWeak *)
(*                                            | .. *)
(*                                            ]. *)
(*                                            Focus 2. *)
(*                                              ceapply EqCtxExtend. *)
(*                                              (**) *)
(*                                                capply CtxRefl. *)
(*                                                capply CtxExtend. *)
(*                                                ceapply TyEl. apply hℙ. *)
(*                                                capply CtxExtend. *)
(*                                                ceapply TyEl. apply hℙ. *)
(*                                                now apply isctx_trans_empty. *)
(*                                              (**) *)
(*                                                capply EqTySym. *)
(*                                                eapply EqTySubstℙ. *)
(*                                                capply SubstWeak. *)
(*                                                ceapply TyEl. apply hℙ. *)
(*                                                capply CtxExtend. *)
(*                                                ceapply TyEl. apply hℙ. *)
(*                                                now apply isctx_trans_empty. *)
(*                                            **** ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** capply CtxRefl. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                       ++++ capply EqTyRefl. *)
(*                                            capply TyUni. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TySubst. *)
(*                                            **** capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*             -- ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                ++ now apply isterm_last_cond. *)
(*                ++ ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*                ++ eapply EqTySubstℙ. *)
(*                   capply SubstWeak. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*             -- pushsubst. *)
(*                ++ capply SubstZero. *)
(*                   ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                   ** now apply isterm_last_cond. *)
(*                   ** ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ ceapply TySubst. *)
(*                   ** capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** capply TyUni. *)
(*                      capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ capply CongProd. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstZero. *)
(*                      ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                      --- now apply isterm_last_cond. *)
(*                      --- ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- eapply EqTySubstℙ. *)
(*                          capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                   ** pushsubst. *)
(*                      --- ceapply SubstShift. *)
(*                          +++ capply SubstZero. *)
(*                              ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                              *** now apply isterm_last_cond. *)
(*                              *** ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** eapply EqTySubstℙ. *)
(*                                  capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                      --- capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- capply EqTyRefl. *)
(*                          capply TyUni. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- pushsubst. *)
(*                          +++ ceapply SubstShift. *)
(*                              *** capply SubstZero. *)
(*                                  ceapply TermTyConv ; [ *)
(*                                    ceapply TermVarSucc *)
(*                                  | .. *)
(*                                  ]. *)
(*                                  ---- now apply isterm_last_cond. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- eapply EqTySubstℙ. *)
(*                                       capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ capply EqTyRefl. *)
(*                              capply TyUni. *)
(*                              capply CtxExtend. *)
(*                              ceapply TySubst. *)
(*                              *** capply SubstZero. *)
(*                                  ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                                  ---- now apply isterm_last_cond. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- eapply EqTySubstℙ. *)
(*                                       capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*           * ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*             -- ceapply TyEl. apply hℙ. *)
(*                now apply isctx_trans_empty. *)
(*             -- eapply EqTySubstℙ. *)
(*                capply SubstWeak. *)
(*                ceapply TyEl. apply hℙ. *)
(*                now apply isctx_trans_empty. *)
(*           * pushsubst. *)
(*             -- capply SubstZero. *)
(*                ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*                ++ ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*                ++ eapply EqTySubstℙ. *)
(*                   capply SubstWeak. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*             -- capply EqTyRefl. *)
(*                capply TyUni. *)
(*                capply CtxExtend. *)
(*                ceapply TyEl. apply hℙ. *)
(*                now apply isctx_trans_empty. *)
(*         + ceapply EqTyTrans ; [ *)
(*             ceapply CongTySubst ; [ ceapply SubstRefl | eapply EqTySubstℙ | .. ] *)
(*           | .. *)
(*           ]. *)
(*           * capply SubstWeak. *)
(*             ceapply TyEl. *)
(*             ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*             -- ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*                ++ ceapply TermTyConv ; [ apply hHom | .. ]. *)
(*                   ** capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** capply CongProd. *)
(*                      --- capply EqTyRefl. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- pushsubst. *)
(*                          +++ capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ ceapply TySubst. *)
(*                              *** capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** capply TyUni. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ capply CongProd. *)
(*                              *** eapply EqTySubstℙ. *)
(*                                  capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** pushsubst. *)
(*                                  ---- ceapply SubstShift. *)
(*                                       ++++ capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- capply EqTyRefl. *)
(*                                       capply TyUni. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- pushsubst. *)
(*                                       ++++ ceapply SubstShift. *)
(*                                            **** capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                       ++++ pushsubst. *)
(*                                            **** ceapply SubstCtxConv ; [ *)
(*                                                   ceapply SubstWeak *)
(*                                                 | ceapply EqCtxExtend ; [ *)
(*                                                     capply CtxRefl *)
(*                                                   | .. *)
(*                                                   ] *)
(*                                                 | .. *)
(*                                                 ]. *)
(*                                                 ----- ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply EqTySym. *)
(*                                                 eapply EqTySubstℙ. *)
(*                                                 ceapply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply CtxRefl. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** capply EqTyRefl. *)
(*                                                 capply TyUni. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TySubst. *)
(*                                                 ----- capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                ++ ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                   ** now apply isterm_last_cond. *)
(*                   ** ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ pushsubst. *)
(*                   ** capply SubstZero. *)
(*                      ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                      --- now apply isterm_last_cond. *)
(*                      --- ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- eapply EqTySubstℙ. *)
(*                          capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                   ** ceapply TySubst. *)
(*                      --- capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- capply TyUni. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                   ** capply CongProd. *)
(*                      --- eapply EqTySubstℙ. *)
(*                          capply SubstZero. *)
(*                          ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                          +++ now apply isterm_last_cond. *)
(*                          +++ ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ eapply EqTySubstℙ. *)
(*                              capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                      --- pushsubst. *)
(*                          +++ ceapply SubstShift. *)
(*                              *** capply SubstZero. *)
(*                                  ---- ceapply TermTyConv ; [ *)
(*                                         ceapply TermVarSucc *)
(*                                       | .. *)
(*                                       ]. *)
(*                                       ++++ now apply isterm_last_cond. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ eapply EqTySubstℙ. *)
(*                                            capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                              *** ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ capply EqTyRefl. *)
(*                              capply TyUni. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ pushsubst. *)
(*                              *** ceapply SubstShift. *)
(*                                  ---- ceapply SubstZero. *)
(*                                       ceapply TermTyConv ; [ *)
(*                                         ceapply TermVarSucc *)
(*                                       | .. *)
(*                                       ]. *)
(*                                       ++++ now apply isterm_last_cond. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ eapply EqTySubstℙ. *)
(*                                            capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** capply EqTyRefl. *)
(*                                  capply TyUni. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TySubst. *)
(*                                  ---- ceapply SubstZero. *)
(*                                       ceapply TermTyConv ; [ *)
(*                                         ceapply TermVarSucc *)
(*                                       | .. *)
(*                                       ]. *)
(*                                       ++++ now apply isterm_last_cond. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ eapply EqTySubstℙ. *)
(*                                            capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*             -- ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*                ++ ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*                ++ eapply EqTySubstℙ. *)
(*                   capply SubstWeak. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*             -- pushsubst. *)
(*                ++ capply SubstZero. *)
(*                   ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*                   ** ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ capply EqTyRefl. capply TyUni. *)
(*                   capply CtxExtend. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*           * capply SubstWeak. *)
(*             ceapply TyEl. apply hℙ. *)
(*             now apply isctx_trans_empty. *)
(*           * eapply EqTySubstℙ. *)
(*             capply SubstWeak. *)
(*             ceapply TyEl. *)
(*             ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*             -- ceapply TermTyConv ; [ ceapply TermApp | .. ]. *)
(*                ++ ceapply TermTyConv ; [ apply hHom | .. ]. *)
(*                   ** capply CtxExtend. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** capply CongProd. *)
(*                      --- capply EqTyRefl. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- pushsubst. *)
(*                          +++ capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ ceapply TySubst. *)
(*                              *** capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** capply TyUni. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ capply CongProd. *)
(*                              *** eapply EqTySubstℙ. *)
(*                                  capply SubstWeak. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                              *** pushsubst. *)
(*                                  ---- ceapply SubstShift. *)
(*                                       ++++ capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            capply CtxExtend. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- capply EqTyRefl. capply TyUni. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- pushsubst. *)
(*                                       ++++ ceapply SubstShift. *)
(*                                            **** capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                       ++++ pushsubst. *)
(*                                            **** ceapply SubstCtxConv ; [ *)
(*                                                   ceapply SubstWeak *)
(*                                                 | ceapply EqCtxExtend ; [ *)
(*                                                     capply CtxRefl *)
(*                                                   | .. *)
(*                                                   ] *)
(*                                                 | .. *)
(*                                                 ]. *)
(*                                                 ----- ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply EqTySym. *)
(*                                                 eapply EqTySubstℙ. *)
(*                                                 ***** capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- capply CtxRefl. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                            **** capply EqTyRefl. *)
(*                                                 capply TyUni. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TySubst. *)
(*                                                 ----- capply SubstWeak. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                                                 ----- ceapply TyEl. apply hℙ. *)
(*                                                 capply CtxExtend. *)
(*                                                 ceapply TyEl. apply hℙ. *)
(*                                                 now apply isctx_trans_empty. *)
(*                ++ ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                   ** now apply isterm_last_cond. *)
(*                   ** ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ pushsubst. *)
(*                   ** capply SubstZero. *)
(*                      ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                      --- now apply isterm_last_cond. *)
(*                      --- ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- eapply EqTySubstℙ. *)
(*                          capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                   ** ceapply TySubst. *)
(*                      --- capply SubstWeak. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                      --- capply TyUni. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          capply CtxExtend. *)
(*                          ceapply TyEl. apply hℙ. *)
(*                          now apply isctx_trans_empty. *)
(*                   ** capply CongProd. *)
(*                      eapply EqTySubstℙ. *)
(*                      --- ceapply SubstZero. *)
(*                          ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]. *)
(*                          +++ now apply isterm_last_cond. *)
(*                          +++ ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ eapply EqTySubstℙ. *)
(*                              capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                      --- pushsubst. *)
(*                          +++ ceapply SubstShift. *)
(*                              *** ceapply SubstZero. *)
(*                                  ceapply TermTyConv ; [ *)
(*                                    ceapply TermVarSucc *)
(*                                  | .. *)
(*                                  ]. *)
(*                                  ---- now apply isterm_last_cond. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                                  ---- eapply EqTySubstℙ. *)
(*                                       capply SubstWeak. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TyEl. apply hℙ. *)
(*                                  now apply isctx_trans_empty. *)
(*                          +++ capply SubstWeak. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ capply EqTyRefl. capply TyUni. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              capply CtxExtend. *)
(*                              ceapply TyEl. apply hℙ. *)
(*                              now apply isctx_trans_empty. *)
(*                          +++ pushsubst. *)
(*                              *** ceapply SubstShift. *)
(*                                  ---- capply SubstZero. *)
(*                                       ceapply TermTyConv ; [ *)
(*                                         ceapply TermVarSucc *)
(*                                       | .. *)
(*                                       ]. *)
(*                                       ++++ now apply isterm_last_cond. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ eapply EqTySubstℙ. *)
(*                                            capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*                              *** capply EqTyRefl. capply TyUni. *)
(*                                  capply CtxExtend. *)
(*                                  ceapply TySubst. *)
(*                                  ---- capply SubstZero. *)
(*                                       ceapply TermTyConv ; [ *)
(*                                         ceapply TermVarSucc *)
(*                                       | .. *)
(*                                       ]. *)
(*                                       ++++ now apply isterm_last_cond. *)
(*                                       ++++ ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                       ++++ eapply EqTySubstℙ. *)
(*                                            capply SubstWeak. *)
(*                                            ceapply TyEl. apply hℙ. *)
(*                                            now apply isctx_trans_empty. *)
(*                                  ---- ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       capply CtxExtend. *)
(*                                       ceapply TyEl. apply hℙ. *)
(*                                       now apply isctx_trans_empty. *)
(*             -- ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*                ++ ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*                ++ eapply EqTySubstℙ. *)
(*                   capply SubstWeak. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*             -- pushsubst. *)
(*                ++ capply SubstZero. *)
(*                   ceapply TermTyConv ; [ ceapply TermVarZero | .. ]. *)
(*                   ** ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                   ** eapply EqTySubstℙ. *)
(*                      capply SubstWeak. *)
(*                      ceapply TyEl. apply hℙ. *)
(*                      now apply isctx_trans_empty. *)
(*                ++ capply EqTyRefl. capply TyUni. *)
(*                   capply CtxExtend. *)
(*                   ceapply TyEl. apply hℙ. *)
(*                   now apply isctx_trans_empty. *)
(*     } *)
(* Defined. *)
Abort.

Fixpoint sound_trans_ctx σ Γ (hσ : isfctx Γ σ) (H : Stt.isctx Γ) {struct hσ} :
  Ttt.isctx (trans_ctx σ Γ).
Proof.
  destruct H.

  (* CtxEmpty *)
  - { dependent destruction hσ.

      (* valid_cond *)
      - simpl. capply CtxExtend.
        ceapply TyEl.
        apply hℙ.
        capply CtxEmpty.

      (* valid_fxpath *)
      - assert (Ttt.isctx (trans_ctx σ ctxempty)).
        { now apply isctx_trans_empty. }
        assert (Ttt.istype (trans_ctx σ ctxempty) (El ℙ)).
        { ceapply TyEl. apply hℙ. assumption. }
        assert (Ttt.isctx (ctxextend (trans_ctx σ ctxempty) (El ℙ))).
        { capply CtxExtend. assumption. }
        assert (
          Ttt.istype (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ)
        ).
        { ceapply TyEl. apply hℙ. assumption. }
        assert (
          Ttt.eqtype (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                     (El ℙ) (El ℙ)
        ).
        { capply EqTyRefl. assumption. }
        assert (
          Ttt.issubst
            (sbweak (El ℙ))
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
        ).
        { capply SubstWeak. assumption. }
        assert (
          Ttt.istype (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                     (Uni (uni 0))
        ).
        { capply TyUni. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (Subst (Uni (uni 0)) (sbweak (El ℙ)))
        ).
        { ceapply TySubst ; eassumption. }
        assert (
          Ttt.eqtype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (Subst (El ℙ) (sbweak (El ℙ)))
            (El ℙ)
        ).
        { eapply EqTySubstℙ ; eassumption. }
        assert (
          Ttt.issubst
            (sbshift (El ℙ) (sbweak (El ℙ)))
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (Subst (El ℙ) (sbweak (El ℙ))))
            (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                  (El ℙ))
                       (El ℙ))
        ).
        { ceapply SubstShift ; assumption. }
        assert (
          Ttt.isctx
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
        ).
        { capply CtxExtend. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (Uni (uni 0))
        ).
        { capply TyUni. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (El ℙ)
        ).
        { ceapply TyEl. apply hℙ. assumption. }
        assert (
          Ttt.eqtype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (El ℙ)
            (Subst (El ℙ) (sbweak (El ℙ)))
        ).
        { ceapply EqTySym. assumption. }
        assert (
          Ttt.issubst
            (sbweak (El ℙ))
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (Subst (El ℙ) (sbweak (El ℙ))))
            (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                  (El ℙ))
                       (El ℙ))
        ).
        { ceapply SubstCtxConv ; [
            ceapply SubstWeak
          | ceapply EqCtxExtend ; [
              ceapply CtxRefl
            | ..
            ]
          | capply CtxRefl
          ] ; assumption.
        }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (Subst (El ℙ) (sbweak (El ℙ)))
        ).
        { ceapply TySubst ; eassumption. }
        assert (
          Ttt.isctx
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (Subst (El ℙ) (sbweak (El ℙ))))
        ).
        { capply CtxExtend. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (Subst (El ℙ) (sbweak (El ℙ)))) (Uni (uni 0))
        ).
        { capply TyUni. assumption. }
        assert (
          Ttt.eqtype
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (Subst (El ℙ) (sbweak (El ℙ))))
            (Subst (Subst (Uni (uni 0)) (sbweak (El ℙ)))
                   (sbshift (El ℙ) (sbweak (El ℙ))))
            (Subst (Uni (uni 0)) (sbweak (El ℙ)))
        ).
        { unfold Ttt.eqtype. pushsubst.
          - eassumption.
          - eassumption.
          - capply EqTyRefl. assumption.
          - pushsubst.
            + eassumption.
            + pushsubst.
              * eassumption.
              * capply EqTyRefl. assumption.
        }
        assert (
          Ttt.eqtype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
            (Subst (Arrow (El ℙ) (Uni (uni 0))) (sbweak (El ℙ)))
            (Arrow (El ℙ) (Uni (uni 0)))
        ).
        { unfold Ttt.eqtype. pushsubst.
          - eassumption.
          - assumption.
          - capply CongProd.
            + assumption.
            + assumption.
        }
        assert (
          Ttt.eqtype (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                     (Arrow (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))
                     (Prod (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))
        ).
        { capply CongProd.
          - assumption.
          - assumption.
        }
        assert (
          Ttt.isterm (trans_ctx σ ctxempty) (var (last_cond σ)) (El ℙ)
        ).
        { now apply isterm_last_cond. }
        assert (
          Ttt.issubst (sbweak (El ℙ))
                      (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                      (trans_ctx σ ctxempty)
        ).
        { capply SubstWeak. assumption. }
        assert (
          Ttt.eqtype
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (Subst (El ℙ) (sbweak (El ℙ)))
            (El ℙ)
        ).
        { eapply EqTySubstℙ. eassumption. }
        assert (
          Ttt.isterm
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (var (S (last_cond σ)))
            (El ℙ)
        ).
        { ceapply TermTyConv ; [ ceapply TermVarSucc | .. ] ; eassumption. }
        assert (
          Ttt.issubst
            (sbzero (El ℙ) (var (S (last_cond σ))))
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ)) (El ℙ))
        ).
        { capply SubstZero. assumption. }
        assert (
          Ttt.issubst
            (sbweak (El ℙ))
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (El ℙ))
            (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                  (El ℙ))
                       (El ℙ))
        ).
        { capply SubstWeak. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (El ℙ))
            (Subst (Uni (uni 0)) (sbweak (El ℙ)))
        ).
        { ceapply TySubst ; eassumption. }
        assert (
          Ttt.eqtype
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (Subst (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ)))))
            (El ℙ)
        ).
        { eapply EqTySubstℙ. eassumption. }
        assert (
          Ttt.issubst
            (sbshift (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ)))))
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                       (Subst (El ℙ)
                              (sbzero (El ℙ) (var (S (last_cond σ))))
            ))
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                                  (El ℙ)) (El ℙ))
        ).
        { ceapply SubstShift ; assumption. }
        assert (
          Ttt.isctx
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty)
                                             (El ℙ))
                                  (El ℙ))
                       (El ℙ))
        ).
        { capply CtxExtend. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                                  (El ℙ))
                       (El ℙ)) (Uni (uni 0))
        ).
        { capply TyUni. assumption. }
        assert (
          Ttt.istype (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                     (Subst (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ)))))
        ).
        { ceapply TySubst ; eassumption. }
        assert (
          Ttt.isctx
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                       (Subst (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ))))))
        ).
        { capply CtxExtend. assumption. }
        assert (
          Ttt.istype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                       (Subst (El ℙ)
                              (sbzero (El ℙ) (var (S (last_cond σ))))))
            (Uni (uni 0))
        ).
        { capply TyUni. assumption. }
        assert (
          Ttt.eqtype
            (ctxextend (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                       (Subst (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ))))))
            (Subst (Subst (Uni (uni 0)) (sbweak (El ℙ)))
                   (sbshift (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ))))))
            (Uni (uni 0))
        ).
        { unfold Ttt.eqtype. pushsubst.
          - eassumption.
          - eassumption.
          - capply EqTyRefl. assumption.
          - pushsubst.
            + eassumption.
            + capply EqTyRefl. assumption.
        }
        assert (
          Ttt.eqtype
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (Prod (Subst (El ℙ) (sbzero (El ℙ) (var (S (last_cond σ)))))
                  (Subst (Subst (Uni (uni 0)) (sbweak (El ℙ)))
                         (sbshift (El ℙ)
                                  (sbzero (El ℙ) (var (S (last_cond σ))))
            )))
            (Prod (El ℙ) (Uni (uni 0)))
        ).
        { capply CongProd ; assumption. }
        assert (
          Ttt.eqtype
            (ctxextend (trans_ctx σ ctxempty) (El ℙ))
            (Subst (Arrow (El ℙ) (Uni (uni 0)))
                   (sbzero (El ℙ) (var (S (last_cond σ)))))
            (Prod (El ℙ) (Uni (uni 0)))
        ).
        { unfold Ttt.eqtype. pushsubst ; eassumption. }
        assert (
          Ttt.isterm (ctxextend (trans_ctx σ ctxempty) (El ℙ))
                     (var 0)
                     (El ℙ)
        ).
        { ceapply TermTyConv ; [ ceapply TermVarZero | .. ] ; assumption. }

        simpl. capply CtxExtend.
        ceapply TyEl.
        ceapply TermTyConv ; [ ceapply TermApp | .. ].
        + ceapply TermTyConv ; [ ceapply TermApp | .. ].
          * ceapply TermTyConv ; [ apply hHom | .. ].
            -- assumption.
            -- assumption.
          * assumption.
          * assumption.
        + assumption.
        + pushsubst.
          * ceapply SubstZero. eassumption.
          * capply EqTyRefl. assumption.
    }

  (* CtxExtend *)
  - { dependent destruction hσ.

      (* valid_fxvar *)
      - simpl. capply CtxExtend.
        pose (hh := sound_trans_type σ G A hσ i0).
        ceapply TySubst.
        + capply SubstZero.
          apply hidℙ'.
          todo.
        + ceapply TySubst.
          * ceapply SubstCtxConv ; [ ceapply SubstShift | .. ].
            -- ceapply SubstZero.
               ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
               ++ todo. (* We probably need a lemma here *)
               ++ todo.
               ++ todo.
            -- todo.
            -- todo.
            -- todo.
          * eassumption.

      (* valid_fxpath *)
      - simpl. capply CtxExtend. subst.
        todo.
    }

  Unshelve. all:todo.
Defined.

End Translation.

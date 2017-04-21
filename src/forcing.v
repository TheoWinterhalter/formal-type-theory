(* Forcing Translation

   Based on The Definitional Side of the Forcing
   by Jaber et al.
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
    + apply hℙ. todo. (* sanity *)
  - ceapply CongEl.
    eapply EqSubstℙ.
    eassumption.
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
  | fxpath σ => o
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

where "[[ A ]] σ" :=
  (Subst (Subst (trans_type σ A)
                (sbshift (Hom (var (S (last_cond σ)))
                              (var 0))
                         (sbzero (El ℙ)
                                 (var (S (last_cond σ))))))
         (sbzero (Hom (var (S (last_cond σ))) (var (S (last_cond σ))))
                 (idℙ (var (S (last_cond σ))))))

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

Lemma isctx_trans_empty :
  forall {σ},
    isfctx ctxempty σ ->
    Ttt.isctx (trans_ctx σ ctxempty).
Proof.
  intros σ h.
  dependent induction h.
  - simpl. capply CtxExtend.
    ceapply TyEl. apply hℙ.
    capply CtxEmpty.
  - simpl. capply CtxExtend.
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
        -- assert (Ttt.isterm (trans_ctx σ ctxempty) (var (last_cond σ)) (El ℙ))
            by todo.
           eassumption.
        -- ceapply TyEl. apply hℙ.
           now apply IHh.
        -- eapply EqTySubstℙ.
           capply SubstWeak.
           ceapply TyEl. apply hℙ.
           now apply IHh.
      * pushsubst.
        -- capply SubstZero.
           ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
           ++ todo.
           ++ todo.
           ++ todo.
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
              todo.
           ++ pushsubst.
              ** ceapply SubstShift.
                 --- capply SubstZero.
                     todo.
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
                         todo.
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
                     +++ ceapply SubstZero. todo.
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
  { capply CtxExtend.
    ceapply TyEl. apply hℙ.
    capply CtxExtend.
    ceapply TyEl. apply hℙ.
    now apply IHh.
  }
  { todo. }
Defined.

Fixpoint sound_trans_ctx σ Γ (hσ : isfctx Γ σ) (H : Stt.isctx Γ) {struct H} :
  Ttt.isctx (trans_ctx σ Γ)

with sound_trans_type σ Γ A (hσ : isfctx Γ σ) (H : Stt.istype Γ A) {struct H} :
  Ttt.istype (trans_ctx (fxpath σ) Γ) (trans_type σ A).

Proof.

  (* sound_trans_ctx *)
  - { destruct H.

      (* CtxEmpty *)
      - { inversion hσ.

          (* valid_cond *)
          - simpl. capply CtxExtend.
            ceapply TyEl.
            apply hℙ.
            capply CtxEmpty.

          (* valid_fxpath *)
          - simpl. capply CtxExtend.
            ceapply TyEl.
            ceapply TermTyConv ; [ ceapply TermApp | .. ].
            + ceapply TermTyConv ; [ ceapply TermApp | .. ].
              * ceapply TermTyConv ; [ apply hHom | .. ].
                -- capply CtxExtend.
                   ceapply TyEl.
                   apply hℙ.
                   todo.
                -- unfold Arrow.
                   assert (
                     Ttt.isterm (ctxextend (trans_ctx σ0 ctxempty) (El ℙ))
                                ℙ
                                (Uni (uni 0))
                   ).
                   { apply hℙ. capply CtxExtend.
                     ceapply TyEl.
                     apply hℙ.
                     todo.
                   }
                   trymagic.
                   ++ eapply EqTySubstℙ.
                      ceapply SubstWeak.
                      ceapply TyEl. apply hℙ.
                      capply CtxExtend.
                      ceapply TyEl. apply hℙ.
                      todo.
                   ++ todo. (* Problem here! *)
                   ++ eapply EqTySubstℙ.
                      ceapply SubstWeak.
                      ceapply TyEl. apply hℙ.
                      todo.
              * ceapply TermTyConv ; [ ceapply TermVarSucc | .. ].
                -- todo.
                -- ceapply TyEl.
                   todo.
                -- todo.
              * trymagic. all:todo.
            + ceapply TermTyConv ; [ ceapply TermVarZero | .. ].
              * todo.
              * todo.
            + trymagic. all:todo.
        }

      (* CtxExtend *)
      - { inversion hσ.

          (* valid_fxvar *)
          - simpl. capply CtxExtend. subst.
            pose (hh := sound_trans_type σ0 G A H2 i0).
            ceapply TySubst.
            + capply SubstZero.
              ceapply TermTyConv ; [ ceapply TermApp | .. ].
              * (* apply hidℙ. *) todo.
              * todo.
              * todo.
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
    }

  (* sound_trans_type *)
  - { todo. }

  Unshelve. all:todo.
Defined.

End Translation.

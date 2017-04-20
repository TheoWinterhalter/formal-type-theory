(* Forcing Translation

   Based on The Definitional Side of the Forcing
   by Jaber et al.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

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
Context `{hℙ : Stt.isterm ctxempty ℙ (Uni (uni 0))}.
Context `{_Hom : term}.
Context `{hHom : Stt.isterm ctxempty _Hom (Arrow (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))}.

Definition Hom p q :=
  El (app (app _Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) p) (El ℙ) (Uni (uni 0)) q).

Context `{_idℙ : term}.
Context `{hidℙ : Stt.isterm ctxempty _idℙ (Prod (El ℙ) (Hom (var 0) (var 0)))}.

Definition idℙ p :=
  app _idℙ (El ℙ) (Hom (var 0) (var 0)) p.

Context `{_comp : term}.
Context `{hcomp : Stt.isterm ctxempty _comp (Prod (El ℙ) (Prod (El ℙ) (Prod (El ℙ) (Arrow (Hom (var 2) (var 1)) (Arrow (Hom (var 1) (var 0)) (Hom (var 2) (var 0)))))))}.

Definition comp p q r f g :=
  app (app (app (app (app _comp (El ℙ) (Prod (El ℙ) (Arrow (Hom (var 2) (var 1)) (Arrow (Hom (var 1) (var 0)) (Hom (var 2) (var 0))))) p) (El ℙ) (Prod (El ℙ) (Arrow (Hom p (var 1)) (Arrow (Hom (var 1) (var 0)) (Hom p (var 0))))) q) (El ℙ) (Arrow (Hom p q) (Arrow (Hom q (var 0)) (Hom p (var 0)))) r) (Hom p q) (Arrow (Hom q r) (Hom p r)) f) (Hom q r) (Hom p r) g.

(* This is really illegible so we need to complete the alternative syntax. *)

(* We require extra definitional equalities *)
Context `{CompIdℙLeft : forall Γ p q f, Stt.isterm Γ f (Hom p q) -> Stt.eqterm Γ (comp p p q (idℙ p) f) f (Hom p q)}.
Context `{CompIdℙRight : forall Γ p q f, Stt.isterm Γ f (Hom p q) -> Stt.eqterm Γ (comp p q q f (idℙ q)) f (Hom p q)}.
Context `{CompℙAssoc : forall Γ p q r s f g h, Stt.isterm Γ f (Hom p q) -> Stt.isterm Γ g (Hom q r) -> Stt.isterm Γ h (Hom r s) -> Stt.eqterm Γ (comp p q s f (comp q r s g h)) (comp p r s (comp p q r f g) h) (Hom p s)}.

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

Axiom todo : forall {A}, A.

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

Ltac todo := apply todo.

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
            (* apply hℙ. *)
            (* This is true but we need to convince Coq it can apply the
             equivalence between Ett and Ptt here. *)
            todo.

          (* valid_fxpath *)
          - simpl. capply CtxExtend.
            (* Same kind of problem here... *)
            todo.
        }

      (* CtxExtend *)
      - { inversion hσ.

          (* valid_fxvar *)
          - simpl. capply CtxExtend. subst.
            pose (hh := sound_trans_type σ0 G A H2 i0).
            ceapply TySubst.
            + capply SubstZero.
              todo. (* again *)
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

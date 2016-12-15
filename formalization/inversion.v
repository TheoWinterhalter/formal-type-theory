(* Inversion lemmas *)

Require Import ett.
Require Import Utf8.

Notation " Γ ⊢ e ∷ A " := (isterm Γ e A) (at level 40).
Notation " Γ ⊢ A 'ty' " := (istype Γ A) (at level 40).


Lemma invert_refl : ∀ {Γ : context} {u : term} {E : type} (J : Γ ⊢ u ∷ E),
    ∀ e (u_refl : u = refl e), {A : type & Γ ⊢ e ∷ A}.

Proof.
  induction 1
  ; intros t u_refl
  ; try solve [discriminate u_refl]
  ; rename A into T.

  - exact (IHJ _ u_refl).                      (* TermTyConv *)
  - pose (IHJ t u_refl) as J_t.                (* TermCtxConv *)
    destruct J_t as [A J_t].
    exists A. exact (TermCtxConv J_t e).
  - inversion u_refl. exists T. now subst.     (* TermRefl *)
Defined.

Fact inversion_refl {Γ e E} (J : Γ ⊢ refl e ∷ E) : {A : type & Γ ⊢ e ∷ A}.
  exact (invert_refl J e eq_refl).
Defined.

Lemma invert_prod : ∀ {Γ : context} {T : type} (J : Γ ⊢ T ty),
    ∀ A B (T_Prod : T = Prod A B), (Γ ⊢ A ty * (ctxextend Γ A ⊢ B ty)).

Proof.
  induction 1
  ; try solve [intros; discriminate T_Prod]
  ; rename A into T; intros.

  - destruct (IHJ A B T_Prod) as [J_A J_B].      (* TyCtxConv *)
    pose (EqCtxExtend e (EqTyRefl J_A)) as e'.
    exact (TyCtxConv J_A e, TyCtxConv J_B e').

  - now inversion T_Prod; subst.                 (* TyProd *)
Defined.

Fact inversion_prod {Γ} {A B} (J : Γ ⊢ Prod A B ty) : Γ ⊢ A ty * (ctxextend Γ A ⊢ B ty).
  exact (invert_prod J A B eq_refl).
Defined.

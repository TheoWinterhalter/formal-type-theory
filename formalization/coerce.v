Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Axiom cheating : forall A : Type, A.
Definition todo {A} := cheating A.

Inductive context_coercion : Type :=
  | ctx_id : context_coercion.

Inductive type_coercion : type -> type -> Type :=
  | type_id : forall (A B : type), type_coercion A B
  | type_cong_prod {A1 A2 B1 B2} : type_coercion A1 A2 ->
                                   type_coercion B1 B2 ->
                                   type_coercion (Prod A1 B1) (Prod A2 B2)
  | type_cong_id {A1 A2 u1 u2 v1 v2} : type_coercion A1 A2 ->
                                       term_coercion ->
                                       term_coercion ->
                                       type_coercion (Id A1 u1 v1) (Id A2 u2 v2)

with term_coercion : Type :=
  | term_id : term_coercion
  | term_reflection : term -> term_coercion.

Fixpoint act_subst_left (crc : context_coercion) (sbs : substitution) : substitution :=
  match crc with
    | ctx_id => sbs
  end.

Fixpoint act_subst_right (crc : context_coercion) (sbs : substitution) : substitution :=
  match crc with
    | ctx_id => sbs
  end.

Definition act_subst (crc1 crc2 : context_coercion) (sbs : substitution) :=
  act_subst_left crc1 (act_subst_right crc2 sbs).

Fixpoint act_type (crc : context_coercion) (A : type) :=
  match crc with
  | ctx_id => A
  end.

Fixpoint act_term_ctx (crc : context_coercion) (u : term) : term :=
  match crc with
  | ctx_id => u
  end.

Fixpoint act_term_type {A B} (crc : type_coercion A B) (u : term) : term :=
  match crc with
  | type_id _ _ => u
  | type_cong_prod cA cB => todo (* Problem with the definition of cB! *)
  | type_cong_id cA cu cv => todo (* I'm a bit lost *)
  end.

Definition act_term {A B} (crc : context_coercion) (crt : type_coercion A B) (u : term) : term :=
  act_term_type crt (act_term_ctx crc u).

Inductive isctxcoe : context_coercion -> context -> context -> Type :=
  | isctx_id : forall G, eitt.isctx G -> isctxcoe ctx_id G G.

Inductive istypecoe : forall {A B}, type_coercion A B -> type -> type -> Type :=
  | istype_id : forall {G A B}, eitt.eqtype G A B -> istypecoe (type_id A B) A B.



(*
(* Identity context coercion. *)
Definition ctx_coe_id (G : context) : eitt.isctx G -> context_coercion G G.
Proof.
  intro.
  refine {| ctx_coe_act := sbid ;
            ctx_coe_inv := sbid |}.
  - now apply SubstId.
  - now apply SubstId.
Defined.

(* Identity type coercion. *)
Definition type_coe_id {G : context} {A : type} :
  forall (isctxG : eitt.isctx G), eitt.istype G A -> type_coercion (ctx_coe_id G isctxG) A A.
Proof.
  intros isctxG istypeA.
  refine {| type_coe_act := lam A (Subst A (sbweak A)) (var 0) ;
            type_coe_inv := lam A (Subst A (sbweak A)) (var 0) |}.
  - ceapply TermTyConv.
    + ceapply TermAbs.
      now ceapply TermVarZero.
    + ceapply CongProd.
      * ceapply EqTySym.
        now ceapply EqTyIdSubst.
      * ceapply CongTySubst.
        -- ceapply CongSubstWeak.
           ceapply EqTySym.
           now ceapply EqTyIdSubst.
        -- now ceapply EqTyRefl.
  - ceapply TermTyConv.
    + ceapply TermAbs.
      now ceapply TermVarZero.
    + ceapply CongProd.
      * ceapply EqTySym.
        now ceapply EqTyIdSubst.
      * ceapply CongTySubst.
        -- ceapply CongSubstWeak.
           ceapply EqTySym.
           now ceapply EqTyIdSubst.
        -- now ceapply EqTyRefl.
Defined.
*)
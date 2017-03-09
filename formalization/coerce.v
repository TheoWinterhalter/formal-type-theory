Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Inductive context_coercion : Type :=
  | ctx_id : context_coercion.

Inductive type_coercion : type -> type -> Type :=
  | type_id : forall (A : type), type_coercion A A.
  
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
  | type_id _ => u
  end.

Definition act_term {A B} (crc : context_coercion) (crt : type_coercion A B) (u : term) : term :=
  act_term_type crt (act_term_ctx crc u).

Inductive isctxcoe : context_coercion -> context -> context -> Type :=
  | isctx_id : forall G, eitt.isctx G -> isctxcoe ctx_id G G.

Inductive istypecoe : forall {A B}, type_coercion A B -> type -> type -> Type :=
  | istype_id : forall {G A}, eitt.istype G A -> istypecoe (type_id A) A A.
  


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
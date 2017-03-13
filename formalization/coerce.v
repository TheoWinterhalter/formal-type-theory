Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Axiom cheating : forall A : Type, A.
Definition todo {A} := cheating A.

Inductive context_coercion : Type :=
  | ctx_id : context_coercion.

(* Can't we remove the type -> type and just keep it inside the constructor? *)
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
  | term_reflection : forall (A : type) (u v p : term), term_coercion.


(* Computation of inverses of coercions *)

Definition inv_ctx_coe (crc : context_coercion) : context_coercion :=
  match crc with
  | ctx_id => ctx_id
  end.

Fixpoint inv_term_coe (crtt : term_coercion) : term_coercion :=
  match crtt with
  | term_id => term_id
  | term_reflection A u v p =>
    term_reflection A v u (j A u (Id A (var 1) u) (refl A u) v p)
  end.

Fixpoint inv_type_coe {A B} (crt : type_coercion A B) : type_coercion B A :=
  match crt with
  | type_id A B => type_id B A
  | type_cong_prod cA cB => type_cong_prod (inv_type_coe cA) (inv_type_coe cB)
  | type_cong_id cA cu cv => type_cong_id (inv_type_coe cA)
                                         (inv_term_coe cu)
                                         (inv_term_coe cv)
  end.


(* Action of coercions on expressions *)

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

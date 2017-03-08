(* The intermediate type theory with coercions
   (CTT stands for Coercive Type Theory). *)
Require Import syntax.
Require eitt.

Structure context_coercion (G G' : context) : Type := {
  ctx_coe_act : substitution ; (* a substitution sbs : G -> G' *)
  ctx_coe_inv : substitution (* a substitution sbs : G' -> G *)
  (* in the future we expect requirements such as derivability of [issubst sbs G G'] *)
}.

Arguments ctx_coe_act {_ _} _.
Arguments ctx_coe_inv {_ _} _.

Structure type_coercion {G G'} (crc : context_coercion G G') (A A' : type) : Type := {
  (* a coercion c : G -> G' *)
  (* a type G |- A *)
  (* a type G' |- A' *)
  type_coe_act : term ; (* a term G' |- _ : crc(A) -> A' *)
  type_coe_inv : term   (* a term G |- _ : crc^-1(A') -> A *)
  (* in the future there will be more requirements here which will create
     dependence on the parameters. *)
}.

Arguments type_coe_act {_ _ _ _ _} _.
Arguments type_coe_inv {_ _ _ _ _} _.

Definition act_subst {G G' D D'}
           (crc1 : context_coercion G G')
           (crc2 : context_coercion D D') sbs
  :=
    sbcomp (ctx_coe_inv crc1) (sbcomp sbs (ctx_coe_act crc2)).

Definition act_type {G G'}
           (crc : context_coercion G G')
           A
  :=
    Subst A (ctx_coe_inv crc).

Definition act_term {G G'} {crc : context_coercion G G'} {A A'}
           (crt : type_coercion crc A A')
           u
  :=
  app (type_coe_act crt)
  (act_type crc A)
  (Subst A' (sbweak (act_type crc A)))
  (subst u (ctx_coe_inv crc)).

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> type -> context

with type :=
     | Prod : type -> type -> type
     | Id : type -> term -> term -> type
     | Subst : type -> substitution -> type
     | Empty : type
     | Unit : type
     | Bool : type
     | Coerce : forall {G G'}, context_coercion G G' -> type -> type

with term : Type :=
     | var : nat -> term
     | lam : type -> type -> term -> term
     | app : term -> type -> type -> term -> term
     | refl : type -> term -> term
     | j : type -> term -> type -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | exfalso : type -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : type -> term -> term -> term -> term
     | coerce : forall {G G'} {crc : context_coercion G G'} {A A'}, type_coercion crc A A' -> term -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
     | sbcoerce : forall {G G' D D'}, context_coercion G G' -> context_coercion D D' -> substitution -> substitution.

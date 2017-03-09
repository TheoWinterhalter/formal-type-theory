Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Structure context_coercion (G G' : context) : Type := {
  ctx_coe_act : substitution ;
  ctx_coe_inv : substitution ;
  ctx_coe_issubst_act : eitt.issubst ctx_coe_act G G' ;
  ctx_coe_issubst_inv : eitt.issubst ctx_coe_inv G' G
}.

Arguments ctx_coe_act {_ _} _.
Arguments ctx_coe_inv {_ _} _.
Arguments ctx_coe_issubst_act {_ _} _.
Arguments ctx_coe_issubst_inv {_ _} _.

Structure type_coercion {G G'} (crc : context_coercion G G') (A A' : type) : Type := {
  type_coe_act : term ; (* a term G' |- _ : crc(A) -> A' *)
  type_coe_inv : term ; (* a term G |- _ : crc^-1(A') -> A *)
  type_coe_istype_act : eitt.isterm G' type_coe_act (Arrow (Subst A (ctx_coe_inv crc)) A') ;
  type_coe_istype_inv : eitt.isterm G type_coe_act (Arrow (Subst A' (ctx_coe_act crc)) A)
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

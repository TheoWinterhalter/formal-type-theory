(* The intermediate type theory with coercions
   (CTT stands for Coercive Type Theory). *)
Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

Require eitt.


(* Coercions between contexts. *)
Structure contextCoercion :=
  { ctxco_map : substitution
  ; ctxco_inv : substitution
  }.

Definition isContextCoercion c G D := (
  eitt.issubst (ctxco_map c) G D *
  eitt.issubst (ctxco_inv c) D G *
  (forall A u,
     eitt.isterm D u A ->
     { p : term
     & eitt.isterm D
                  p
                  (Id A
                          (subst (subst u (ctxco_map c)) (ctxco_inv c))
                          u
                  )
     }
  ))%type.

(* Coercions between types, over a context coercion. *)
Structure typeCoercion :=
  { tyco_map : term
  ; tyco_inv : term
  }.

(* Type coercion tc is a valid coercion from A to B
   over context coercion cc from G to D. *)
Definition istypeCoercion cc G D tc A B :=
(
  eitt.isterm G
             (tyco_map tc)
             (Prod
                A
                (Subst (Subst B (ctxco_map cc)) (sbweak A))) *
  eitt.isterm D
             (tyco_inv tc)
             (Prod
                B
                (Subst (Subst A (ctxco_inv cc)) (sbweak B))) *
  (forall x,
        eitt.isterm G x A ->
        { p : term
        & eitt.isterm G p
                     (Id
                        A
                        (app
                           (subst (tyco_inv tc) (ctxco_map cc))
                           (Subst B (ctxco_map cc))
                           (Subst (Subst (Subst A (ctxco_inv cc)) (sbweak B))
                                  (ctxco_map cc))
                           (app
                              (tyco_map tc)
                              A
                              (Subst (Subst B (ctxco_map cc)) (sbweak A))
                              x))
                        x)
        }
  )
)%type.

(* Coercion for a type *)
Definition typeCoerce : Type := contextCoercion.

(* Coercion for a term *)
Definition termCoerce : Type :=
  contextCoercion * typeCoercion.

(* Structure termCoerce : Type := *)
(*   { (* ctx_fro : eitt.context ; *) *)
(*     (* ctx_to  : context ; *) *)
(*     (* ctx_co  : @contextCoercion ctx_fro ctx_to ; *) *)
(*     full_ctx_co : typeCoerce ; (* Maybe abstract it away? *) *)
(*     ty_fro      : type ; *)
(*     ty_to       : type ; *)
(*     ty_co       : @typeCoercion (ctx_fro full_ctx_co) *)
(*                                 (ctx_to  full_ctx_co) *)
(*                                 (ctx_co  full_ctx_co) *)
(*                                 ty_fro ty_to *)
(*   }. *)

(* Coercion for a substitution *)
Definition substCoerce : Type :=
  contextCoercion * contextCoercion.

(* Inverses of coercions *)
Definition contextInv c : contextCoercion :=
  {| ctxco_map := ctxco_inv c
   ; ctxco_inv := ctxco_map c |}.

Lemma isCoercionContextInv :
  forall {c G D}, isContextCoercion c G D ->
             isContextCoercion (contextInv c) D G.
Proof.
  intros c G D H.
  destruct H as [[h1 h2] h3].
  repeat split.
  - assumption.
  - assumption.
  - intros A u H.
    pose (sbs := ctxco_inv c).
    pose (As := Subst A sbs).
    pose (us := subst u sbs).
    assert (H' : eitt.isterm D us As).
    { ceapply TermSubst.
      - exact h2.
      - assumption.
    }
    destruct (h3 As us H') as (p & Hp).
    (* Am I missing something? Or do we need to modify the definition? *)
    admit.
Admitted.

(* Definition typeInv c : typeCoercion := *)
(*   {| tyco_map := tyco_inv c *)
(*    ; tyco_inv := tyco_map c |}. *)

(* Composition of coercions *)
Definition contextComp c1 c2 : contextCoercion :=
  {| ctxco_map := sbcomp (ctxco_map c1) (ctxco_map c2)
   ; ctxco_inv := sbcomp (ctxco_inv c2) (ctxco_inv c1) |}.

Lemma isCoercionContextComp :
  forall {G D E c1 c2},
    isContextCoercion c1 D E ->
    isContextCoercion c2 G D ->
    isContextCoercion (contextComp c1 c2) G E.
Proof.
  intros G D E c1 c2 h1 h2.
  destruct h1 as [[map1 inv1] coh1].
  destruct h2 as [[map2 inv2] coh2].
  repeat split.
  - unfold contextComp. simpl.
    ceapply SubstComp.
    + eassumption.
    + assumption.
  - unfold contextComp. simpl.
    ceapply SubstComp.
    + eassumption.
    + assumption.
  - admit.
Admitted.


(* Some identities *)
Definition contextId : contextCoercion :=
  {| ctxco_map := sbid
   ; ctxco_inv := sbid |}.

Definition typeId A : typeCoercion :=
  {| tyco_map := lam A (Subst A (sbweak A)) (var 0)
   ; tyco_inv := lam A (Subst A (sbweak A)) (var 0) |}.

Definition idTy : typeCoerce := contextId.
Definition idTm A : termCoerce := (contextId , typeId A).
Definition idSb : substCoerce := (contextId , contextId).

Lemma isCoercionContextId :
  forall G,
    eitt.isctx G ->
    isContextCoercion (contextId) G G.
Proof.
  intros G h. repeat split.
  - unfold contextId. simpl.
    apply SubstId. assumption.
  - simpl.
    capply SubstId. assumption.
  - intros A u H. simpl.
    exists (refl A u).
    admit.
Admitted.



(* CTT *)

Inductive context : Type :=
| ctxempty : context
| ctxextend : context -> type -> context

with type' :=
     | Prod : type -> type -> type'
     | Id : type -> term -> term -> type'
     | Subst : type -> substitution -> type'
     | Empty : type'
     | Unit : type'
     | Bool : type'

with type : Type :=
     | Coerce : typeCoerce -> type' -> type

with term' : Type :=
     | var : nat -> term'
     | lam : type -> type -> term -> term'
     | app : term -> type -> type -> term -> term'
     | refl : type -> term -> term'
     | j : type -> term -> type -> term -> term -> term -> term'
     | subst : term -> substitution -> term'
     | exfalso : type -> term -> term'
     | unit : term'
     | true : term'
     | false : term'
     | cond : type -> term -> term -> term -> term'

with term : Type :=
     | coerce : termCoerce -> term' -> term

with substitution' : Type :=
     | sbzero : context -> type -> term -> substitution'
     | sbweak : context -> type -> substitution'
     | sbshift : context -> type -> substitution -> substitution'
     | sbid : context -> substitution'
     | sbcomp : substitution -> substitution -> substitution'

with substitution : Type :=
     | sbcoerce : substCoerce -> substitution' -> substitution.

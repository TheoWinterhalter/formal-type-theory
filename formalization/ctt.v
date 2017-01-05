(* The intermediate type theory with coercions
   (CTT stands for Coercive Type Theory). *)
Require itt.


(* Coercions between contexts. *)
Structure contextCoercion :=
  { ctxco_map : itt.substitution
  ; ctxco_inv : itt.substitution
  }.

Definition isContextCoercion c G D := (
  itt.issubst (ctxco_map c) G D *
  itt.issubst (ctxco_inv c) D G *
  (forall A u,
     itt.isterm D u A ->
     { p : itt.term
     & itt.isterm D
                  p
                  (itt.Id A
                          (itt.subst (itt.subst u (ctxco_map c)) (ctxco_inv c))
                          u
                  )
     }
  ))%type.

(* Coercions between types, over a context coercion. *)
Structure typeCoercion :=
  { tyco_map : itt.term
  ; tyco_inv : itt.term
  }.

(* Type coercion tc is a valid coercion from A to B
   over context coercion cc from G to D. *)
Definition istypeCoercion cc G D tc A B :=
(
  itt.isterm G
             (tyco_map tc)
             (itt.Prod
                A
                (itt.Subst (itt.Subst B (ctxco_map cc)) (itt.sbweak G A))) *
  itt.isterm D
             (tyco_inv tc)
             (itt.Prod
                B
                (itt.Subst (itt.Subst A (ctxco_inv cc)) (itt.sbweak D B))) *
  (forall x,
        itt.isterm G x A ->
        { p : itt.term
        & itt.isterm G p
                     (itt.Id
                        A
                        (itt.app
                           (itt.subst (tyco_inv tc) (ctxco_map cc))
                           (itt.Subst B (ctxco_map cc))
                           (itt.Subst
                              A
                              (itt.sbweak G (itt.Subst B (ctxco_map cc))))
                           (itt.app
                              (tyco_map tc)
                              A
                              (itt.Subst (itt.Subst B (ctxco_map cc))
                                         (itt.sbweak G A))
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
(*   { (* ctx_fro : itt.context ; *) *)
(*     (* ctx_to  : itt.context ; *) *)
(*     (* ctx_co  : @contextCoercion ctx_fro ctx_to ; *) *)
(*     full_ctx_co : typeCoerce ; (* Maybe abstract it away? *) *)
(*     ty_fro      : itt.type ; *)
(*     ty_to       : itt.type ; *)
(*     ty_co       : @typeCoercion (ctx_fro full_ctx_co) *)
(*                                 (ctx_to  full_ctx_co) *)
(*                                 (ctx_co  full_ctx_co) *)
(*                                 ty_fro ty_to *)
(*   }. *)

(* Coercion for a substitution *)
Definition substCoerce : Type :=
  contextCoercion * contextCoercion.

(* Some identities *)
Definition contextId G : contextCoercion :=
  {| ctxco_map := itt.sbid G
   ; ctxco_inv := itt.sbid G |}.

Definition typeId G A : typeCoercion :=
  {| tyco_map := itt.lam A (itt.Subst A (itt.sbweak G A)) (itt.var 0)
   ; tyco_inv := itt.lam A (itt.Subst A (itt.sbweak G A)) (itt.var 0) |}.

Definition idTy G : typeCoerce := contextId G.
Definition idTm G A : termCoerce := (contextId G , typeId G A).
Definition idSb G D : substCoerce := (contextId G , contextId D).

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

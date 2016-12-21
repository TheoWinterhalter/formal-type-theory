(* The intermediate type theory with coercions
   (CTT stands for Coercive Type Theory). *)
Require itt.


(* Coercions between contexts. *)
Structure contextCoercion {G D : itt.context} :=
  { ctx_bij : itt.substitution
  ; ctx_inv : itt.substitution
  ; ctx_bij_ty : itt.issubst ctx_bij G D
  ; ctx_inv_ty : itt.issubst ctx_inv D G
  ; ctx_coh :
      forall A u,
        itt.isterm D u A ->
        { p : itt.term
        & itt.isterm D p (itt.Id A (itt.subst (itt.subst u ctx_bij) ctx_inv) u)
        }
  }.

(* Coercions between types, over a context coercion. *)
Structure typeCoercion {G D : itt.context} (c : @contextCoercion G D)
                       (A B : itt.type) :=
  { ty_bij : itt.term
  ; ty_inv : itt.term
  ; ty_bij_ty :
      itt.isterm G
                 ty_bij
                 (itt.Prod
                    A
                    (itt.Subst (itt.Subst B (ctx_bij c)) (itt.sbweak G A)))
  ; ty_inv_ty :
      itt.isterm D
                 ty_inv
                 (itt.Prod
                    B
                    (itt.Subst (itt.Subst A (ctx_inv c)) (itt.sbweak D B)))
  ; ty_coh :
      forall x,
        itt.isterm G x A ->
        { p : itt.term
        & itt.isterm G p
                     (itt.Id A
                       (itt.app
                          (itt.subst ty_inv (ctx_bij c))
                          (itt.Subst B (ctx_bij c))
                          (itt.Subst A (itt.sbweak G (itt.Subst B (ctx_bij c))))
                          (itt.app
                             ty_bij
                             A
                             (itt.Subst (itt.Subst B (ctx_bij c))
                                        (itt.sbweak G A))
                             x))
                       x)
        }
  }.

(* Coercion for a type *)
Structure typeCoerce : Type :=
  { ctx_fro : itt.context ;
    ctx_to  : itt.context ;
    ctx_co  : @contextCoercion ctx_fro ctx_to
  }.

(* Coercion for a term *)
Structure termCoerce : Type :=
  { (* ctx_fro : itt.context ; *)
    (* ctx_to  : itt.context ; *)
    (* ctx_co  : @contextCoercion ctx_fro ctx_to ; *)
    full_ctx_co : typeCoerce ; (* Maybe abstract it away? *)
    ty_fro      : itt.type ;
    ty_to       : itt.type ;
    ty_co       : @typeCoercion (ctx_fro full_ctx_co)
                                (ctx_to  full_ctx_co)
                                (ctx_co  full_ctx_co)
                                ty_fro ty_to
  }.

Parameter substCoerce : Type.

(* These will require parameters. *)
Parameter idTy : typeCoerce.
Parameter idTm : termCoerce.
Parameter idSb : substCoerce.

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

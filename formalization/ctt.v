(* The intermediate type theory with coercions
   (CTT stands for Coercive Type Theory). *)
Require Import syntax.
Require eitt.

Parameter type_coercion : Type.

Structure type_coercion : Type :=
{ type_dom : context ;
  type_cod : context ;
  type_act : forall A : type, eitt.istype type_dom A -> eitt.istype type_cod A
}.


Parameter subst_coercion : Type.
Parameter term_coercion : Type.

Parameter type_act : type_coercion 

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
     | Coerce : type_coercion -> type' -> type

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
     | coerce : term_coercion -> term' -> term

with substitution' : Type :=
     | sbzero : type -> term -> substitution'
     | sbweak : type -> substitution'
     | sbshift : type -> substitution -> substitution'
     | sbid : substitution'
     | sbcomp : substitution -> substitution -> substitution'

with substitution : Type :=
     | sbcoerce : subst_coercion -> substitution' -> substitution.

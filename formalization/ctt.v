(* The intermediate type theory with coercions (CTT for Coercive Type Theory). *)


Parameter typeCoerce : Type.
Parameter termCoerce : Type.

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
     | subst : term -> substitution -> term'
     | exfalso : type -> term -> term'
     | unit : term'
     | true : term'
     | false : term'
     | cond : type -> term -> term -> term -> term'

with term : Type :=
     | coerce : termCoerce -> term' -> term

with substitution : Type :=
     | sbzero : context -> type -> term -> substitution
     | sbweak : context -> type -> substitution
     | sbshift : context -> type -> substitution -> substitution.

Parameter isctx : context -> Type.

Parameter istype : context -> type -> Type.

Parameter isterm : context -> term -> type -> Type.

Parameter issubst : substitution -> context -> context -> Type.
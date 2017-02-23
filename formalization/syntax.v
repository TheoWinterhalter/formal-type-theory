Inductive context : Type :=
| ctxempty : context
| ctxextend : context -> type -> context

with type : Type :=
     | Prod : type -> type -> type
     | Id : type -> term -> term -> type
     | Subst : type -> substitution -> type
     | Empty : type
     | Unit : type
     | Bool : type

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

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution.

Parameter reflective : type -> type.

(* Notations for writing down inference rules. *)

Notation "'rule' r 'endrule'" := (r) (at level 96, only parsing).
Notation "'parameters:'  x .. y , p" := ((forall x , .. (forall y , p) ..)) (at level 200, x binder, y binder,
                                                            right associativity, only parsing).
Notation "'premise:' p q" := (p -> q) (only parsing, at level 95).
Notation "'conclusion:' q" := q (no associativity, only parsing, at level 94).

(* Alternative syntax with names for variables *)

Require Import String.

Definition variable := string.

Inductive context : Type :=
| ctxempty : context
| ctxextend : context -> variable -> type -> context

with type : Type :=
| Prod : variable -> type -> type -> type
| Id : type -> term -> term -> type
(* | Subst : type -> substitution -> type *)
| Empty : type
| Unit : type
| Bool : type
| SimProd : type -> type -> type
| Uni : nat -> type
(* TODO: Add a Prop universe *)
| El : term -> type

with term : Type :=
| var : variable -> term
| lam : variable -> type -> type -> term -> term
| app : term -> variable -> type -> type -> term -> term
| refl : type -> term -> term
| j : type -> term -> variable -> variable -> type -> term -> term -> term -> term
(* | subst : term -> substitution -> term *)
| exfalso : type -> term -> term
| unit : term
| true : term
| false : term
| cond : variable -> type -> term -> term -> term -> term
| pair : type -> type -> term -> term -> term
| proj1 : type -> type -> term -> term
| proj2 : type -> type -> term -> term
| uniProd : nat -> variable -> term -> term -> term
| uniId : nat -> term -> term -> term -> term
| uniEmpty : nat -> term
| uniUnit : nat -> term
| uniBool : nat -> term
| uniSimProd : nat -> term -> term -> term
| uniUni : nat -> term.

(* with substitution : Type := *)
(* (* | sbzero : type -> term -> substitution *) *)
(* (* | sbweak : type -> substitution *) *)
(* (* | sbshift : type -> substitution -> substitution *) *)
(* | sbvar : type -> variable -> term -> substitution *)
(* | sbid : substitution *)
(* | sbcomp : substitution -> substitution -> substitution. *)

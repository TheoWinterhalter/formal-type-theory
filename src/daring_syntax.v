(* Daring Syntax

   In a similar fashion as the paranoid syntax, or rather in a dual fashion,
   we write a syntax that isn't entirely defined inductively but that offers
   operators that compute or ignore some of the arguments.

   This way, we hope to provide a syntax that doesn't feature any type
   annotation, doesn't distinguish between the syntax of term and the syntax
   of types, has Russel style universes, and meta-substitutions (substitutions
   compute).

   We intend the both of them as a way to express the two extremes that should
   be captured by our formalisation.
*)

Require config.

(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> term -> context

with term : Type :=
     (* Types *)
     | Prod : term -> term -> term
     | Id : term -> term -> term -> term
     | Empty : term
     | Unit : term
     | Bool : term
     | SimProd : term -> term -> term
     | Uni : level -> term
     (* Terms *)
     | var : nat -> term
     | lam : term -> term
     | app : term -> term -> term
     | refl : term -> term -> term
     | j : term -> term -> term -> term -> term -> term -> term
     | exfalso : term -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : term -> term -> term -> term -> term
     | pair : term -> term -> term -> term -> term
     | proj1 : term -> term -> term -> term
     | proj2 : term -> term -> term -> term
.

Definition exactly : forall {F A}, A -> config.Flag F -> A.
Proof.
  intros F A a f.
  exact a.
Defined.

Local Instance Syntax : config.Syntax := {|
  config.context      := context ;
  config.type         := term ;
  config.term         := term ;
  (* config.substitution := substitution ; *)

  config.ctxempty  := ctxempty ;
  config.ctxextend := ctxextend ;

  config.Id    := Id ;
  (* config.Subst := Subst ; *)

  config.var   := var ;
  config.refl  := refl ;
  (* TODO BELOW *)
  (* config.subst := subst ; *)

  (* config.sbzero  := sbzero ; *)
  (* config.sbweak  := sbweak ; *)
  (* config.sbshift := sbshift ; *)
  (* config.sbid    := sbid ; *)
  (* config.sbcomp  := sbcomp *)
|}.
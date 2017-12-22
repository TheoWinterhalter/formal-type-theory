(* Abstract notion of syntax. *)

(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Class LIFT tt := glift (n k : nat) (t : tt) : tt.
Notation "t ↑ n # k" :=
  (glift n k t) (at level 5, n at level 0, left associativity).
Notation "t ↑ n" :=
  (glift n 0 t) (at level 5, n at level 0, left associativity).
Notation "t ↑" :=
  (glift 1 0 t) (at level 5, left associativity).

Class SUBST term tt := gsubst (u : term) (t : tt) (n : nat) : tt.
Notation "t [ n ← u ]" :=
  (gsubst u t n) (at level 5, n at level 0, left associativity).
Notation "t [ ← u ]" :=
  (gsubst u t 0) (at level 5, left associativity).

Section SyntaxDefinition.

Class Syntax := {
  context : Type;
  type : Type;
  term : Type;
  substitution : Type;

  ctxempty : context;
  ctxextend : context -> type -> context;

  Prod : type -> type -> type;
  Id : type -> term -> term -> type;
  Empty : type;
  Unit : type;
  Bool : type;
  BinaryProd : type -> type -> type;
  Uni : level -> type;
  El : level -> term -> type;

  var : nat -> term;
  lam : type -> type -> term -> term;
  app : term -> type -> type -> term -> term;
  refl : type -> term -> term;
  j : type -> term -> type -> term -> term -> term -> term;
  exfalso : type -> term -> term;
  unit : term;
  true : term;
  false : term;
  cond : type -> term -> term -> term -> term;
  pair : type -> type -> term -> term -> term;
  proj1 : type -> type -> term -> term;
  proj2 : type -> type -> term -> term;
  uniProd : level -> level -> term -> term -> term;
  uniId : level -> term -> term -> term -> term;
  uniEmpty : level -> term;
  uniUnit : level -> term;
  uniBool : nat -> term;
  uniBinaryProd : level -> level -> term -> term -> term;
  uniUni : level -> term;

  (* Meta-level operations *)
  lift :> LIFT term;
  Lift :> LIFT type;

  subst :> SUBST term term;
  Subst :> SUBST term type;

  (* TODO *)

  Arrow := fun (A B :  type) => Prod A B↑
}.

End SyntaxDefinition.
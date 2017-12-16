(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Local Class CONS A B := Cons : A -> B -> B.
Local Notation "u ⋅ σ" := (Cons u σ) (at level 20).

Class Syntax := {
  context : Type;
  type : Type;
  term : Type;
  substitution : Type;

  ctxempty : context;
  ctxextend : context -> type -> context;

  Prod : type -> type -> type;
  Id : type -> term -> term -> type;
  Subst : type -> substitution -> type;
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
  subst : term -> substitution -> term;
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

  (* Substitutions *)
  sbid : substitution;
  (* sbcons : term -> substitution -> substitution; *)
  sbcons : CONS term substitution;

  (* Computation rules for substitutions *)
  SubstProd :
    forall {σ A B},
      Subst (Prod A B) σ = Prod (Subst A σ) (Subst B ((var 0) ⋅ σ));
  SubstId :
    forall {σ A u v},
      Subst (Id A u v) σ = Id (Subst A σ) (subst u σ) (subst v σ);
  SubstEmpty :
    forall {σ}, Subst Empty σ = Empty;
  SubstUnit :
    forall {σ}, Subst Unit σ = Unit;
  SubstBool :
    forall {σ}, Subst Bool σ = Bool;
  SubstBinaryProd :
    forall {σ A B},
      Subst (BinaryProd A B) σ = BinaryProd (Subst A σ) (Subst B σ);
  (* TO BE CONTINUED... *)

  (* Should be defined concepts? *)
  (* sbzero : type -> term -> substitution; *)
  (* sbweak : type -> substitution; *)
  (* sbshift : type -> substitution -> substitution; *)
  (* sbid : substitution; *)
  (* sbcomp : substitution -> substitution -> substitution; *)

  (* Arrow := (fun (A B :  type) => Prod A (Subst B sbweak)) *)
}.

Global Notation "u ⋅ σ" := (sbcons u σ) (at level 20).
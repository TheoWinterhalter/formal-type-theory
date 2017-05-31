Class Syntax := {
  context      : Type ;
  type         : Type ;
  term         : Type ;
  substitution : Type ;

  (* Context constructors *)
  ctxempty  : context ;
  ctxextend : context -> type -> context ;

  (* Types *)
  Id    : type -> term -> term -> type ;
  Subst : type -> substitution -> type ;

  (* Terms *)
  var   : nat -> term ;
  refl  : type -> term -> term ;
  subst : term -> substitution -> term ;

  (* Explicit substitutions *)
  sbzero  : type -> term -> substitution ;
  sbweak  : type -> substitution ;
  sbshift : type -> substitution -> substitution ;
  sbid    : substitution ;
  sbcomp  : substitution -> substitution -> substitution
}.

Class Precond := {
  precondFlag : Type
}.

Class Reflection := {
  reflectionFlag : Type
}.

Class SimpleProducts `{S : Syntax} := {
  simpleproductsFlag : Type ;

  (* Type *)
  SimProd : type -> type -> type ;

  (* Terms *)
  pair  : type -> type -> term -> term -> term ;
  proj1 : type -> type -> term -> term ;
  proj2 : type -> type -> term -> term
}.

Class ProdEta := {
  prodetaFlag : Type
}.

Class Universes `{S : Syntax} := {
  universesFlag : Type ;

  (* Problem: How to handle levels? *)

  (* Types *)
  Uni : level -> type ;
  El  : level -> term -> type ;

  (* Problem: The codes need to depend on other flags!
     I need to learn more about them to see if it is possible.
   *)

  (* Terms *)
  uniUni : level -> term
}.

Class WithProp := {
  withpropFlag : Type
}.

Class WithJ := {
  withjFlag : Type
}.

Class WithEmpty := {
  withemptyFlag : Type
}.

Class WithUnit := {
  withunitFlag : Type
}.

Class WithBool := {
  withboolFlag : Type
}.

Class WithPi := {
  withpiFlag : Type
}.

Inductive Yes : Type := yes.
Inductive No : Type := .

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
  SimProd : `{simpleproductsFlag} -> type -> type -> type ;

  (* Terms *)
  pair  : `{simpleproductsFlag} -> type -> type -> term -> term -> term ;
  proj1 : `{simpleproductsFlag} -> type -> type -> term -> term ;
  proj2 : `{simpleproductsFlag} -> type -> type -> term -> term
}.

Class ProdEta := {
  prodetaFlag : Type
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

Class UniverseLevels := {
  level : Type
}.

Class Universes `{S : Syntax} `{UL : UniverseLevels} := {
  universesFlag : Type ;

  (* Levels *)
  uni : `{universesFlag} -> nat -> level ;

  (* Types *)
  Uni : `{universesFlag} -> level -> type ;
  El  : `{universesFlag} -> level -> term -> type ;

  (* Terms *)
  uniUni : `{universesFlag} -> level -> term
}.

Class UniSimProd `{S : Syntax} `{U : Universes} `{SP : SimpleProducts} := {
  uniSimProd : `{universesFlag} -> `{simpleproductsFlag} ->
               level -> level -> term -> term -> term
}.

Inductive Yes : Type := yes.
Inductive No : Type := .

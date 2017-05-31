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

Class SimpleProducts `{Syntax} := {
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

Class WithJ `{Syntax} := {
  withjFlag : Type ;

  (* Term *)
  j : `{withjFlag} -> type -> term -> type -> term -> term -> term -> term
}.

Class WithEmpty `{Syntax} := {
  withemptyFlag : Type ;

  (* Type *)
  Empty : `{withemptyFlag} -> type
}.

Class WithUnit `{Syntax} := {
  withunitFlag : Type ;

  (* Type *)
  Unit : `{withunitFlag} -> type ;

  (* Term *)
  unit : `{withunitFlag} -> term
}.

Class WithBool `{Syntax} := {
  withboolFlag : Type ;

  (* Type *)
  Bool : `{withboolFlag} -> type ;

  (* Terms *)
  true  : `{withboolFlag} -> term ;
  false : `{withboolFlag} -> term ;
  cond  : `{withboolFlag} -> type -> term -> term -> term -> term
}.

Class WithPi `{Syntax} := {
  withpiFlag : Type ;

  (* Type *)
  Prod : `{withpiFlag} -> type -> type -> type ;

  (* Terms *)
  lam : `{withpiFlag} -> type -> type -> term -> term ;
  app : `{withpiFlag} -> term -> type -> type -> term -> term
}.

Class UniverseLevels := {
  level : Type
}.

Class Universes `{Syntax} `{UniverseLevels} := {
  universesFlag : Type ;

  (* Levels *)
  uni : `{universesFlag} -> nat -> level ;

  (* Types *)
  Uni : `{universesFlag} -> level -> type ;
  El  : `{universesFlag} -> level -> term -> type ;

  (* Terms *)
  uniUni : `{universesFlag} -> level -> term
}.

Class WithProp `{Universes} := {
  withpropFlag : Type ;

  (* Level *)
  prop : `{withpropFlag} -> level
}.

Class UniProd `{Universes} `{WithPi} := {
  uniProd : `{universesFlag} -> `{withpiFlag} ->
            level -> level -> term -> term -> term
}.

Class UniId `{Universes} (* `{WithId} *) := {
  uniId : `{universesFlag} -> (* `{withidFlag} -> *)
          level -> term -> term -> term -> term
}.

Class UniEmpty `{Universes} `{WithEmpty} := {
  uniEmpty : `{universesFlag} -> `{withemptyFlag} ->
             level -> term
}.

Class UniUnit `{Universes} `{WithUnit} := {
  uniUnit : `{universesFlag} -> `{withunitFlag} ->
             level -> term
}.

Class UniBool `{Universes} `{WithBool} := {
  uniBool : `{universesFlag} -> `{withboolFlag} ->
             level -> term
}.

Class UniSimProd `{Universes} `{SimpleProducts} := {
  uniSimProd : `{universesFlag} -> `{simpleproductsFlag} ->
               level -> level -> term -> term -> term
}.

Inductive Yes : Type := yes.
Inductive No : Type := .

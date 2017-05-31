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
  SimProd : forall {_ : simpleproductsFlag}, type -> type -> type ;

  (* Terms *)
  pair  : forall {_ : simpleproductsFlag}, type -> type -> term -> term -> term ;
  proj1 : forall {_ : simpleproductsFlag}, type -> type -> term -> term ;
  proj2 : forall {_ : simpleproductsFlag}, type -> type -> term -> term
}.

Class ProdEta := {
  prodetaFlag : Type
}.

Class WithJ `{Syntax} := {
  withjFlag : Type ;

  (* Term *)
  j : forall {_ : withjFlag}, type -> term -> type -> term -> term -> term -> term
}.

Class WithEmpty `{Syntax} := {
  withemptyFlag : Type ;

  (* Type *)
  Empty : forall {_ : withemptyFlag}, type ;

  (* Term *)
  exfalso : forall {_ : withemptyFlag}, type -> term -> term
}.

Class WithUnit `{Syntax} := {
  withunitFlag : Type ;

  (* Type *)
  Unit : forall {_ : withunitFlag}, type ;

  (* Term *)
  unit : forall {_ : withunitFlag}, term
}.

Class WithBool `{Syntax} := {
  withboolFlag : Type ;

  (* Type *)
  Bool : forall {_ : withboolFlag}, type ;

  (* Terms *)
  true  : forall {_ : withboolFlag}, term ;
  false : forall {_ : withboolFlag}, term ;
  cond  : forall {_ : withboolFlag}, type -> term -> term -> term -> term
}.

Class WithPi `{Syntax} := {
  withpiFlag : Type ;

  (* Type *)
  Prod : forall {_ : withpiFlag}, type -> type -> type ;

  (* Terms *)
  lam : forall {_ : withpiFlag}, type -> type -> term -> term ;
  app : forall {_ : withpiFlag}, term -> type -> type -> term -> term
}.

Class UniverseLevels := {
  level : Type
}.

Class Universes `{Syntax} `{UniverseLevels} := {
  universesFlag : Type ;

  (* Levels *)
  uni : forall {_ : universesFlag}, nat -> level ;

  (* Types *)
  Uni : forall {_ : universesFlag}, level -> type ;
  El  : forall {_ : universesFlag}, level -> term -> type ;

  (* Terms *)
  uniUni : forall {_ : universesFlag}, level -> term
}.

Class WithProp `{Universes} := {
  withpropFlag : Type ;

  (* Level *)
  prop : forall {_ : withpropFlag}, level
}.

Class UniProd `{Universes} `{WithPi} := {
  uniProd : forall {_ : universesFlag}, forall {_ : withpiFlag},
            level -> level -> term -> term -> term
}.

Class UniId `{Universes} (* `{WithId} *) := {
  uniId : forall {_ : universesFlag}, (* forall {_ : withidFlag}, *)
          level -> term -> term -> term -> term
}.

Class UniEmpty `{Universes} `{WithEmpty} := {
  uniEmpty : forall {_ : universesFlag}, forall {_ : withemptyFlag},
             level -> term
}.

Class UniUnit `{Universes} `{WithUnit} := {
  uniUnit : forall {_ : universesFlag}, forall {_ : withunitFlag},
             level -> term
}.

Class UniBool `{Universes} `{WithBool} := {
  uniBool : forall {_ : universesFlag}, forall {_ : withboolFlag},
             nat -> term
}.

Class UniSimProd `{Universes} `{SimpleProducts} := {
  uniSimProd : forall {_ : universesFlag}, forall {_ : simpleproductsFlag},
               level -> level -> term -> term -> term
}.

Inductive Yes : Type := yes.
Inductive No : Type := .
